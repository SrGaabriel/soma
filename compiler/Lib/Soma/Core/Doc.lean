import Soma.Core.Path
import Std.Data.HashMap

namespace Soma.Core

/-- A pretty-printing document -/
inductive Doc where
  /-- The empty document -/
  | empty
  /-- A literal piece of text -/
  | text (s : String)
  /-- A forced newline -/
  | line
  /-- A soft line break -/
  | softline
  /-- Concatenation -/
  | concat (a b : Doc)
  /-- Increase the indent of every newline -/
  | nest (n : Nat) (d : Doc)
  /-- A group -/
  | group (d : Doc)
  /-- Record the rendered span of `d` against `path` -/
  | tagPath (path : Path) (d : Doc)
  deriving Inhabited

namespace Doc

def append (a b : Doc) : Doc := .concat a b

instance : Append Doc := ⟨append⟩

partial def flatten : Doc → Doc
  | .empty => .empty
  | .text s => .text s
  | .line => .line
  | .softline => .text " "
  | .concat a b => .concat (flatten a) (flatten b)
  | .nest _ d => flatten d
  | .group d => flatten d
  | .tagPath p d => .tagPath p (flatten d)

partial def flatWidth : Doc → Option Nat
  | .empty => some 0
  | .text s => some s.length
  | .line => none
  | .softline => some 1
  | .concat a b => do
    let wa ← flatWidth a
    let wb ← flatWidth b
    return wa + wb
  | .nest _ d => flatWidth d
  | .group d => flatWidth d
  | .tagPath _ d => flatWidth d

end Doc

structure PpSubSpan where
  startLine : Nat
  startCol : Nat
  endLine : Nat
  endCol : Nat
  deriving Repr, BEq, Hashable, Inhabited

abbrev PpSubSpanMap := Std.HashMap Path PpSubSpan

structure Rendered where
  text : String
  spans : PpSubSpanMap := {}
  deriving Inhabited

private structure LayoutState where
  buf : String := ""
  line : Nat := 1
  col : Nat := 0
  pending : List (Path × Nat × Nat) := []
  spans : PpSubSpanMap := {}
  deriving Inhabited

private abbrev LayoutM := StateM LayoutState

namespace LayoutM

private def emit (s : String) : LayoutM Unit :=
  modify fun st => { st with buf := st.buf ++ s, col := st.col + s.length }

private def newline (indent : Nat) : LayoutM Unit :=
  modify fun st =>
    { st with
        buf := st.buf ++ "\n" ++ String.ofList (List.replicate indent ' ')
        line := st.line + 1
        col := indent }

private def pushTag (path : Path) : LayoutM Unit := do
  let st ← get
  set { st with pending := (path, st.line, st.col) :: st.pending }

private def popTag : LayoutM Unit := do
  let st ← get
  match st.pending with
  | [] => pure ()
  | (path, startLine, startCol) :: rest =>
    set { st with
            pending := rest
            spans := st.spans.insert path
              { startLine, startCol, endLine := st.line, endCol := st.col } }

end LayoutM

open LayoutM

private partial def render (maxWidth : Nat) (indent : Nat) (flat : Bool)
    : Doc → LayoutM Unit
  | .empty => pure ()
  | .text s => emit s
  | .line => newline indent
  | .softline =>
    if flat then emit " "
    else newline indent
  | .concat a b => do
    render maxWidth indent flat a
    render maxWidth indent flat b
  | .nest n d => render maxWidth (indent + n) flat d
  | .group d => do
    let st ← get
    let remaining := if st.col ≥ maxWidth then 0 else maxWidth - st.col
    match Doc.flatWidth d with
    | some w =>
      if w ≤ remaining then
        render maxWidth indent true d
      else
        render maxWidth indent false d
    | none =>
      render maxWidth indent false d
  | .tagPath path d => do
    pushTag path
    render maxWidth indent flat d
    popTag

def Doc.render (d : Doc) (maxWidth : Nat := 80) (startCol : Nat := 0)
    : Rendered :=
  let initial : LayoutState :=
    { buf := "", line := 1, col := startCol, pending := [], spans := {} }
  let (_, final) := (Soma.Core.render maxWidth 0 false d) |>.run initial
  { text := final.buf, spans := final.spans }

end Soma.Core
