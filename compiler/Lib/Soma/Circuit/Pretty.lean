import Soma.Circuit.Graph
import Soma.Circuit.Node
import Soma.Circuit.Term
import Soma.Core.Quote

namespace Soma.Circuit.Pretty

open Soma.Circuit.Graph (Graph GraphM NodeEntry Definition enumList)
open Soma.Circuit.Node (Node NodeId PortId PortIdx Wire ActivePair Label PortRole)
open Soma.Circuit.Term (Term Tag Loc Op2Code PrimType)

/-! ## Configuration -/

/-- Pretty printing configuration -/
structure Config where
  /-- Indentation size -/
  indent : Nat := 2
  /-- Show node IDs -/
  showIds : Bool := true
  /-- Show port connections -/
  showConnections : Bool := true
  /-- Show labels on DUP/SUP -/
  showLabels : Bool := true
  /-- Show type annotations on nodes -/
  showTypes : Bool := false
  /-- Maximum line width before wrapping -/
  maxWidth : Nat := 80
  deriving Repr, Inhabited

/-- Default configuration -/
def Config.default : Config := {}

/-! ## Pretty Printing -/

/-- Pretty print a label -/
def ppLabel (l : Label) : String := s!"&{l.id}"

/-- Pretty print a node -/
def ppNode (cfg : Config) (n : Node) : String :=
  match n with
  | .lam true    => "λ_"
  | .lam false   => "λ"
  | .app         => "@"
  | .dup label   => if cfg.showLabels then s!"dup{ppLabel label}" else "dup"
  | .sup label   => if cfg.showLabels then s!"sup{ppLabel label}" else "sup"
  | .era         => "era"
  | .ctor tag ar => s!"C{tag}[{ar}]"
  | .mat exp     => s!"mat({exp})"
  | .record numFields => s!"rec[{numFields}]"
  | .proj idx    => s!".{idx}"
  | .num pt val  => s!"{ToString.toString pt |>.toLower}({val})"
  | .op1 op      => s!"({op})"
  | .op2 op      => s!"({op})"
  | .ref rid     => s!"@{rid}"
  | .use         => "use"
  | .alo rid     => s!"alo@{rid}"
  | .array et    => s!"array[{ToString.toString et |>.toLower}]"
  | .index       => "index"
  | .string      => "string"
  | .slice       => "slice"

/-- Pretty print a port ID -/
def ppPortId (p : PortId) : String :=
  if p.port.isPrincipal then s!"n{p.node.id}●"
  else s!"n{p.node.id}.{p.port.idx}"

/-- Pretty print a wire -/
def ppWire (w : Wire) : String :=
  s!"{ppPortId w.src} ~ {ppPortId w.dst}"

/-- Pretty print an active pair -/
def ppActivePair (ap : ActivePair) : String :=
  s!"(n{ap.node1.id} ●─● n{ap.node2.id})"

/-- Pretty print a node entry with connections -/
def ppNodeEntry (cfg : Config) (nid : NodeId) (entry : NodeEntry) : String :=
  let nodeStr := ppNode cfg entry.node
  let idStr := if cfg.showIds then s!"n{nid.id}: " else ""
  let typeStr := if cfg.showTypes then s!" : {entry.ty}" else ""
  let connStr := if cfg.showConnections then
    let conns := entry.connections.map fun (pIdx, target) =>
      let pName := match entry.node.portRole pIdx with
        | some role => ToString.toString role
        | none => s!"p{pIdx.idx}"
      s!"{pName}→{ppPortId target}"
    if conns.isEmpty then "" else s!" [{String.intercalate ", " conns}]"
  else ""
  s!"{idStr}{nodeStr}{typeStr}{connStr}"

/-- Pretty print an entire graph -/
def ppGraph (cfg : Config := .default) (g : Graph) : String :=
  let header := s!"Circuit Graph ({g.nodeCount} nodes)"
  let rootStr := s!"Root: {ppPortId g.root}"

  let nodesList := g.nodes.toList
    |>.toArray
    |>.qsort (fun a b => a.1 < b.1)
    |>.toList
    |>.map fun (id, entry) => ppNodeEntry cfg ⟨id⟩ entry
  let nodesStr := String.intercalate "\n" nodesList

  let activePairs := g.activePairs
  let activeStr := if activePairs.isEmpty then "Normal form (no active pairs)"
    else
      let pairStrs := activePairs.map ppActivePair
      s!"Active pairs: {String.intercalate ", " pairStrs}"

  s!"{header}\n{rootStr}\n\n{nodesStr}\n\n{activeStr}"

/-- Pretty print book definitions -/
def ppBook (cfg : Config := .default) (g : Graph) : String :=
  if g.book.isEmpty then "Book: (empty)"
  else
    let defs := (enumList g.book.toList).map fun (idx, def_) =>
      let typeStr := if cfg.showTypes then s!" : {def_.ty}" else ""
      s!"  [{idx}] {def_.name} (arity {def_.arity}, root n{def_.root.id}){typeStr}"
    s!"Book:\n{String.intercalate "\n" defs}"

/-- Full graph dump including book -/
def ppFull (cfg : Config := .default) (g : Graph) : String :=
  s!"{ppGraph cfg g}\n\n{ppBook cfg g}"

/-! ## Term-level Pretty Printing -/

/-- Pretty print a term (packed representation) -/
def ppTerm (t : Term) : String :=
  let tagStr := ToString.toString t.tag
  let extStr := if t.ext.val == 0 then "" else s!"#{t.ext.val}"
  let valStr := s!"@{t.val}"
  let subStr := if t.isSubstituted then "!" else ""
  s!"{subStr}{tagStr}{extStr}{valStr}"

end Soma.Circuit.Pretty
