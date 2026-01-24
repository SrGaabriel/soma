import Soma.Syntax
import Lapis

namespace Lsp

open Soma.Syntax
open Lapis.Protocol.Types

/-- Convert a Soma SourceLoc to an LSP Position (0-indexed) -/
def sourceLocToPosition (loc : SourceLoc) : Position :=
  { line := loc.line - 1
  , character := loc.column - 1 }

/-- Convert a Soma Span to an LSP Range -/
def spanToRange (span : Span) : Range :=
  { start := sourceLocToPosition span.start
  , «end» := sourceLocToPosition span.stop }

/-- Convert an LSP Position to a byte offset -/
def positionToOffset (sf : SourceFile) (pos : Position) : Nat :=
  let lineIdx := pos.line
  if h : lineIdx < sf.lineStarts.size then
    let lineStart := sf.lineStarts[lineIdx]
    lineStart + pos.character
  else
    -- Past end of file
    sf.content.utf8ByteSize

/-- Get line content at a 0-indexed line number -/
def getLineAt (sf : SourceFile) (line : Nat) : String :=
  sf.getLine (line + 1)

/-- Check if character is a word character -/
def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_'

/-- Find word start going backwards from position -/
partial def findWordStart (line : String) (pos : Nat) : Nat :=
  if pos == 0 then 0
  else if isWordChar (String.Pos.Raw.get line ⟨pos - 1⟩) then
    findWordStart line (pos - 1)
  else pos

/-- Find word end going forwards from position -/
partial def findWordEnd (line : String) (pos : Nat) : Nat :=
  if pos >= line.length then pos
  else if isWordChar (String.Pos.Raw.get line ⟨pos⟩) then
    findWordEnd line (pos + 1)
  else pos

/-- Get word at position -/
def wordAtPosition (sf : SourceFile) (pos : Position) : Option String :=
  let line := getLineAt sf pos.line
  let char := pos.character
  if char >= line.length then none
  else
    let start := findWordStart line char
    let stop := findWordEnd line char
    if start == stop then none
    else some (String.Pos.Raw.extract line ⟨start⟩ ⟨stop⟩)

/-- Convert a file path to a file URI -/
def pathToUri (path : String) : String :=
  if path.startsWith "file://" then path
  else "file://" ++ path

/-- Convert a file URI to a path -/
def uriToPath (uri : String) : String :=
  if uri.startsWith "file://" then uri.drop 7 |>.copy
  else uri

end Lsp
