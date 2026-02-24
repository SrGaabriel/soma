import Soma.Syntax
import Lapis

namespace Lsp

open Soma.Syntax
open Lapis.Protocol.Types

/-- Convert a UTF-16 code unit offset within a line to a UTF-8 byte offset -/
partial def utf16OffsetToUtf8 (line : String) (utf16Offset : Nat) : Nat :=
  go 0 0
where
  go (bytePos utf16Pos : Nat) : Nat :=
    if utf16Pos >= utf16Offset then bytePos
    else if bytePos >= line.utf8ByteSize then bytePos
    else
      let c := String.Pos.Raw.get line ⟨bytePos⟩
      let nextByte := (String.Pos.Raw.next line ⟨bytePos⟩).byteIdx
      let utf16Width := if c.toNat >= 0x10000 then 2 else 1
      go nextByte (utf16Pos + utf16Width)

/-- Convert a UTF-8 byte offset within a line to a UTF-16 code unit offset -/
partial def utf8OffsetToUtf16 (line : String) (utf8Offset : Nat) : Nat :=
  go 0 0
where
  go (bytePos utf16Pos : Nat) : Nat :=
    if bytePos >= utf8Offset then utf16Pos
    else if bytePos >= line.utf8ByteSize then utf16Pos
    else
      let c := String.Pos.Raw.get line ⟨bytePos⟩
      let nextByte := (String.Pos.Raw.next line ⟨bytePos⟩).byteIdx
      let utf16Width := if c.toNat >= 0x10000 then 2 else 1
      go nextByte (utf16Pos + utf16Width)

/-- Convert a byte-length span to UTF-16 code unit length -/
partial def utf8LengthToUtf16 (text : String) : Nat :=
  go 0 0
where
  go (bytePos utf16Len : Nat) : Nat :=
    if bytePos >= text.utf8ByteSize then utf16Len
    else
      let c := String.Pos.Raw.get text ⟨bytePos⟩
      let nextByte := (String.Pos.Raw.next text ⟨bytePos⟩).byteIdx
      let utf16Width := if c.toNat >= 0x10000 then 2 else 1
      go nextByte (utf16Len + utf16Width)

/-- Get the content of a line (0-indexed) from a SourceFile, without trailing newline -/
def getLineContent (sf : SourceFile) (lineIdx : Nat) : String :=
  let line1 := lineIdx + 1
  sf.getLine line1

/-- Convert a Soma SourceLoc to an LSP Position (0-indexed, UTF-16 character offset) -/
def sourceLocToPosition (sf : SourceFile) (loc : SourceLoc) : Position :=
  let lineIdx := loc.line - 1
  let lineContent := getLineContent sf lineIdx
  let byteCol := loc.column - 1
  let utf16Col := utf8OffsetToUtf16 lineContent byteCol
  { line := lineIdx, character := utf16Col }

/-- Convert a Soma Span to an LSP Range -/
def spanToRange (sf : SourceFile) (span : Span) : Range :=
  { start := sourceLocToPosition sf span.start
  , «end» := sourceLocToPosition sf span.stop }

/-- Convert an LSP Position (UTF-16 character) to a byte offset -/
def positionToOffset (sf : SourceFile) (pos : Position) : Nat :=
  let lineIdx := pos.line
  if h : lineIdx < sf.lineStarts.size then
    let lineStart := sf.lineStarts[lineIdx]
    let lineContent := getLineContent sf lineIdx
    let byteCol := utf16OffsetToUtf8 lineContent pos.character
    lineStart + byteCol
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
  let lineContent := getLineContent sf pos.line
  let byteCol := utf16OffsetToUtf8 lineContent pos.character
  if byteCol >= lineContent.utf8ByteSize then none
  else
    let start := findWordStart lineContent byteCol
    let stop := findWordEnd lineContent byteCol
    if start == stop then none
    else some (String.Pos.Raw.extract lineContent ⟨start⟩ ⟨stop⟩)

/-- Convert a file path to a file URI -/
def pathToUri (path : String) : String :=
  if path.startsWith "file://" then path
  else "file://" ++ path

/-- Convert a file URI to a path -/
def uriToPath (uri : String) : String :=
  if uri.startsWith "file://" then uri.drop 7 |>.copy
  else uri

end Lsp
