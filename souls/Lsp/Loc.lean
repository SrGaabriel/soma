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

/-- Convert a byte offset to an LSP Position -/
def offsetToPosition (sf : SourceFile) (offset : Nat) : Position := Id.run do
  let mut lineIdx := 0
  for h : i in [1:sf.lineStarts.size] do
    if sf.lineStarts[i] > offset then
      break
    lineIdx := i
  let lineStart := if lineIdx < sf.lineStarts.size then sf.lineStarts[lineIdx]! else 0
  let byteCol := offset - lineStart
  let lineContent := getLineContent sf lineIdx
  let utf16Col := utf8OffsetToUtf16 lineContent byteCol
  { line := lineIdx, character := utf16Col }

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
  else
    let pfx := if path.length > 1 && path.get? ⟨1⟩ == some ':' then "/" else ""
    "file://" ++ pfx ++ path

/-- Decode percent-encoded characters in a URI path -/
private partial def decodePercent (s : String) : String :=
  go s 0 ""
where
  hexVal (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  go (s : String) (i : Nat) (acc : String) : String :=
    if i >= s.length then acc
    else
      let c := s.get ⟨i⟩
      if c == '%' && i + 2 < s.length then
        let h := s.get ⟨i + 1⟩
        let l := s.get ⟨i + 2⟩
        match hexVal h, hexVal l with
        | some hv, some lv => go s (i + 3) (acc.push (Char.ofNat (hv * 16 + lv)))
        | _, _ => go s (i + 1) (acc.push c)
      else go s (i + 1) (acc.push c)

/-- Convert a file URI to a path -/
def uriToPath (uri : String) : String :=
  let raw := if uri.startsWith "file://" then uri.drop 7 |>.copy else uri
  let decoded := decodePercent raw
  if decoded.length > 2 then
    match decoded.get? ⟨0⟩, decoded.get? ⟨2⟩ with
    | some '/', some ':' => decoded.drop 1 |>.copy
    | _, _ => decoded
  else decoded

/-- Normalize a file path for cross-platform comparison -/
def normalizePath (path : String) : String :=
  let p := if path.startsWith "\\\\?\\" then path.drop 4 |>.copy
    else if path.startsWith "//?/" then path.drop 4 |>.copy
    else path
  let p := p.map fun c => if c == '\\' then '/' else c
  let p := if p.length > 2 then
    match p.get? ⟨0⟩, p.get? ⟨2⟩ with
    | some '/', some ':' => p.drop 1 |>.copy
    | _, _ => p
  else p
  -- Lowercase drive letter (C:/ → c:/)
  if p.length > 1 && p.get? ⟨1⟩ == some ':' then
    let drive := (p.get ⟨0⟩).toLower
    s!"{drive}{p.drop 1 |>.copy}"
  else p

end Lsp
