import Std.Data.HashMap
import Kenosis

namespace Soma.Syntax

open Kenosis

/-- Interned file identifier for efficient comparison -/
structure FileId where
  id : Nat
  deriving BEq, Hashable, Repr, Inhabited, Serialize, Deserialize

instance : ToString FileId where
  toString fid := s!"FileId({fid.id})"

/-- A source file with precomputed line information -/
structure SourceFile where
  id : FileId
  path : String
  content : String
  /-- Byte offsets where each line starts. lineStarts[0] = 0 always. -/
  lineStarts : Array Nat
  deriving Repr, Inhabited

/-- Create a SourceFile from path and content, precomputing line starts -/
def SourceFile.create (id : FileId) (path : String) (content : String) : SourceFile :=
  let lineStarts := computeLineStarts content
  { id, path, content, lineStarts }
where
  computeLineStarts (s : String) : Array Nat :=
    let size := s.utf8ByteSize
    let rec go (pos : Nat) (acc : Array Nat) : Array Nat :=
      if h : pos < size then
        let c := String.Pos.Raw.get s ⟨pos⟩
        let nextPos := (String.Pos.Raw.next s ⟨pos⟩).byteIdx
        have hNext : nextPos > pos := String.Pos.Raw.byteIdx_lt_byteIdx_next s ⟨pos⟩
        have _ : size - nextPos < size - pos := Nat.sub_lt_sub_left h hNext
        if c == '\n' then
          go nextPos (acc.push nextPos)
        else
          go nextPos acc
      else
        acc
    termination_by size - pos
    go 0 #[0]

/-- Get the line number (1-indexed) for a byte offset using binary search -/
def SourceFile.lineAt (sf : SourceFile) (byteOffset : Nat) : Nat :=
  -- Binary search to find the largest line start <= byteOffset
  let rec binarySearch (lo hi : Nat) : Nat :=
    if lo >= hi then lo
    else
      let mid := (lo + hi + 1) / 2
      if h : mid < sf.lineStarts.size then
        if sf.lineStarts[mid] <= byteOffset then
          binarySearch mid hi
        else
          binarySearch lo (mid - 1)
      else
        lo
  termination_by hi - lo
  -- Line numbers are 1-indexed
  binarySearch 0 (sf.lineStarts.size - 1) + 1

/-- Get the column number (1-indexed) for a byte offset -/
def SourceFile.columnAt (sf : SourceFile) (byteOffset : Nat) : Nat :=
  let line := sf.lineAt byteOffset
  let lineStart := if h : line - 1 < sf.lineStarts.size then sf.lineStarts[line - 1] else 0
  byteOffset - lineStart + 1

/-- Get a substring of the source content -/
def SourceFile.slice (sf : SourceFile) (start stop : Nat) : String :=
  String.Pos.Raw.extract sf.content ⟨start⟩ ⟨stop⟩

/-- Get the line content at a given line number (1-indexed) -/
def SourceFile.getLine (sf : SourceFile) (line : Nat) : String :=
  if line == 0 || line > sf.lineStarts.size then ""
  else
    let startIdx := line - 1
    let start := if h : startIdx < sf.lineStarts.size then sf.lineStarts[startIdx] else 0
    let stop :=
      if h : line < sf.lineStarts.size then sf.lineStarts[line]
      else sf.content.utf8ByteSize
    -- Remove trailing newline if present
    let str := String.Pos.Raw.extract sf.content ⟨start⟩ ⟨stop⟩
    if str.endsWith "\n" then str.dropRight 1 else str

/-- Rich source location with all information needed for diagnostics -/
structure SourceLoc where
  file : FileId
  byteOffset : Nat
  line : Nat      -- 1-indexed
  column : Nat    -- 1-indexed
  deriving Repr, BEq, Inhabited, Hashable, Serialize, Deserialize

instance : ToString SourceLoc where
  toString loc := s!"{loc.line}:{loc.column}"

/-- Create a SourceLoc from a byte offset -/
def SourceLoc.fromOffset (sf : SourceFile) (byteOffset : Nat) : SourceLoc :=
  { file := sf.id
  , byteOffset
  , line := sf.lineAt byteOffset
  , column := sf.columnAt byteOffset
  }

/-- Ordering on SourceLoc based on byte offset -/
instance : Ord SourceLoc where
  compare a b := compare a.byteOffset b.byteOffset

instance : LT SourceLoc where
  lt a b := a.byteOffset < b.byteOffset

instance : LE SourceLoc where
  le a b := a.byteOffset <= b.byteOffset

/-- A span of source code -/
structure Span where
  start : SourceLoc
  stop : SourceLoc
  deriving Repr, BEq, Inhabited, Hashable, Serialize, Deserialize

instance : ToString Span where
  toString span :=
    if span.start.line == span.stop.line then
      s!"{span.start.line}:{span.start.column}-{span.stop.column}"
    else
      s!"{span.start.line}:{span.start.column}-{span.stop.line}:{span.stop.column}"

/-- Merge two spans to get the smallest span containing both -/
def Span.merge (a b : Span) : Span :=
  { start := if a.start.byteOffset <= b.start.byteOffset then a.start else b.start
  , stop := if a.stop.byteOffset >= b.stop.byteOffset then a.stop else b.stop
  }

/-- Create a span from two byte offsets -/
def Span.fromOffsets (sf : SourceFile) (start stop : Nat) : Span :=
  { start := SourceLoc.fromOffset sf start
  , stop := SourceLoc.fromOffset sf stop
  }

/-- Get the length of a span in bytes -/
def Span.length (span : Span) : Nat :=
  span.stop.byteOffset - span.start.byteOffset

/-- Check if a span is empty (zero-width) -/
def Span.isEmpty (span : Span) : Bool :=
  span.start.byteOffset >= span.stop.byteOffset

/-- Create a zero-width span at a location -/
def Span.point (loc : SourceLoc) : Span :=
  { start := loc, stop := loc }

/-- Get the text content of a span from a source file -/
def Span.getText (span : Span) (sf : SourceFile) : String :=
  sf.slice span.start.byteOffset span.stop.byteOffset

/-- Uninhabited span, never use in real code -/
def Span.uninhabited : Span :=
  { start := { file := ⟨0⟩, byteOffset := 0, line := 0, column := 0 }
  , stop := { file := ⟨0⟩, byteOffset := 0, line := 0, column := 0 }
  }

/-- Well-known FileId for built-in compiler constructs -/
def FileId.builtin : FileId := ⟨1⟩

/-- Create a synthetic source file for built-in compiler constructs -/
def SourceFile.builtin : SourceFile :=
  SourceFile.create FileId.builtin "<built-in>" ""

/-- Create a span for built-in compiler constructs (type classes, instances, etc.) -/
def Span.builtin : Span :=
  { start := { file := FileId.builtin, byteOffset := 0, line := 1, column := 1 }
  , stop := { file := FileId.builtin, byteOffset := 0, line := 1, column := 1 }
  }

/-- A mapping from FileId to SourceFile for multi-file compilation -/
structure SourceFileMap where
  files : Std.HashMap FileId SourceFile
  deriving Inhabited

namespace SourceFileMap

/-- Create an empty source file map -/
def empty : SourceFileMap := { files := {} }

/-- Create a source file map from a single source file -/
def fromSingle (sf : SourceFile) : SourceFileMap :=
  { files := ({} : Std.HashMap FileId SourceFile).insert sf.id sf }

/-- Add a source file to the map -/
def insert (map : SourceFileMap) (sf : SourceFile) : SourceFileMap :=
  { files := map.files.insert sf.id sf }

/-- Look up a source file by FileId -/
def get? (map : SourceFileMap) (id : FileId) : Option SourceFile :=
  map.files.get? id

/-- Get the source file for a span -/
def getForSpan? (map : SourceFileMap) (span : Span) : Option SourceFile :=
  map.get? span.start.file

/-- Check if the map is empty -/
def isEmpty (map : SourceFileMap) : Bool :=
  map.files.isEmpty

/-- Get the number of files in the map -/
def size (map : SourceFileMap) : Nat :=
  map.files.size

end SourceFileMap

end Soma.Syntax
