/-
  Features:

  - Colored output with Unicode box-drawing characters
  - Source code snippets with line numbers
  - Multiple labeled spans (primary and secondary)
  - Multi-line span support with vertical connectors
  - Line break indicators with connected pipes
  - Notes and help suggestions
-/

import Kenosis
import Soma.Syntax.Source
import Soma.Syntax.Diagnostic

namespace Soma.Logging.Error

open Soma.Syntax

/-! ## ANSI Color Codes -/

namespace Color

def reset : String := "\x1b[0m"
def bold : String := "\x1b[1m"
def dim : String := "\x1b[2m"

def red : String := "\x1b[31m"
def green : String := "\x1b[32m"
def yellow : String := "\x1b[33m"
def blue : String := "\x1b[34m"
def magenta : String := "\x1b[35m"
def cyan : String := "\x1b[36m"
def white : String := "\x1b[37m"

def brightRed : String := "\x1b[91m"
def brightBlue : String := "\x1b[94m"
def brightCyan : String := "\x1b[96m"

def severityColor : Severity → String
  | .error => bold ++ red
  | .warning => bold ++ yellow
  | .info => bold ++ blue
  | .hint => bold ++ green

def labelColor : LabelStyle → String
  | .primary => bold ++ red
  | .secondary => bold ++ blue

end Color

/-! ## Unicode Characters -/

namespace Chars

def pipe : String := "│"
def pipeDotted : String := "┆"
def horizontal : String := "─"
def horizontalChar : Char := '─'
def cornerTopLeft : String := "╭"
def cornerBottomLeft : String := "╰"
def cornerTopRight : String := "╮"
def cornerBottomRight : String := "╯"
def teeLeft : String := "┤"
def teeRight : String := "├"
def teeUp : String := "┴"
def teeDown : String := "┬"
def cross : String := "┼"
def underlineCaret : Char := '^'
def underlineTilde : Char := '~'
def arrowRight : String := "→"
def notePrefix : String := "="
def helpPrefix : String := "="

end Chars

/-! ## Rendering Helpers -/

/-- Convert a byte-based column (1-indexed) to a visual column (1-indexed) -/
def byteColToVisualCol (lineContent : String) (byteCol : Nat) : Nat :=
  if byteCol == 0 then 0
  else
    let pfx := String.Pos.Raw.extract lineContent ⟨0⟩ ⟨byteCol - 1⟩
    pfx.length + 1

/-- Expand tabs to spaces for consistent rendering -/
def expandTabs (s : String) (tabWidth : Nat := 4) : String := Id.run do
  let mut result : Array Char := #[]
  let mut col : Nat := 0
  for c in s.toList do
    if c == '\t' then
      let spaces := tabWidth - (col % tabWidth)
      for _ in List.range spaces do
        result := result.push ' '
      col := col + spaces
    else
      result := result.push c
      col := col + 1
  return String.ofList result.toList

/-- Convert byte column to visual column accounting for tabs -/
def byteColToVisualColWithTabs (lineContent : String) (byteCol : Nat) (tabWidth : Nat := 4) : Nat :=
  if byteCol == 0 then 0
  else
    let pfx := String.Pos.Raw.extract lineContent ⟨0⟩ ⟨byteCol - 1⟩
    let expanded := expandTabs pfx tabWidth
    expanded.length + 1

def padNum (n : Nat) (width : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (width - s.length) ' ') ++ s

def lineNumWidth (maxLine : Nat) : Nat :=
  (toString maxLine).length

def gutter (lineNum : Option Nat) (width : Nat) : String :=
  match lineNum with
  | some n => Color.brightBlue ++ padNum n width ++ " " ++ Chars.pipe ++ Color.reset
  | none => String.ofList (List.replicate width ' ') ++ " " ++ Color.brightBlue ++ Chars.pipe ++ Color.reset

def emptyGutter (width : Nat) : String :=
  String.ofList (List.replicate width ' ') ++ " " ++ Color.brightBlue ++ Chars.pipe ++ Color.reset

def skipGutter (width : Nat) : String :=
  String.ofList (List.replicate width ' ') ++ " " ++ Color.brightBlue ++ Chars.pipeDotted ++ Color.reset

/-! ## Multi-line Span Tracking -/

structure MultiSpan where
  style : LabelStyle
  startLine : Nat
  endLine : Nat
  startCol : Nat
  endCol : Nat
  message : String
  isVirtual : Bool := false
  visualCol : Nat := 0  -- Assigned to handle overlapping spans at same connectorCol
  deriving Repr, Inhabited, BEq

def MultiSpan.connectorCol (ms : MultiSpan) : Nat :=
  min ms.startCol ms.endCol

/-- Assign unique visual columns to overlapping multi-line spans -/
def assignVisualColumns (spans : Array MultiSpan) : Array MultiSpan := Id.run do
  let sorted := spans.toList.mergeSort (fun a b =>
    if a.startLine != b.startLine then a.startLine < b.startLine
    else a.connectorCol < b.connectorCol) |>.toArray

  let mut result : Array MultiSpan := #[]
  let mut usedCols : Array (Nat × Nat × Nat) := #[]

  for ms in sorted do
    let baseCol := ms.connectorCol
    let mut visualCol := baseCol
    let mut found := false
    while !found do
      let conflict := usedCols.any fun (col, sLine, eLine) =>
        col == visualCol && ms.startLine < eLine && sLine < ms.endLine
      if conflict then
        visualCol := visualCol + 1
      else
        found := true
    usedCols := usedCols.push (visualCol, ms.startLine, ms.endLine)
    result := result.push { ms with visualCol := visualCol }

  result

structure SingleLabel where
  line : Nat
  startCol : Nat
  endCol : Nat
  style : LabelStyle
  message : String
  deriving Repr, Inhabited, BEq

def mostSevereStyle (a b : LabelStyle) : LabelStyle :=
  match a, b with
  | .primary, _ => .primary
  | _, .primary => .primary
  | _, _ => .secondary

def getMostSevereColorAtCol (spans : Array MultiSpan) (visualCol : Nat) : String :=
  let matching := spans.filter (·.visualCol == visualCol)
  let style := matching.foldl (fun acc ms => mostSevereStyle acc ms.style) LabelStyle.secondary
  Color.labelColor style

def getMostSevereColorAtColVirtual (spans : Array MultiSpan) (col : Nat) : String :=
  let matching := spans.filter (·.startCol == col)
  let style := matching.foldl (fun acc ms => mostSevereStyle acc ms.style) LabelStyle.secondary
  Color.labelColor style

/-! ## Main Rendering -/

/-- Helper to build a string from an array of parts efficiently -/
private def buildString (parts : Array String) : String :=
  String.intercalate "" parts.toList

/-- Create a position ruler showing column numbers -/
private def makeRuler (len : Nat) : String :=
  let digits := List.range len |>.map fun i =>
    let col := i + 1
    if col % 10 == 0 then toString (col / 10 % 10)
    else if col % 5 == 0 then "+"
    else "."
  String.intercalate "" digits

/-- Annotate a string showing the visual position of each character -/
private def annotatePositions (s : String) : String :=
  let chars := s.toList
  let indices := List.range chars.length
  let indexed := chars.zip indices |>.map fun (c, i) => s!"[{i+1}:{c}]"
  String.intercalate "" indexed

/-- Group single labels by column, returning (singleColLabels, multiColGroups) -/
private def groupLabelsByColumn (labels : Array SingleLabel) : Array SingleLabel × Array (Array SingleLabel) := Id.run do
  if labels.size <= 1 then
    return (labels, #[])

  let sortedLabels := labels.toList.mergeSort (fun a b => a.startCol < b.startCol) |>.toArray
  let mut singleColLabels : Array SingleLabel := #[]
  let mut multiColGroups : Array (Array SingleLabel) := #[]
  let mut currentGroup : Array SingleLabel := #[]
  let mut currentCol : Option Nat := none

  for sl in sortedLabels do
    match currentCol with
    | none =>
      currentGroup := #[sl]
      currentCol := some sl.startCol
    | some col =>
      if sl.startCol == col then
        currentGroup := currentGroup.push sl
      else
        -- Flush current group
        if currentGroup.size == 1 then
          if h : currentGroup.size > 0 then
            singleColLabels := singleColLabels.push currentGroup[0]
        else if currentGroup.size > 1 then
          multiColGroups := multiColGroups.push currentGroup
        currentGroup := #[sl]
        currentCol := some sl.startCol

  -- Flush final group
  if currentGroup.size == 1 then
    if h : currentGroup.size > 0 then
      singleColLabels := singleColLabels.push currentGroup[0]
  else if currentGroup.size > 1 then
    multiColGroups := multiColGroups.push currentGroup

  (singleColLabels, multiColGroups)

/-- Collect unique line numbers from all label sources -/
private def collectUniqueLines (singleLabels : Array SingleLabel) (multiSpans : Array MultiSpan) (virtualSpans : Array MultiSpan) : Array Nat :=
  let fromSingle := singleLabels.map (·.line)
  let fromMultiStart := multiSpans.map (·.startLine)
  let fromMultiEnd := multiSpans.map (·.endLine)
  let fromVirtual := virtualSpans.map (·.startLine)
  let all := fromSingle ++ fromMultiStart ++ fromMultiEnd ++ fromVirtual
  all.toList.eraseDups.toArray

def renderDiagnostic (d : Diagnostic) (sf : SourceFile) (debug : Bool := false) : String := Id.run do
  let mut output : Array String := #[]

  -- Header: severity and message
  let sevColor := Color.severityColor d.severity
  let sevText := toString d.severity
  let codeText := match d.code with
    | some c => s!"[{c}]"
    | none => ""
  output := output.push s!"{sevColor}{sevText}{codeText}{Color.reset}: {Color.bold}{d.message}{Color.reset}"

  -- Location arrow
  let labels := d.labels
  if h : labels.size > 0 then
    let primarySpan := labels[0]'h |>.span
    let arrow := s!"{Color.brightBlue}{Chars.cornerTopLeft}{Chars.horizontal}{Chars.arrowRight}{Color.reset}"
    output := output.push s!" {arrow} {sf.path}:{primarySpan.start.line}:{primarySpan.start.column}"

  -- Categorize labels into single-line and multi-line
  let mut singleLabels : Array SingleLabel := #[]
  let mut multiSpans : Array MultiSpan := #[]

  for label in d.labels do
    let startLine := label.span.start.line
    let endLine := label.span.stop.line
    if startLine == endLine then
      singleLabels := singleLabels.push {
        line := startLine
        startCol := label.span.start.column
        endCol := label.span.stop.column
        style := label.style
        message := label.message
      }
    else
      multiSpans := multiSpans.push {
        style := label.style
        startLine := startLine
        endLine := endLine
        startCol := label.span.start.column
        endCol := label.span.stop.column
        message := label.message
        isVirtual := false
      }

  -- Process single labels: separate those at unique columns from those sharing columns
  let mut virtualSpans : Array MultiSpan := #[]
  let mut finalSingleLabels : Array SingleLabel := #[]

  let singleLabelLines := singleLabels.map (·.line) |>.toList.eraseDups.toArray

  for lineNum in singleLabelLines do
    let lineLabels := singleLabels.filter (·.line == lineNum)
    let (uniqueLabels, groupedLabels) := groupLabelsByColumn lineLabels

    for sl in uniqueLabels do
      finalSingleLabels := finalSingleLabels.push sl

    for group in groupedLabels do
      for sl in group do
        virtualSpans := virtualSpans.push {
          style := sl.style
          startLine := sl.line
          endLine := sl.line
          startCol := sl.startCol
          endCol := sl.endCol
          message := sl.message
          isVirtual := true
        }

  let multiSpansWithCols := assignVisualColumns multiSpans

  -- Collect all lines we need to render (#5: O(n) instead of O(n²))
  let allLines := collectUniqueLines finalSingleLabels multiSpansWithCols virtualSpans

  if allLines.isEmpty then
    return String.intercalate "\n" output.toList

  let sortedLines := allLines.toList.mergeSort (· < ·) |>.toArray
  let maxLine := sortedLines.foldl max 0
  let gutterWidth := lineNumWidth maxLine

  output := output.push s!" {emptyGutter gutterWidth}"

  let mut prevLineNum : Option Nat := none

  for lineNum in sortedLines do
    let activeSpans := (multiSpansWithCols.filter fun ms =>
      ms.startLine < lineNum && lineNum <= ms.endLine).toList.mergeSort (fun a b => a.visualCol < b.visualCol) |>.toArray

    let rawContent := sf.getLine lineNum
    let content := expandTabs rawContent

    -- Skip indicator for non-consecutive lines
    match prevLineNum with
    | some prev =>
        if lineNum > prev + 1 then
          let mut skipParts : Array String := #[]
          let mut visualPos : Nat := 0
          for ms in activeSpans do
            let color := Color.labelColor ms.style
            -- Use START line content for consistent vertical alignment
            let startLineContent := sf.getLine ms.startLine
            -- +1 to account for space between margin and content
            let targetCol := byteColToVisualColWithTabs startLineContent ms.visualCol
            skipParts := skipParts.push (String.ofList (List.replicate (targetCol - visualPos) ' '))
            skipParts := skipParts.push color
            skipParts := skipParts.push Chars.pipeDotted
            skipParts := skipParts.push Color.reset
            visualPos := targetCol + 1
          output := output.push s!" {skipGutter gutterWidth}{buildString skipParts}"
    | none => pure ()

    prevLineNum := some lineNum

    let mut marginParts : Array String := #[]
    let mut visualPos : Nat := 0
    for ms in activeSpans do
      -- Use START line content for consistent vertical alignment
      let startLineContent := sf.getLine ms.startLine
      -- +1 to account for space between margin and content
      let targetCol := byteColToVisualColWithTabs startLineContent ms.visualCol
      if targetCol >= visualPos then
        let color := getMostSevereColorAtCol activeSpans ms.visualCol
        marginParts := marginParts.push (String.ofList (List.replicate (targetCol - visualPos) ' '))
        marginParts := marginParts.push color
        marginParts := marginParts.push Chars.pipe
        marginParts := marginParts.push Color.reset
        visualPos := targetCol + 1
    let margin := buildString marginParts

    -- Render line content with tab expansion
    let displayContent := if content.trimAscii.isEmpty then
      s!"{Color.dim}<empty line>{Color.reset}"
    else
      content
    output := output.push s!" {gutter (some lineNum) gutterWidth}{margin} {displayContent}"

    if debug then
      output := output.push s!"  DEBUG L{lineNum}: rawContent=\"{rawContent}\" (len={rawContent.length})"
      output := output.push s!"  DEBUG L{lineNum}: ruler:  {makeRuler (content.length + 1)}"

    -- Render multi-line span start underlines
    for ms in multiSpansWithCols do
      if ms.startLine == lineNum then
        let color := Color.labelColor ms.style
        -- For the span's own connector, use current line (rawContent) since this IS the start line
        let connVisualCol := byteColToVisualColWithTabs rawContent ms.visualCol
        let startVisualCol := byteColToVisualColWithTabs rawContent ms.startCol

        let mut underlineParts : Array String := #[]
        let mut underlineVisualPos : Nat := 0

        for other in activeSpans do
          -- Use START line content for other spans' consistent vertical alignment
          let otherStartLineContent := sf.getLine other.startLine
          -- +1 to account for space between margin and content
          let targetCol := byteColToVisualColWithTabs otherStartLineContent other.visualCol
          if targetCol >= underlineVisualPos then
            underlineParts := underlineParts.push (String.ofList (List.replicate (targetCol - underlineVisualPos) ' '))
            let c := getMostSevereColorAtCol activeSpans other.visualCol
            underlineParts := underlineParts.push c
            underlineParts := underlineParts.push Chars.pipe
            underlineParts := underlineParts.push Color.reset
            underlineVisualPos := targetCol + 1

        -- +1 to account for the space between margin and content
        let toCornerLen := connVisualCol - underlineVisualPos
        underlineParts := underlineParts.push (String.ofList (List.replicate (max toCornerLen 0) ' '))

        -- -1 because we shifted the corner right by 1
        let toStartLen := if startVisualCol > connVisualCol then startVisualCol - connVisualCol - 2 else 0
        underlineParts := underlineParts.push color
        underlineParts := underlineParts.push Chars.cornerTopLeft
        underlineParts := underlineParts.push (String.ofList (List.replicate toStartLen Chars.horizontalChar))

        -- #9: Use visual content length for underline
        let underlineLen := content.length - max startVisualCol connVisualCol
        underlineParts := underlineParts.push (String.ofList (List.replicate (max underlineLen 0) Chars.horizontalChar))
        underlineParts := underlineParts.push Color.reset

        output := output.push s!" {emptyGutter gutterWidth}{buildString underlineParts}"

        if debug then
          output := output.push s!"  DEBUG SPAN-START: visualCol(byte)={ms.visualCol} startCol(byte)={ms.startCol}"
          output := output.push s!"  DEBUG SPAN-START: connVisualCol={connVisualCol} startVisualCol={startVisualCol}"
          output := output.push s!"  DEBUG SPAN-START: corner at pos {connVisualCol}, horiz line from {startVisualCol} for {underlineLen} chars"

    -- Render multi-line span end lines
    for ms in multiSpansWithCols do
      if ms.endLine == lineNum then
        let color := Color.labelColor ms.style
        let continuingSpans := activeSpans.filter fun other => other.endLine > lineNum
        -- Use START line content for connector position to ensure vertical alignment
        let startLineContent := sf.getLine ms.startLine
        let endVisualCol := byteColToVisualColWithTabs rawContent ms.endCol
        let msVisualCol := byteColToVisualColWithTabs startLineContent ms.visualCol



        let mut rowParts : Array String := #[]
        let mut rowPos : Nat := 0

        -- Draw pipes for spans to the left
        for other in activeSpans do
          -- Use START line content for consistent vertical alignment
          let otherStartLineContent := sf.getLine other.startLine
          -- +1 to account for space between margin and content
          let otherVisualCol := byteColToVisualColWithTabs otherStartLineContent other.visualCol
          let targetCol := otherVisualCol
          if targetCol < msVisualCol && targetCol >= rowPos then
            rowParts := rowParts.push (String.ofList (List.replicate (targetCol - rowPos) ' '))
            let c := getMostSevereColorAtCol activeSpans other.visualCol
            rowParts := rowParts.push c
            rowParts := rowParts.push Chars.pipe
            rowParts := rowParts.push Color.reset
            rowPos := targetCol + 1

        -- +1 to account for space between margin and content
        let cornerCol := msVisualCol
        if cornerCol >= rowPos then
          rowParts := rowParts.push (String.ofList (List.replicate (cornerCol - rowPos) ' '))
          rowParts := rowParts.push color
          rowParts := rowParts.push Chars.cornerBottomLeft
          rowParts := rowParts.push Color.reset
          rowPos := cornerCol + 1

        -- The endVisualCol is a position in the content area, but we need to add the margin offset
        -- +1 because corner was shifted right by 1
        let actualEndPos := msVisualCol + endVisualCol + 1
        let horizLen := if actualEndPos > rowPos then actualEndPos - rowPos else 1
        for i in List.range horizLen do
          let currentCol := rowPos + i
          -- Use START line content for continuing spans check
          let hasContinuing := continuingSpans.any fun s =>
            let sStartContent := sf.getLine s.startLine
            byteColToVisualColWithTabs sStartContent s.visualCol == currentCol
          if hasContinuing then
            let continuingStyle := continuingSpans.foldl (fun acc s =>
              let sStartContent := sf.getLine s.startLine
              if byteColToVisualColWithTabs sStartContent s.visualCol == currentCol then mostSevereStyle acc s.style else acc) LabelStyle.secondary
            let combinedStyle := mostSevereStyle ms.style continuingStyle
            let c := Color.labelColor combinedStyle
            rowParts := rowParts.push c
            rowParts := rowParts.push Chars.cross
            rowParts := rowParts.push Color.reset
          else
            rowParts := rowParts.push color
            rowParts := rowParts.push Chars.horizontal
            rowParts := rowParts.push Color.reset

        if !ms.message.isEmpty then
          rowParts := rowParts.push color
          rowParts := rowParts.push " "
          rowParts := rowParts.push ms.message
          rowParts := rowParts.push Color.reset

        output := output.push s!" {emptyGutter gutterWidth}{buildString rowParts}"

        if debug then
          output := output.push s!"  DEBUG SPAN-END: visualCol(byte)={ms.visualCol} endCol(byte)={ms.endCol}"
          output := output.push s!"  DEBUG SPAN-END: msVisualCol={msVisualCol} endVisualCol={endVisualCol}"
          output := output.push s!"  DEBUG SPAN-END: corner at pos {msVisualCol}, horiz line for {horizLen} chars to pos {endVisualCol}"

    -- Render stacked labels (virtual spans)
    let lineVirtualSpans := virtualSpans.filter (·.startLine == lineNum)
    if !lineVirtualSpans.isEmpty then
      let sortedVirtual := lineVirtualSpans.toList.mergeSort (fun a b => a.startCol < b.startCol) |>.toArray
      let numSpans := sortedVirtual.size

      let mut firstRowParts : Array String := #[]
      let mut firstRowPos : Nat := 0

      for ms in activeSpans do
        -- +1 to account for space between margin and content
        let targetCol := ms.visualCol
        if targetCol >= firstRowPos then
          let color := getMostSevereColorAtCol activeSpans ms.visualCol
          firstRowParts := firstRowParts.push (String.ofList (List.replicate (targetCol - firstRowPos) ' '))
          firstRowParts := firstRowParts.push color
          firstRowParts := firstRowParts.push Chars.pipe
          firstRowParts := firstRowParts.push Color.reset
          firstRowPos := targetCol + 1

      for vs in sortedVirtual do
        let targetCol := byteColToVisualColWithTabs rawContent vs.startCol
        if targetCol >= firstRowPos then
          let color := getMostSevereColorAtColVirtual sortedVirtual vs.startCol
          firstRowParts := firstRowParts.push (String.ofList (List.replicate (targetCol - firstRowPos) ' '))
          firstRowParts := firstRowParts.push color
          firstRowParts := firstRowParts.push Chars.teeRight
          firstRowParts := firstRowParts.push Color.reset
          firstRowPos := targetCol + 1

      let lastSpan := sortedVirtual.getD (sortedVirtual.size - 1) default
      if !lastSpan.message.isEmpty then
        firstRowParts := firstRowParts.push (Color.labelColor lastSpan.style)
        firstRowParts := firstRowParts.push Chars.horizontal
        firstRowParts := firstRowParts.push " "
        firstRowParts := firstRowParts.push lastSpan.message
        firstRowParts := firstRowParts.push Color.reset

      output := output.push s!" {emptyGutter gutterWidth}{buildString firstRowParts}"

      -- Render remaining virtual span messages (bottom to top)
      for spanIdx in List.range (numSpans - 1) |>.reverse do
        let currentSpan := sortedVirtual.getD spanIdx default
        let color := Color.labelColor currentSpan.style

        let mut rowParts : Array String := #[]
        let mut rowPos : Nat := 0

        for ms in activeSpans do
          -- +1 to account for space between margin and content
          let targetCol := ms.visualCol
          if targetCol >= rowPos then
            let c := getMostSevereColorAtCol activeSpans ms.visualCol
            rowParts := rowParts.push (String.ofList (List.replicate (targetCol - rowPos) ' '))
            rowParts := rowParts.push c
            rowParts := rowParts.push Chars.pipe
            rowParts := rowParts.push Color.reset
            rowPos := targetCol + 1

        let cornerCol := byteColToVisualColWithTabs rawContent currentSpan.startCol
        let mut drewCorner := false

        for i in List.range spanIdx do
          let vs := sortedVirtual.getD i default
          let targetCol := byteColToVisualColWithTabs rawContent vs.startCol
          if targetCol >= rowPos then
            rowParts := rowParts.push (String.ofList (List.replicate (targetCol - rowPos) ' '))
            if targetCol == cornerCol then
              let c := getMostSevereColorAtColVirtual sortedVirtual vs.startCol
              rowParts := rowParts.push c
              rowParts := rowParts.push Chars.teeRight
              rowParts := rowParts.push Color.reset
              drewCorner := true
            else
              let c := getMostSevereColorAtColVirtual sortedVirtual vs.startCol
              rowParts := rowParts.push c
              rowParts := rowParts.push Chars.pipe
              rowParts := rowParts.push Color.reset
            rowPos := targetCol + 1

        let msgPart := if currentSpan.message.isEmpty then "" else " " ++ currentSpan.message
        if drewCorner then
          rowParts := rowParts.push color
          rowParts := rowParts.push Chars.horizontal
          rowParts := rowParts.push msgPart
          rowParts := rowParts.push Color.reset
        else if cornerCol >= rowPos then
          rowParts := rowParts.push (String.ofList (List.replicate (cornerCol - rowPos) ' '))
          rowParts := rowParts.push color
          rowParts := rowParts.push Chars.cornerBottomLeft
          rowParts := rowParts.push Chars.horizontal
          rowParts := rowParts.push msgPart
          rowParts := rowParts.push Color.reset
        else
          rowParts := rowParts.push color
          rowParts := rowParts.push Chars.horizontal
          rowParts := rowParts.push msgPart
          rowParts := rowParts.push Color.reset

        output := output.push s!" {emptyGutter gutterWidth}{buildString rowParts}"

    let lineLabels := (finalSingleLabels.filter (·.line == lineNum)).toList.mergeSort (fun a b => a.startCol < b.startCol) |>.toArray

    if lineLabels.size == 1 then
      -- Single label: render with message inline
      let sl := lineLabels[0]!
      let color := Color.labelColor sl.style
      let char := match sl.style with
        | .primary => Chars.underlineCaret
        | .secondary => Chars.underlineTilde

      let mut labelParts : Array String := #[]
      let mut labelVisualPos : Nat := 0

      for ms in activeSpans do
        -- +1 to account for space between margin and content
        let targetCol := ms.visualCol
        if targetCol >= labelVisualPos then
          let c := getMostSevereColorAtCol activeSpans ms.visualCol
          labelParts := labelParts.push (String.ofList (List.replicate (targetCol - labelVisualPos) ' '))
          labelParts := labelParts.push c
          labelParts := labelParts.push Chars.pipe
          labelParts := labelParts.push Color.reset
          labelVisualPos := targetCol + 1

      let startVisualCol := byteColToVisualColWithTabs rawContent sl.startCol
      let endVisualCol := byteColToVisualColWithTabs rawContent sl.endCol

      labelParts := labelParts.push " "
      labelParts := labelParts.push (String.ofList (List.replicate (startVisualCol - 1) ' '))
      let underlineLen := if endVisualCol > startVisualCol then endVisualCol - startVisualCol else 1
      labelParts := labelParts.push color
      labelParts := labelParts.push (String.ofList (List.replicate underlineLen char))
      if !sl.message.isEmpty then
        labelParts := labelParts.push " "
        labelParts := labelParts.push sl.message
      labelParts := labelParts.push Color.reset

      output := output.push s!" {emptyGutter gutterWidth}{buildString labelParts}"

      if debug then
        output := output.push s!"  DEBUG LABEL: startCol(byte)={sl.startCol} endCol(byte)={sl.endCol}"
        output := output.push s!"  DEBUG LABEL: startVisualCol={startVisualCol} endVisualCol={endVisualCol}"
        output := output.push s!"  DEBUG LABEL: underline at pos {startVisualCol} for {underlineLen} chars"

    else if lineLabels.size > 1 then
      -- Multiple labels: render underlines first, then drop-down messages
      let mut underlineParts : Array String := #[]
      let mut underlineRowPos : Nat := 0

      for ms in activeSpans do
        -- +1 to account for space between margin and content
        let targetCol := ms.visualCol
        if targetCol >= underlineRowPos then
          let c := getMostSevereColorAtCol activeSpans ms.visualCol
          underlineParts := underlineParts.push (String.ofList (List.replicate (targetCol - underlineRowPos) ' '))
          underlineParts := underlineParts.push c
          underlineParts := underlineParts.push Chars.pipe
          underlineParts := underlineParts.push Color.reset
          underlineRowPos := targetCol + 1

      underlineParts := underlineParts.push " "
      underlineRowPos := underlineRowPos + 1

      -- Render all underlines character by character to handle overlaps correctly
      let minCol := lineLabels.foldl (fun acc sl => min acc (byteColToVisualColWithTabs rawContent sl.startCol)) 1000
      let maxCol := lineLabels.foldl (fun acc sl => max acc (byteColToVisualColWithTabs rawContent sl.endCol)) 0

      -- Pad to reach the first label
      if minCol > underlineRowPos then
        underlineParts := underlineParts.push (String.ofList (List.replicate (minCol - underlineRowPos) ' '))
        underlineRowPos := minCol

      -- Render each column, checking which labels cover it
      for col in List.range (maxCol - minCol) do
        let currentCol := minCol + col
        -- Find the most severe label covering this column
        let coveringLabels := lineLabels.filter fun sl =>
          let startVC := byteColToVisualColWithTabs rawContent sl.startCol
          let endVC := byteColToVisualColWithTabs rawContent sl.endCol
          currentCol >= startVC && currentCol < endVC

        if coveringLabels.isEmpty then
          underlineParts := underlineParts.push " "
        else
          -- Primary takes precedence over secondary
          let hasPrimary := coveringLabels.any (·.style == .primary)
          let char := if hasPrimary then Chars.underlineCaret else Chars.underlineTilde
          let color := if hasPrimary then Color.labelColor .primary else Color.labelColor .secondary
          underlineParts := underlineParts.push color
          underlineParts := underlineParts.push (String.ofList [char])
          underlineParts := underlineParts.push Color.reset

      output := output.push s!" {emptyGutter gutterWidth}{buildString underlineParts}"

      if debug then
        for sl in lineLabels do
          let startVC := byteColToVisualColWithTabs rawContent sl.startCol
          let endVC := byteColToVisualColWithTabs rawContent sl.endCol
          output := output.push s!"  DEBUG MULTI-LABEL: startCol={sl.startCol} endCol={sl.endCol} startVC={startVC} endVC={endVC}"

      -- Drop-down messages (rightmost to leftmost)
      let numLabels := lineLabels.size
      for idx in List.range numLabels |>.reverse do
        let currentLabel := lineLabels.getD idx default
        let color := Color.labelColor currentLabel.style

        let mut rowParts : Array String := #[]
        let mut rowPos : Nat := 0

        for ms in activeSpans do
          -- +1 to account for space between margin and content
          let targetCol := ms.visualCol
          if targetCol >= rowPos then
            let c := getMostSevereColorAtCol activeSpans ms.visualCol
            rowParts := rowParts.push (String.ofList (List.replicate (targetCol - rowPos) ' '))
            rowParts := rowParts.push c
            rowParts := rowParts.push Chars.pipe
            rowParts := rowParts.push Color.reset
            rowPos := targetCol + 1

        rowParts := rowParts.push " "
        rowPos := rowPos + 1

        -- Vertical pipes for labels to the left
        for i in List.range idx do
          let sl := lineLabels.getD i default
          let targetCol := byteColToVisualColWithTabs rawContent sl.startCol
          if targetCol > rowPos then
            rowParts := rowParts.push (String.ofList (List.replicate (targetCol - rowPos) ' '))
            rowPos := targetCol
          let c := Color.labelColor sl.style
          rowParts := rowParts.push c
          rowParts := rowParts.push Chars.pipe
          rowParts := rowParts.push Color.reset
          rowPos := rowPos + 1

        -- Corner and message
        let cornerCol := byteColToVisualColWithTabs rawContent currentLabel.startCol
        if cornerCol > rowPos then
          rowParts := rowParts.push (String.ofList (List.replicate (cornerCol - rowPos) ' '))

        rowParts := rowParts.push color
        rowParts := rowParts.push Chars.cornerBottomLeft
        rowParts := rowParts.push Chars.horizontal
        if !currentLabel.message.isEmpty then
          rowParts := rowParts.push " "
          rowParts := rowParts.push currentLabel.message
        rowParts := rowParts.push Color.reset

        output := output.push s!" {emptyGutter gutterWidth}{buildString rowParts}"

  output := output.push s!" {emptyGutter gutterWidth}"

  for note in d.notes do
    output := output.push s!" {Color.brightBlue}{Chars.notePrefix}{Color.reset} {Color.bold}note{Color.reset}: {note}"

  if let some helpText := d.help then
    output := output.push s!" {Color.green}{Chars.helpPrefix}{Color.reset} {Color.bold}help{Color.reset}: {helpText}"

  return String.intercalate "\n" output.toList

def renderDiagnostics (ds : Diagnostics) (sf : SourceFile) : String :=
  let rendered := ds.toList.map (renderDiagnostic · sf)
  String.intercalate "\n\n" rendered

/-- Render diagnostics with a source file map (multi-file support) -/
def renderDiagnosticsWithMap (ds : Diagnostics) (sourceMap : SourceFileMap) : String :=
  let rendered := ds.toList.filterMap fun d =>
    sourceMap.getForSpan? d.span |>.map fun sf =>
      renderDiagnostic d sf
  String.intercalate "\n\n" rendered

def printDiagnostic (d : Diagnostic) (sf : SourceFile) : IO Unit :=
  IO.eprintln (renderDiagnostic d sf)

def printDiagnostics (ds : Diagnostics) (sf : SourceFile) : IO Unit :=
  for d in ds do
    printDiagnostic d sf
    IO.eprintln ""

/-- Print diagnostics with a source file map (multi-file support) -/
def printDiagnosticsWithMap (ds : Diagnostics) (sourceMap : SourceFileMap) : IO Unit :=
  for d in ds do
    match sourceMap.getForSpan? d.span with
    | some sf =>
      IO.eprintln (renderDiagnostic d sf)
      IO.eprintln ""
    | none =>
      -- Fallback if source file not found (shouldn't happen)
      IO.eprintln s!"{d.severity}: {d.message}"
      IO.eprintln ""

def renderSummary (ds : Diagnostics) : String := Id.run do
  let errors := ds.filter (·.severity == .error) |>.size
  let warnings := ds.filter (·.severity == .warning) |>.size
  let mut parts : Array String := #[]
  if errors > 0 then
    let s := if errors == 1 then "error" else "errors"
    parts := parts.push s!"{Color.severityColor .error}{errors} {s}{Color.reset}"
  if warnings > 0 then
    let s := if warnings == 1 then "warning" else "warnings"
    parts := parts.push s!"{Color.severityColor .warning}{warnings} {s}{Color.reset}"
  if parts.isEmpty then
    s!"{Color.green}no errors{Color.reset}"
  else
    String.intercalate ", " parts.toList ++ " emitted"

/-- Convert severity to LSP DiagnosticSeverity number (Error=1, Warning=2, Information=3, Hint=4) -/
def severityToLspCode : Severity → Nat
  | .error => 1
  | .warning => 2
  | .info => 3
  | .hint => 4

open Kenosis (Encoder)
open Kenosis.Json (JsonWriter)

/-- Write a diagnostic to JSON -/
private def writeDiagnostic (d : Diagnostic) (filePath : String := "") : JsonWriter Unit := do
  let span := d.span
  Encoder.putObject [
    ("file", Encoder.putString filePath),
    ("range", Encoder.putObject [
      ("start", Encoder.putObject [
        ("line", Encoder.putNat span.start.line),
        ("character", Encoder.putNat span.start.column)
      ]),
      ("end", Encoder.putObject [
        ("line", Encoder.putNat span.stop.line),
        ("character", Encoder.putNat span.stop.column)
      ])
    ]),
    ("severity", Encoder.putNat (severityToLspCode d.severity)),
    ("message", Encoder.putString d.message),
    ("source", Encoder.putString (toString d.severity).toUpper),
    ("code", Encoder.putNull)
  ]

/-- Render diagnostics as JSON array -/
def renderDiagnosticsJson (diags : Diagnostics) (filePath : String := "") : String :=
  JsonWriter.run do
    Encoder.putList (diags.toList.map (writeDiagnostic · filePath))

/-- Render diagnostics as JSON array with source file map (multi-file support) -/
def renderDiagnosticsJsonWithMap (diags : Diagnostics) (sourceMap : SourceFileMap) : String :=
  JsonWriter.run do
    let items := diags.toList.map fun d =>
      let filePath := sourceMap.getForSpan? d.span |>.map (·.path) |>.getD ""
      writeDiagnostic d filePath
    Encoder.putList items

/-- Render check output as JSON object matching haoma's expected format -/
def renderCheckOutputJson (diags : Diagnostics) (moduleName : Option String := none) (filePath : String := "") : String :=
  JsonWriter.run do
    let success := !diags.hasErrors
    let baseFields : List (String × JsonWriter Unit) := [
      ("success", Encoder.putBool success),
      ("diagnostics", Encoder.putList (diags.toList.map (writeDiagnostic · filePath)))
    ]
    let fields := match moduleName with
      | some name => baseFields ++ [("module", Encoder.putString name)]
      | none => baseFields
    Encoder.putObject fields

end Soma.Logging.Error
