/-
  Features:

  - Colored output with Unicode box-drawing characters
  - Source code snippets with line numbers
  - Multiple labeled spans (primary and secondary)
  - Multi-line span support with vertical connectors
  - Line break indicators with connected pipes
  - Notes and help suggestions
-/

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

def renderDiagnostic (d : Diagnostic) (sf : SourceFile) : String := Id.run do
  let mut output : Array String := #[]

  let sevColor := Color.severityColor d.severity
  let sevText := toString d.severity
  let codeText := match d.code with
    | some c => s!"[{c}]"
    | none => ""
  output := output.push s!"{sevColor}{sevText}{codeText}{Color.reset}: {Color.bold}{d.message}{Color.reset}"

  if h : d.labels.size > 0 then
    let primarySpan := d.labels[0].span
    let arrow := s!"{Color.brightBlue}{Chars.cornerTopLeft}{Chars.horizontal}{Chars.arrowRight}{Color.reset}"
    output := output.push s!" {arrow} {sf.path}:{primarySpan.start.line}:{primarySpan.start.column}"

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

  -- Convert labels at same column to virtual spans (stacked with vertical connectors)
  let mut virtualSpans : Array MultiSpan := #[]
  let mut remainingSingleLabels : Array SingleLabel := #[]

  let singleLabelLines := singleLabels.map (·.line) |>.toList |> List.eraseDups |>.toArray

  for lineNum in singleLabelLines do
    let lineLabels := singleLabels.filter (·.line == lineNum)
    if lineLabels.size <= 1 then
      for sl in lineLabels do
        remainingSingleLabels := remainingSingleLabels.push sl
    else
      let sortedLabels := lineLabels.toList.mergeSort (fun a b => a.startCol < b.startCol) |>.toArray

      let mut groups : Array (Array SingleLabel) := #[]
      let mut currentGroup : Array SingleLabel := #[]

      for sl in sortedLabels do
        if currentGroup.isEmpty then
          currentGroup := currentGroup.push sl
        else
          let sameCol := currentGroup.any fun prev => sl.startCol == prev.startCol
          if sameCol then
            currentGroup := currentGroup.push sl
          else
            groups := groups.push currentGroup
            currentGroup := #[sl]

      if !currentGroup.isEmpty then
        groups := groups.push currentGroup

      for group in groups do
        if group.size == 1 then
          remainingSingleLabels := remainingSingleLabels.push group[0]!
        else
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

  let finalSingleLabels := remainingSingleLabels
  let multiSpansWithCols := assignVisualColumns multiSpans

  let mut allLines : Array Nat := #[]
  for sl in finalSingleLabels do
    if !allLines.contains sl.line then
      allLines := allLines.push sl.line
  for ms in multiSpansWithCols do
    if !allLines.contains ms.startLine then
      allLines := allLines.push ms.startLine
    if !allLines.contains ms.endLine then
      allLines := allLines.push ms.endLine
  for vs in virtualSpans do
    if !allLines.contains vs.startLine then
      allLines := allLines.push vs.startLine

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

    match prevLineNum with
    | some prev =>
        if lineNum > prev + 1 then
          let mut skipLine := ""
          let mut visualPos : Nat := 0
          for ms in activeSpans do
            let color := Color.labelColor ms.style
            let targetCol := ms.visualCol - 1
            let padding := String.ofList (List.replicate (targetCol - visualPos) ' ')
            skipLine := skipLine ++ padding ++ color ++ Chars.pipeDotted ++ Color.reset
            visualPos := targetCol + 1
          output := output.push s!" {skipGutter gutterWidth}{skipLine}"
    | none => pure ()

    prevLineNum := some lineNum

    let mut margin := ""
    let mut visualPos : Nat := 0
    for ms in activeSpans do
      let targetCol := ms.visualCol - 1
      if targetCol >= visualPos then
        let color := getMostSevereColorAtCol activeSpans ms.visualCol
        let padding := String.ofList (List.replicate (targetCol - visualPos) ' ')
        margin := margin ++ padding ++ color ++ Chars.pipe ++ Color.reset
        visualPos := targetCol + 1

    let content := sf.getLine lineNum
    let displayContent := if content.trim.isEmpty then
      s!"{Color.dim}<empty line>{Color.reset}"
    else
      content
    output := output.push s!" {gutter (some lineNum) gutterWidth}{margin} {displayContent}"

    for ms in multiSpansWithCols do
      if ms.startLine == lineNum then
        let color := Color.labelColor ms.style
        let connCol := ms.visualCol
        let startCol := ms.startCol
        let mut underlineMargin := ""
        let mut underlineVisualPos : Nat := 0
        for other in activeSpans do
          let targetCol := other.visualCol - 1
          if targetCol >= underlineVisualPos then
            let padding := String.ofList (List.replicate (targetCol - underlineVisualPos) ' ')
            let c := getMostSevereColorAtCol activeSpans other.visualCol
            underlineMargin := underlineMargin ++ padding ++ c ++ Chars.pipe ++ Color.reset
            underlineVisualPos := targetCol + 1
        let toCornerLen := connCol - 1 - underlineVisualPos
        let cornerPadding := String.ofList (List.replicate (max toCornerLen 0) ' ')
        let toStartLen := if startCol > connCol then startCol - connCol - 1 else 0
        let toStartHoriz := String.ofList (List.replicate toStartLen Chars.horizontalChar)
        let underlineLen := content.length - max startCol connCol + 2
        let underline := String.ofList (List.replicate (max underlineLen 0) Chars.horizontalChar)
        output := output.push s!" {emptyGutter gutterWidth}{underlineMargin}{cornerPadding}{color}{Chars.cornerTopLeft}{toStartHoriz}{underline}{Color.reset}"

    for ms in multiSpansWithCols do
      if ms.endLine == lineNum then
        let color := Color.labelColor ms.style
        let continuingSpans := activeSpans.filter fun other => other.endLine > lineNum

        let mut row := ""
        let mut rowPos : Nat := 0

        for other in activeSpans do
          let targetCol := other.visualCol - 1
          if targetCol < ms.visualCol - 1 && targetCol >= rowPos then
            let padding := String.ofList (List.replicate (targetCol - rowPos) ' ')
            let c := getMostSevereColorAtCol activeSpans other.visualCol
            row := row ++ padding ++ c ++ Chars.pipe ++ Color.reset
            rowPos := targetCol + 1

        let cornerCol := ms.visualCol - 1
        if cornerCol >= rowPos then
          let padding := String.ofList (List.replicate (cornerCol - rowPos) ' ')
          row := row ++ padding ++ color ++ Chars.cornerBottomLeft ++ Color.reset
          rowPos := cornerCol + 1

        -- Draw horizontal line, using cross (┼) where continuing spans intersect
        let endPos := ms.endCol + ms.visualCol
        for col in List.range endPos do
          let actualCol := rowPos + col
          let hasContinuing := continuingSpans.any fun s => s.visualCol == actualCol + 1
          if hasContinuing then
            let continuingStyle := continuingSpans.foldl (fun acc s =>
              if s.visualCol == actualCol + 1 then mostSevereStyle acc s.style else acc) LabelStyle.secondary
            let combinedStyle := mostSevereStyle ms.style continuingStyle
            let c := Color.labelColor combinedStyle
            row := row ++ c ++ Chars.cross ++ Color.reset
          else
            row := row ++ color ++ Chars.horizontal ++ Color.reset

        let msgPart := if ms.message.isEmpty then "" else " " ++ ms.message
        row := row ++ color ++ msgPart ++ Color.reset
        output := output.push s!" {emptyGutter gutterWidth}{row}"

    -- Render stacked labels (virtual spans)
    let lineVirtualSpans := virtualSpans.filter (·.startLine == lineNum)
    if !lineVirtualSpans.isEmpty then
      let sortedVirtual := lineVirtualSpans.toList.mergeSort (fun a b => a.startCol < b.startCol) |>.toArray
      let numSpans := sortedVirtual.size

      let mut firstRow := ""
      let mut firstRowPos : Nat := 0
      for ms in activeSpans do
        let targetCol := ms.visualCol - 1
        if targetCol >= firstRowPos then
          let color := getMostSevereColorAtCol activeSpans ms.visualCol
          let padding := String.ofList (List.replicate (targetCol - firstRowPos) ' ')
          firstRow := firstRow ++ padding ++ color ++ Chars.pipe ++ Color.reset
          firstRowPos := targetCol + 1

      let mut lastCol : Nat := 0
      let mut idx : Nat := 0
      for vs in sortedVirtual do
        let targetCol := vs.startCol - 1
        if targetCol >= firstRowPos then
          let color := getMostSevereColorAtColVirtual sortedVirtual vs.startCol
          let padding := String.ofList (List.replicate (targetCol - firstRowPos) ' ')
          firstRow := firstRow ++ padding ++ color ++ Chars.teeRight ++ Color.reset
          firstRowPos := targetCol + 1
        lastCol := targetCol
        idx := idx + 1
      if h : sortedVirtual.size > 0 then
        let lastSpan := sortedVirtual[sortedVirtual.size - 1]!
        if !lastSpan.message.isEmpty then
          firstRow := firstRow ++ Color.labelColor lastSpan.style ++ Chars.horizontal ++ " " ++ lastSpan.message ++ Color.reset
      output := output.push s!" {emptyGutter gutterWidth}{firstRow}"

      for spanIdx in List.range (numSpans - 1) |>.reverse do
        let currentSpan := sortedVirtual[spanIdx]!
        let color := Color.labelColor currentSpan.style

        let mut row := ""
        let mut rowPos : Nat := 0

        for ms in activeSpans do
          let targetCol := ms.visualCol - 1
          if targetCol >= rowPos then
            let c := getMostSevereColorAtCol activeSpans ms.visualCol
            let padding := String.ofList (List.replicate (targetCol - rowPos) ' ')
            row := row ++ padding ++ c ++ Chars.pipe ++ Color.reset
            rowPos := targetCol + 1

        let cornerCol := currentSpan.startCol - 1
        let mut drewCorner := false
        for i in List.range spanIdx do
          let vs := sortedVirtual[i]!
          let targetCol := vs.startCol - 1
          if targetCol >= rowPos then
            let padding := String.ofList (List.replicate (targetCol - rowPos) ' ')
            if targetCol == cornerCol then
              let c := getMostSevereColorAtColVirtual sortedVirtual vs.startCol
              row := row ++ padding ++ c ++ Chars.teeRight ++ Color.reset
              drewCorner := true
            else
              let c := getMostSevereColorAtColVirtual sortedVirtual vs.startCol
              row := row ++ padding ++ c ++ Chars.pipe ++ Color.reset
            rowPos := targetCol + 1

        let msgPart := if currentSpan.message.isEmpty then "" else " " ++ currentSpan.message
        if drewCorner then
          row := row ++ color ++ Chars.horizontal ++ msgPart ++ Color.reset
        else if cornerCol >= rowPos then
          let padding := String.ofList (List.replicate (cornerCol - rowPos) ' ')
          row := row ++ padding ++ color ++ Chars.cornerBottomLeft ++ Chars.horizontal ++ msgPart ++ Color.reset
        else
          row := row ++ color ++ Chars.horizontal ++ msgPart ++ Color.reset

        output := output.push s!" {emptyGutter gutterWidth}{row}"

    let lineLabels := (finalSingleLabels.filter (·.line == lineNum)).toList.mergeSort (fun a b => a.startCol < b.startCol) |>.toArray

    if lineLabels.size == 1 then
      -- Single label: render with message inline (original behavior)
      let sl := lineLabels[0]!
      let color := Color.labelColor sl.style
      let char := match sl.style with
        | .primary => Chars.underlineCaret
        | .secondary => Chars.underlineTilde
      let mut labelMargin := ""
      let mut labelVisualPos : Nat := 0
      for ms in activeSpans do
        let targetCol := ms.visualCol - 1
        if targetCol >= labelVisualPos then
          let padding := String.ofList (List.replicate (targetCol - labelVisualPos) ' ')
          let c := getMostSevereColorAtCol activeSpans ms.visualCol
          labelMargin := labelMargin ++ padding ++ c ++ Chars.pipe ++ Color.reset
          labelVisualPos := targetCol + 1
      let underlinePadding := String.ofList (List.replicate (sl.startCol - 1) ' ')
      let underlineLen := if sl.endCol > sl.startCol then sl.endCol - sl.startCol else 1
      let underlineStr := String.ofList (List.replicate underlineLen char)
      let msgPart := if sl.message.isEmpty then "" else " " ++ sl.message
      output := output.push s!" {emptyGutter gutterWidth}{labelMargin} {underlinePadding}{color}{underlineStr}{msgPart}{Color.reset}"

    else if lineLabels.size > 1 then
      -- Multiple labels on same line: render underlines first, then drop-down messages
      -- First row: all underlines without messages
      let mut underlineRow := ""
      let mut underlineRowPos : Nat := 0

      -- Add margin for active multi-line spans
      for ms in activeSpans do
        let targetCol := ms.visualCol - 1
        if targetCol >= underlineRowPos then
          let padding := String.ofList (List.replicate (targetCol - underlineRowPos) ' ')
          let c := getMostSevereColorAtCol activeSpans ms.visualCol
          underlineRow := underlineRow ++ padding ++ c ++ Chars.pipe ++ Color.reset
          underlineRowPos := targetCol + 1

      -- Add space after gutter margin
      underlineRow := underlineRow ++ " "
      underlineRowPos := underlineRowPos + 1

      -- Render all underlines
      for sl in lineLabels do
        let color := Color.labelColor sl.style
        let char := match sl.style with
          | .primary => Chars.underlineCaret
          | .secondary => Chars.underlineTilde
        let targetCol := sl.startCol
        if targetCol > underlineRowPos then
          let padding := String.ofList (List.replicate (targetCol - underlineRowPos) ' ')
          underlineRow := underlineRow ++ padding
          underlineRowPos := targetCol
        let underlineLen := if sl.endCol > sl.startCol then sl.endCol - sl.startCol else 1
        let underlineStr := String.ofList (List.replicate underlineLen char)
        underlineRow := underlineRow ++ color ++ underlineStr ++ Color.reset
        underlineRowPos := underlineRowPos + underlineLen

      output := output.push s!" {emptyGutter gutterWidth}{underlineRow}"

      -- Now render drop-down messages, from rightmost to leftmost (bottom to top visually)
      let numLabels := lineLabels.size
      for idx in List.range numLabels |>.reverse do
        let currentLabel := lineLabels[idx]!
        let color := Color.labelColor currentLabel.style

        let mut row := ""
        let mut rowPos : Nat := 0

        -- Add margin for active multi-line spans
        for ms in activeSpans do
          let targetCol := ms.visualCol - 1
          if targetCol >= rowPos then
            let padding := String.ofList (List.replicate (targetCol - rowPos) ' ')
            let c := getMostSevereColorAtCol activeSpans ms.visualCol
            row := row ++ padding ++ c ++ Chars.pipe ++ Color.reset
            rowPos := targetCol + 1

        -- Add space after gutter margin
        row := row ++ " "
        rowPos := rowPos + 1

        -- Draw vertical pipes for labels to the left that still need messages below
        for i in List.range idx do
          let sl := lineLabels[i]!
          let targetCol := sl.startCol
          if targetCol > rowPos then
            let padding := String.ofList (List.replicate (targetCol - rowPos) ' ')
            row := row ++ padding
            rowPos := targetCol
          let c := Color.labelColor sl.style
          row := row ++ c ++ Chars.pipe ++ Color.reset
          rowPos := rowPos + 1

        -- Draw corner and message for current label
        let cornerCol := currentLabel.startCol
        if cornerCol > rowPos then
          let padding := String.ofList (List.replicate (cornerCol - rowPos) ' ')
          row := row ++ padding
          rowPos := cornerCol
        let msgPart := if currentLabel.message.isEmpty then "" else " " ++ currentLabel.message
        row := row ++ color ++ Chars.cornerBottomLeft ++ Chars.horizontal ++ msgPart ++ Color.reset

        output := output.push s!" {emptyGutter gutterWidth}{row}"

  output := output.push s!" {emptyGutter gutterWidth}"

  for note in d.notes do
    output := output.push s!" {Color.brightBlue}{Chars.notePrefix}{Color.reset} {Color.bold}note{Color.reset}: {note}"

  if let some helpText := d.help then
    output := output.push s!" {Color.green}{Chars.helpPrefix}{Color.reset} {Color.bold}help{Color.reset}: {helpText}"

  return String.intercalate "\n" output.toList

def renderDiagnostics (ds : Diagnostics) (sf : SourceFile) : String :=
  let rendered := ds.toList.map (renderDiagnostic · sf)
  String.intercalate "\n\n" rendered

def printDiagnostic (d : Diagnostic) (sf : SourceFile) : IO Unit :=
  IO.eprintln (renderDiagnostic d sf)

def printDiagnostics (ds : Diagnostics) (sf : SourceFile) : IO Unit :=
  for d in ds do
    printDiagnostic d sf
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

end Soma.Logging.Error
