import Psychopomp
import Soma.Core.Value
import Soma.Core.Pp
import Soma.Diagnostic
import Soma.Diagnostic.Attach

namespace Soma.Diagnostic.Pretty.Substrate

open Psychopomp

/-- Construct a `SubstrateView` from a pretty-printed value -/
def ofString (text : String) (name : String) (tabWidth : Nat := 4)
    : SubstrateView :=
  let lines := text.splitOn "\n"
  let lineArr := lines.toArray
  { name
    kind := .custom "type"
    numLines := lineArr.size
    getLine := fun n =>
      if n == 0 then ""
      else if h : n - 1 < lineArr.size then lineArr[n - 1] else ""
    tabWidth }

/-- Pretty-print a value -/
def ofValue (pp : Soma.Core.PpContext) (v : Soma.Core.Value)
    (name : String) (tabWidth : Nat := 4) : SubstrateView :=
  ofString (Soma.Core.Value.pp pp v) name tabWidth

/-- The full span of a substrate view -/
def fullSpan (view : SubstrateView) : Span :=
  if view.numLines == 0 then
    { startLine := 1, startCol := 0, endLine := 1, endCol := 0 }
  else
    let last := view.getLine view.numLines
    { startLine := 1, startCol := 0
      endLine := view.numLines
      endCol := last.length }

/-- Look up the rendered span for an exact path in a PpOutput -/
def findTokenSpan (out : Soma.Core.PpOutput) (path : Soma.Core.Path) : Option Span :=
  out.spans[path]?.map fun sub =>
    { startLine := sub.startLine, startCol := sub.startCol
      endLine := sub.endLine, endCol := sub.endCol }

/-- Resolve a Path to the span the substrate decorator should underline -/
def resolveOperandPath (out : Soma.Core.PpOutput) (view : SubstrateView)
    (path : Soma.Core.Path) : Span :=
  if path.isEmpty then fullSpan view
  else
    match findTokenSpan out path with
    | some s => s
    | none =>
      panic! s!"resolveOperandPath: path `{path.describe}` has no rendered span in `{view.name}`"

/-- Build a substrate view from a `PpOutput` -/
def ofPpOutput (out : Soma.Core.PpOutput) (name : String) (tabWidth : Nat := 4)
    : SubstrateView :=
  ofString out.text name tabWidth

/-- A single hypothesis in a printed goal-state -/
structure GoalHyp where
  name : String
  type : String
  deriving Repr, Inhabited

/-- The fully-printed goal-state, ready for substrate wrapping -/
structure RenderedGoal where
  /-- One line per hypothesis -/
  hypLines : List String
  /-- The pretty-printed target -/
  targetOut : Soma.Core.PpOutput
  /-- The turnstile-prefix's length -/
  turnstilePrefix : String := "⊢ "
  deriving Inhabited

namespace RenderedGoal

/-- 1-indexed line number -/
def targetLine (g : RenderedGoal) : Nat := g.hypLines.length + 1

/-- Translate a `Path` inside the target to a `Span` -/
def targetSpan (g : RenderedGoal) (path : Soma.Core.Path) : Option Span :=
  g.targetOut.spans[path]?.map fun sub =>
    let prefixLen := g.turnstilePrefix.length
    let lineOffset := g.targetLine - 1
    let startCol := if sub.startLine == 1 then sub.startCol + prefixLen else sub.startCol
    let endCol := if sub.endLine == 1 then sub.endCol + prefixLen else sub.endCol
    { startLine := sub.startLine + lineOffset, startCol
      endLine := sub.endLine + lineOffset, endCol }

/-- The full lines of the rendered view, in order -/
def allLines (g : RenderedGoal) : List String :=
  g.hypLines ++ [g.turnstilePrefix ++ g.targetOut.text]

end RenderedGoal

/-- Render a goal-state into a multi-line substrate view -/
def renderGoal (pp : Soma.Core.PpContext) (hypotheses : List GoalHyp)
    (target : Soma.Core.Value) : RenderedGoal :=
  let hypLines := hypotheses.map fun h => s!"{h.name} : {h.type}"
  let targetOut := Soma.Core.Value.ppWithSpans pp target
  { hypLines, targetOut }

/-- Build a `SubstrateView` from a `RenderedGoal` and a header name -/
def ofGoal (g : RenderedGoal) (name : String) (tabWidth : Nat := 4)
    : SubstrateView :=
  let lineArr := g.allLines.toArray
  { name
    kind := .custom "goal"
    numLines := lineArr.size
    getLine := fun n =>
      if n == 0 then ""
      else if h : n - 1 < lineArr.size then lineArr[n - 1] else ""
    tabWidth }

end Soma.Diagnostic.Pretty.Substrate

namespace Soma.DiagContext

open Psychopomp

/-- Register a value-substrate view in the project repo -/
def putGoalView (ctx : Soma.DiagContext) (view : SubstrateView)
    : Soma.DiagContext × SubstrateRef :=
  let (repo', ref) := ctx.repo.putSynthetic view
  ({ ctx with repo := repo' }, ref)

/-- Convenience: build + register a value-substrate in one call -/
def putValueSubstrate (ctx : Soma.DiagContext) (pp : Soma.Core.PpContext)
    (v : Soma.Core.Value) (name : String) (message : String)
    (style : LabelStyle := .support)
    : Soma.DiagContext × SubstrateRef × Label :=
  let view := Soma.Diagnostic.Pretty.Substrate.ofValue pp v name
  let (ctx', ref) := ctx.putGoalView view
  let label : Label :=
    { substrate := ref
      range := Soma.Diagnostic.Pretty.Substrate.fullSpan view
      message := some message
      style }
  (ctx', ref, label)

/-- Register a goal-state substrate and produce the ref plus a label anchored inside it -/
def putGoalSubstrate (ctx : Soma.DiagContext) (pp : Soma.Core.PpContext)
    (hypotheses : List Soma.Diagnostic.Pretty.Substrate.GoalHyp)
    (target : Soma.Core.Value) (name : String) (message : String)
    (style : LabelStyle := .support)
    (targetPath : Soma.Core.Path := Soma.Core.Path.empty)
    : Soma.DiagContext × SubstrateRef × Label :=
  let g := Soma.Diagnostic.Pretty.Substrate.renderGoal pp hypotheses target
  let view := Soma.Diagnostic.Pretty.Substrate.ofGoal g name
  let (ctx', ref) := ctx.putGoalView view
  let range : Span :=
    if let some s := g.targetSpan targetPath then s
    else
      let lastLine := view.numLines
      let last := view.getLine lastLine
      { startLine := lastLine, startCol := 0
        endLine := lastLine, endCol := last.length }
  let label : Label :=
    { substrate := ref, range, message := some message, style }
  (ctx', ref, label)

end Soma.DiagContext

namespace Soma.Diagnostic.Pretty.Substrate

open Psychopomp

/-- Decorate a base diagnostic with value-substrate snippets -/
def decorateBinary (ctx : Soma.DiagContext) (pp : Soma.Core.PpContext)
    (expected actual : Soma.Core.Value) (sourceName : String)
    (d : Diagnostic) (path : Soma.Core.Path := Soma.Core.Path.empty)
    : Soma.DiagContext × Diagnostic :=
  let expOut := Soma.Core.Value.ppWithSpans pp expected
  let actOut := Soma.Core.Value.ppWithSpans pp actual
  let expView := ofPpOutput expOut s!"<expected at {sourceName}>"
  let actView := ofPpOutput actOut s!"<actual at {sourceName}>"
  let group := s!"mismatch-at-{sourceName}"
  let expRange := resolveOperandPath expOut expView path
  let actRange := resolveOperandPath actOut actView path
  let (ctx₁, expRef) := ctx.putGoalView expView
  let (ctx₂, actRef) := ctx₁.putGoalView actView
  let expStyle : LabelStyle :=
    { LabelStyle.support with linkGroup := some group }
  let actStyle : LabelStyle :=
    { LabelStyle.error with linkGroup := some group }
  let expLabel : Label :=
    { substrate := expRef, range := expRange
      message := some "expected type", style := expStyle }
  let actLabel : Label :=
    { substrate := actRef, range := actRange
      message := some "actual type", style := actStyle }
  let d' :=
    { d with secondary := d.secondary ++ [expLabel, actLabel] }
  (ctx₂, d')

end Soma.Diagnostic.Pretty.Substrate
