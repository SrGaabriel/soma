import Psychopomp

namespace Soma.Diagnostic.Cascade

open Psychopomp

/-- The audience tag -/
def cascadeRootTag : String := "soma:cascade-root"

/-- Whether a diagnostic was tagged as a cascade root by its producer -/
def isCascadeRoot (d : Diagnostic) : Bool :=
  d.severity.audiences.contains cascadeRootTag

def disabled : IO Bool := do
  match ← IO.getEnv "SOMA_COLLAPSE" with
  | none => return false
  | some s =>
    let t := s.trimAscii
    return (t == "0" || t == "false")

/-- Phase priority -/
def phaseRank : Option String → Nat
  | some "parse" => 0
  | some "lower" => 1
  | some "elaborate" => 2
  | some "codegen" => 3
  | some "link" => 4
  | _ => 5

/-- Whether a diagnostic at phase `b` should be absorbed under a root cause -/
def shouldAbsorb (rootPhase childPhase : Option String) : Bool :=
  phaseRank rootPhase < phaseRank childPhase

private def spanContains (outer inner : Span) : Bool :=
  let startsBefore :=
    outer.startLine < inner.startLine ||
      (outer.startLine == inner.startLine && outer.startCol <= inner.startCol)
  let endsAfter :=
    outer.endLine > inner.endLine ||
      (outer.endLine == inner.endLine && outer.endCol >= inner.endCol)
  startsBefore && endsAfter

private def shouldAbsorbDiagnostic (root child : Diagnostic) : Bool :=
  root.primary.substrate == child.primary.substrate &&
    (shouldAbsorb root.severity.phase child.severity.phase ||
      (isCascadeRoot root && spanContains root.primary.range child.primary.range))

/-- Pick the cascade root inside a single substrate -/
private def findRoot (ds : Array Diagnostic) (substrate : Nat) : Option Diagnostic := Id.run do
  let mut best : Option Diagnostic := none
  for d in ds do
    if d.severity.level != .error then continue
    if d.primary.substrate != substrate then continue
    match best with
    | none => best := some d
    | some r =>
      if isCascadeRoot d && !isCascadeRoot r then
        best := some d
      else if isCascadeRoot d == isCascadeRoot r &&
          phaseRank d.severity.phase < phaseRank r.severity.phase then
        best := some d
  return best

/-- Collapse one file's worth of diagnostics -/
private def collapseFile (file : Nat) (ds : Array Diagnostic) : Array Diagnostic := Id.run do
  match findRoot ds file with
  | none => return ds
  | some root =>
    let rootId := root.id
    let isRoot (d : Diagnostic) : Bool :=
      d.primary.substrate == root.primary.substrate
      && d.primary.range == root.primary.range
      && d.code == root.code
      && d.id == rootId
    let mut keep : Array Diagnostic := #[]
    let mut children : Array Diagnostic := #[]
    for d in ds do
      if d.primary.substrate != file then
        keep := keep.push d
        continue
      if isRoot d then
        continue
      if shouldAbsorbDiagnostic root d then
        children := children.push d
      else
        keep := keep.push d
    let rootWithChildren : Diagnostic :=
      { root with causedBy := root.causedBy ++ children.toList }
    return #[rootWithChildren] ++ keep

/-- Collapse cascades across the full diagnostic array -/
def collapse (ds : Array Diagnostic) : Array Diagnostic := Id.run do
  let mut substrates : Array Nat := #[]
  for d in ds do
    if !substrates.contains d.primary.substrate then
      substrates := substrates.push d.primary.substrate
  let mut working := ds
  for s in substrates do
    working := collapseFile s working
  return working

def maybeCollapse (ds : Array Diagnostic) : IO (Array Diagnostic) := do
  if ← disabled then return ds else return collapse ds

end Soma.Diagnostic.Cascade
