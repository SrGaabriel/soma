import Psychopomp

namespace Soma.Diagnostic.Cascade

open Psychopomp

/-- Read `SOMA_COLLAPSE` to decide whether collapse is disabled (TODO) -/
def disabled : IO Bool := do
  match ← IO.getEnv "SOMA_COLLAPSE" with
  | none => return true
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

/-- Find the first error-severity diagnostic in `ds` that lives in `substrate` -/
private def findRoot (ds : Array Diagnostic) (substrate : Nat) : Option Diagnostic := Id.run do
  let mut best : Option Diagnostic := none
  for d in ds do
    if d.severity.level != .error then continue
    if d.primary.substrate != substrate then continue
    match best with
    | none => best := some d
    | some r =>
      if phaseRank d.severity.phase < phaseRank r.severity.phase then
        best := some d
  return best

/-- Collapse one file's worth of diagnostics -/
private def collapseFile (file : Nat) (ds : Array Diagnostic) : Array Diagnostic := Id.run do
  match findRoot ds file with
  | none => return ds
  | some root =>
    let rootPhase := root.severity.phase
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
      if shouldAbsorb rootPhase d.severity.phase then
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
