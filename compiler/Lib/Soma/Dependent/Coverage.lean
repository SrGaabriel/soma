import Soma.Core.Value
import Soma.Core.Expr
import Soma.Core.Primitive
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Error
import Soma.Syntax.Source

namespace Soma.Dependent.Coverage

open Soma (Unique)
open Soma.Core
open Soma.Syntax (Span)

/-- Head-shape a pattern column dispatches on -/
inductive Head where
  | ctor (tag : Nat) (arity : Nat)
  | lit (l : Literal)
  | variant (label : String) (hasPayload : Bool)
  deriving BEq, Repr, Inhabited

/-- A candidate inhabitant head at a column, with the sub-column types it -/
structure Candidate where
  display : String
  head : Head
  fieldTypes : List Value
  deriving Inhabited

/-- A pattern that matches anything and binds zero structure. -/
def isTrivialPattern : Pattern → Bool
  | .var _ => true
  | .wildcard => true
  | _ => false

/-- Row is fully trivial: matches every value shape at every column -/
def rowIsTrivial (row : Array Pattern) : Bool :=
  row.all isTrivialPattern

/-- Does the row's leading pattern delegate to the default column -/
def rowStartsTrivial (row : Array Pattern) : Bool :=
  match row[0]? with
  | some p => isTrivialPattern p
  | none => false

/-- Match two literal patterns for equality -/
def literalEq : Literal → Literal → Bool
  | .int a, .int b => a == b
  | .string a, .string b => a == b
  | .bool a, .bool b => a == b
  | _, _ => false

/-- Specialize a row against `head` -/
def specializeRow (head : Head) (arity : Nat) (row : Array Pattern) : Option (Array Pattern) :=
  match row[0]? with
  | none => none
  | some p =>
    let rest := row.extract 1 row.size
    match p with
    | .var _ | .wildcard =>
      let wilds := (Array.range arity).map (fun _ => Pattern.wildcard)
      some (wilds ++ rest)
    | .ctor _ tag fields =>
      match head with
      | .ctor t _ => if tag == t then some (fields ++ rest) else none
      | _ => none
    | .lit l =>
      match head with
      | .lit l' => if literalEq l l' then some rest else none
      | _ => none
    | .inject label arg =>
      match head with
      | .variant l hasPayload =>
        if label != l then none
        else
          match arg with
          | some payload => some (#[payload] ++ rest)
          | none =>
            if hasPayload then some (#[Pattern.wildcard] ++ rest)
            else some rest
      | _ => none

/-- Drop the leading column, keeping only rows whose first pattern is trivial -/
def defaultMatrix (matrix : Array (Array Pattern)) : Array (Array Pattern) :=
  matrix.filterMap fun row =>
    if rowStartsTrivial row then some (row.extract 1 row.size) else none

/-- Walk a ctor's Pi chain to collect (resultType, explicitFieldTypes) -/
partial def instantiateCtor (ctorTy : Value) : TCM (Value × List Value) := do
  let rec go (ty : Value) (acc : List Value) : TCM (List Value × Value) := do
    let ty' ← force ty
    match ty' with
    | .vPi _ binder _ dom cod =>
      if binder.isImplicit then
        let metaVal ← TCM.freshMetaVal dom
        let r ← applyClosure cod metaVal
        go r acc
      else
        let lvl ← TCM.currentLevel
        let dummy := Value.vNeutral dom (.nVar ⟨"_cov", lvl⟩)
        let r ← applyClosure cod dummy
        go r (acc ++ [dom])
    | _ => return (acc, ty')
  let (fs, result) ← go ctorTy []
  return (result, fs)

/-- Collect `(label, payloadType)` pairs from a variant row -/
partial def collectRowLabelsWithTypes (row : Value) : TCM (Array (String × Value)) := do
  match ← force row with
  | .vRowEmpty => return #[]
  | .vRowExtend (.vLabelLit name) ty tail =>
    let rest ← collectRowLabelsWithTypes tail
    return #[(name, ty)] ++ rest
  | .vRowExtend _ _ tail => collectRowLabelsWithTypes tail
  | _ => return #[]

/-- Is a row terminated by an empty row (fully closed) or by a meta/neutral -/
partial def rowIsClosed (row : Value) : TCM Bool := do
  match ← force row with
  | .vRowEmpty => return true
  | .vRowExtend _ _ tail => rowIsClosed tail
  | _ => return false

/-- Enumerate the live heads for a scrutinee type -/
partial def liveCandidates (scrutTy : Value) : TCM (Bool × Array Candidate) := do
  let ty ← force scrutTy
  match ty with
  | .vDataType typeId _ =>
    let ctx ← TCM.getCtx
    let typeQN : QualifiedName := ⟨typeId⟩
    match ctx.globals.lookupInductive typeQN with
    | some indMeta =>
      let mut live : Array Candidate := #[]
      for ctor in indMeta.ctors do
        let savedState ← get
        let (resultTy, fieldTypes) ← instantiateCtor ctor.type
        let incompat ← structurallyIncompatible resultTy scrutTy
        if incompat then
          set savedState
        else
          let display := s!"{typeQN.display}::{ctor.simpleName}"
          live := live.push {
            display,
            head := .ctor ctor.tag fieldTypes.length,
            fieldTypes
          }
      return (false, live)
    | none =>
      return (true, #[])
  | .vVariant row =>
    if !(← rowIsClosed row) then
      return (true, #[])
    let labels ← collectRowLabelsWithTypes row
    let cands : Array Candidate := labels.map fun (label, labelTy) => {
      display := s!".{label}",
      head := .variant label true,
      fieldTypes := [labelTy]
    }
    return (false, cands)
  | .vSigma _qty _name fstTy sndClos =>
    -- Sigma types have a single inhabitant (the pair constructor)
    let pairInfo? ← TCM.lookupWiredIn .pair
    match pairInfo? with
    | some info =>
      let lvl ← TCM.currentLevel
      let dummy := Value.vNeutral fstTy (.nVar ⟨"_pair", lvl⟩)
      let sndTy ← applyClosure sndClos dummy
      let cand : Candidate := {
        display := s!"({fstTy}, {sndTy})",
        head := .ctor info.ctorTag 2,
        fieldTypes := [fstTy, sndTy]
      }
      return (false, #[cand])
    | none =>
      return (true, #[])
  | _ => return (true, #[])

/-- Core exhaustiveness check -/
partial def isExhaustive
    (matrix : Array (Array Pattern)) (types : List Value)
    : TCM (Option (Array String)) := do
  -- Case 1: a row of all-trivial patterns matches any value shape
  if matrix.any rowIsTrivial then return none
  match types with
  | [] =>
    -- No columns left but no trivial row exists: the matrix does not match
    if matrix.isEmpty then return some #[] else return none
  | ty :: restTys =>
    if !matrix.isEmpty && matrix.all rowStartsTrivial then
      match ← isExhaustive (defaultMatrix matrix) restTys with
      | none => return none
      | some witness => return some (#["_"] ++ witness)
    let (isOpen, cands) ← liveCandidates ty
    if cands.isEmpty then
      if !isOpen then
        return none
      -- Open type: exhaustiveness requires a wildcard column-0 row
      let hasWild := matrix.any rowStartsTrivial
      if !hasWild then return some #["_"]
      match ← isExhaustive (defaultMatrix matrix) restTys with
      | none => return none
      | some witness => return some (#["_"] ++ witness)
    else
      -- Enumerable: every live candidate must specialize exhaustively
      for cand in cands do
        let arity := match cand.head with
          | .ctor _ a => a
          | .variant _ hasP => if hasP then 1 else 0
          | .lit _ => 0
        let spec := matrix.filterMap (specializeRow cand.head arity)
        let subTypes := cand.fieldTypes ++ restTys
        match ← isExhaustive spec subTypes with
        | none => pure ()
        | some witness =>
          let fieldW := witness.extract 0 arity
          let restW := witness.extract arity witness.size
          let rendered :=
            if arity == 0 then cand.display
            else s!"{cand.display}({String.intercalate ", " fieldW.toList})"
          return some (#[rendered] ++ restW)
      return none

/-- Entry point -/
def checkExhaustiveness
    (arms : Array Arm) (scrutTys : List Value) (span : Span) : TCM Unit := do
  if arms.isEmpty || scrutTys.isEmpty then
    if arms.isEmpty ∧ !scrutTys.isEmpty then
      let scrutType := scrutTys.head?.getD (.vType .zero)
      TCM.addError (.nonExhaustiveMatch scrutType #[] span)
    return
  let matrix : Array (Array Pattern) := arms.map (·.patterns)
  let savedState ← get
  let result ← isExhaustive matrix scrutTys
  set savedState
  match result with
  | none => pure ()
  | some missing =>
    let scrutType := scrutTys.head?.getD (.vType .zero)
    TCM.addError (.nonExhaustiveMatch scrutType missing span)

end Soma.Dependent.Coverage
