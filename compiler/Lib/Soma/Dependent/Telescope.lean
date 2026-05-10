import Soma.Syntax.Ast
import Soma.Core.Value
import Soma.Core.Quote
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Instance

namespace Soma.Dependent

open Soma.Core
open Soma.Syntax (Span)

/-- The semantic role of a binder inside an elaborated telescope -/
inductive BinderRole where
  | param
  | index
  | field
  | termParam
  | typeParam
  | instanceDict
  | autoImplicit
  | selfDict
  deriving Inhabited, BEq, Repr

/-- A binder before it has been elaborated into the local context -/
structure BinderSpec where
  name : String
  kindSyntax : Option Soma.Syntax.Expr := none
  quantity : Quantity := .omega
  binderInfo : BinderInfo := .explicit
  role : BinderRole := .termParam
  span : Span := Span.uninhabited
  deriving Inhabited, Repr

/-- A binder after introduction into the local context -/
structure LocalBinder where
  name : String
  unique : Soma.Unique
  type : Value
  typeExpr : Expr
  quantity : Quantity
  binderInfo : BinderInfo
  role : BinderRole
  span : Span
  level : DeBruijnLvl
  deriving Inhabited

/-- Extract class information from a local dictionary type -/
def extractClassInfo? : Value → Option (Soma.Unique × Array Value)
  | .vDataType unique args => some (unique, args.toArray)
  | _ => none

/-- The value of a locally-bound dictionary variable -/
def localDictValue (dictName : String) (dictTy : Value) : TCM Value := do
  match ← TCM.lookupLocal dictName with
  | some entry =>
    pure (Value.vNeutral dictTy (.nVar ⟨dictName, entry.level⟩))
  | none =>
    panic! s!"localDictValue: dictionary `{dictName}` is not bound in the local \
context (callers must install the binding via TCM.withBinding first)"

/-- Register an already-bound local dictionary as a temporary local instance -/
def withLocalInstanceForBoundDict (dictName : String) (_dictUnique : Soma.Unique)
    (dictTy : Value) (span : Span) (action : TCM α) : TCM α := do
  let forcedTy ← Soma.Dependent.force dictTy
  match extractClassInfo? forcedTy with
  | none => action
  | some (classId, classArgs) =>
    let instUnique ← TCM.freshUnique s!"$localInst_{dictName}"
    let dictValue ← localDictValue dictName dictTy
    let instInfo : InstanceInfo := {
      instanceId := instUnique
      classId := classId
      args := classArgs
      constraints := #[]
      value := dictValue
      span := span
    }
    let env ← TCM.getInstanceEnv
    let env' ← env.addInstanceWithIdForced instInfo
    TCM.withInstanceEnv env' action

/-- Bind an instance dictionary and register it in the local instance scope -/
def withLocalInstanceBinding (dictName : String) (dictUnique : Soma.Unique)
    (dictTy : Value) (qty : Quantity := .omega)
    (span : Span := Span.uninhabited) (action : TCM α) : TCM α :=
  TCM.withBinding dictName dictUnique dictTy qty .instance_ span do
    withLocalInstanceForBoundDict dictName dictUnique dictTy span action

/-- Bind a dictionary parameter with a concrete resolved value -/
def withResolvedInstanceBinding (dictName : String) (dictUnique : Soma.Unique)
    (dictTy : Value) (resolvedValue : Value) (qty : Quantity := .omega)
    (span : Span := Span.uninhabited) (action : TCM α) : TCM α :=
  TCM.withBindingValue dictName dictUnique dictTy qty .instance_ span resolvedValue do
    let forcedTy ← Soma.Dependent.force dictTy
    match extractClassInfo? forcedTy with
    | none => action
    | some (classId, classArgs) =>
      let instUnique ← TCM.freshUnique s!"$resolvedInst_{dictName}"
      let instInfo : InstanceInfo := {
        instanceId := instUnique
        classId := classId
        args := classArgs
        constraints := #[]
        value := resolvedValue
        span := span
      }
      let env ← TCM.getInstanceEnv
      let env' ← env.addInstanceWithIdForced instInfo
      TCM.withInstanceEnv env' action

/-- Bind an array of local instance dictionaries -/
def withLocalInstanceBindings
    (bindings : Array (Soma.Unique × String × Value))
    (span : Span := Span.uninhabited) (action : TCM α) : TCM α := do
  let rec go (idx : Nat) : TCM α := do
    if idx >= bindings.size then
      action
    else
      let (dictUnique, dictName, dictTy) := bindings[idx]!
      withLocalInstanceBinding dictName dictUnique dictTy .omega span (go (idx + 1))
  termination_by bindings.size - idx
  go 0

/-- What kind of metavariable the elaborator is creating -/
inductive MetaKind where
  | user
  | autoImplicit
  | instanceArg
  | synthetic
  | recovery
  deriving Inhabited, BEq, Repr

namespace MetaKind

def origin : MetaKind → MetaOrigin
  | .recovery => .errorRecovery
  | _ => .user

end MetaKind

/-- Policy for creating metavariables in a local context -/
structure MetaPolicy where
  kind : MetaKind := .user
  abstractLocals : Bool := false
  includeInstanceLocals : Bool := false
  includeTermLocals : Bool := true
  includeErasedProofLocals : Bool := false
  piLevel : Option Nat := none
  deriving Inhabited, Repr

/-- A freshly-created meta plus the corresponding value and core expression -/
structure FreshMeta where
  id : MetaId
  value : Value
  expr : Expr
  deriving Inhabited

/-- Create a meta according to a context policy -/
def freshMetaWithPolicy (expectedTy : Value) (policy : MetaPolicy := {})
    : TCM FreshMeta := do
  if !policy.abstractLocals then
    let mid ← TCM.freshMeta expectedTy (piLevel := policy.piLevel)
      (origin := policy.kind.origin)
    pure {
      id := mid
      value := Value.vNeutral expectedTy (.nMeta mid)
      expr := .mvar mid
    }
  else
    let ctx ← TCM.getCtx
    let locals ← ctx.locals.filterM fun entry => do
      if !policy.includeInstanceLocals && entry.binder == .instance_ then
        return false
      if !policy.includeTermLocals then
        let entryTy ← force entry.type
        match entryTy with
        | .vType _ | .vRowSort | .vLabelSort => pure ()
        | _ => return false
      if !policy.includeErasedProofLocals && entry.qty == .zero then
        let isProof ← valueInPropUniverse entry.type
        return !isProof
      return true
    let ordered := locals.reverse.toArray
    let N := ordered.size

    let mut metaTyExpr := Soma.Core.quoteExpr ⟨N⟩ expectedTy
    for revIdx in [:N] do
      let idx := N - 1 - revIdx
      let entry := ordered[idx]!
      let typeExpr := Soma.Core.quoteExpr ⟨idx⟩ entry.type
      metaTyExpr := .pi entry.qty entry.binder entry.name typeExpr metaTyExpr
    let metaTy ← TCM.evalExprInEnv Soma.Core.Env.empty metaTyExpr

    let mid ← TCM.freshMeta metaTy (piLevel := policy.piLevel)
      (origin := policy.kind.origin)
    let metaBare := Value.vNeutral metaTy (.nMeta mid)
    let value := ordered.foldl
      (init := metaBare)
      fun acc entry =>
        let argVal := Value.vNeutral entry.type (.nVar ⟨entry.name, entry.level⟩)
        Soma.Core.vAppPure acc argVal

    let mut expr : Expr := .mvar mid
    for entry in ordered do
      let entryTyExpr := Soma.Core.quoteExpr0 entry.type
      expr := .app expr (.fvar entry.fvarId entryTyExpr)

    pure { id := mid, value := value, expr := expr }

end Soma.Dependent
