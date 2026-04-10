import Soma.Core.Expr
import Soma.Core.Value
import Soma.Core.Quote
import Soma.Dependent.Monad

namespace Soma.Dependent.Specialize

open Soma.Core (Expr QualifiedName Value Closure Level Quantity Arm Pattern)
open Soma (Unique)
open Soma.Core (Intrinsic FFIOp)

/-- Info about a class method needed for specialization -/
structure ClassMethodInfo where
  /-- The method's display name -/
  methodName : String
  /-- Field index in the class record -/
  fieldIdx : Nat
  /-- The class unique this method belongs to -/
  classId : Unique
  deriving Inhabited

/-- Registry mapping class method QualifiedNames to their specialization info -/
abbrev ClassMethodRegistry := Std.HashMap QualifiedName ClassMethodInfo

/-- Peel off Pi binders to find the underlying type -/
private partial def peelPi : Value → Value
  | .vPi _ _ _ _ cod => peelPi (cod.applyPure (.vType .zero))
  | v => v

/-- Extract row field names in order -/
private partial def extractRowFields (row : Value) (idx : Nat) : Array (String × Nat) :=
  match row with
  | .vRowExtend (.vLabelLit name) _ rest =>
    #[(name, idx)] ++ extractRowFields rest (idx + 1)
  | _ => #[]

/-- Extract method field names and indices from a class record type -/
private def extractMethodFields (recordType : Value) : Array (String × Nat) :=
  let innerTy := peelPi recordType
  match innerTy with
  | .vRecord row => extractRowFields row 0
  | _ => #[]

/-- Build a ClassMethodRegistry from the instance environment and globals -/
def buildClassMethodRegistry (globals : Globals) (instanceEnv : InstanceEnv)
    : ClassMethodRegistry := Id.run do
  let mut registry : ClassMethodRegistry := {}
  for (_, info) in globals.allDecls do
    if info.origin == .traitMethod then
      let methodName := info.name.id.original
      for (classId, classInfo) in instanceEnv.classes.toList do
        let fields := extractMethodFields classInfo.recordType
        for (fieldName, fieldIdx) in fields do
          if fieldName == methodName then
            registry := registry.insert info.name {
              methodName := methodName
              fieldIdx := fieldIdx
              classId := classId
            }
  return registry


/-- Try to inline a field access on a known record literal -/
private def inlineFieldAccess (dictExpr : Expr) (methodName : String) (fieldIdx : Nat)
    : Option Expr :=
  match dictExpr with
  | .record fields =>
    match fields.find? (fun (name, _) => name == methodName) with
    | some (_, impl) => some impl
    | none =>
      if h : fieldIdx < fields.size then
        some fields[fieldIdx].2
      else
        none
  | _ => none


/-- Find the index of the dictionary argument in a class method application spine -/
private def findDictArgIdx (args : Array Expr) : Option Nat :=
  args.findIdx? fun
    | .record _ => true
    | _ => false


mutual

/-- Core specialization: transform a single expression node -/
private partial def specializeExpr (registry : ClassMethodRegistry) (e : Expr) : Expr :=
  let (head, args) := e.collectAppSpine
  match head with
  | .const qn _ =>
    match registry.get? qn with
    | some info =>
      match findDictArgIdx args with
      | some idx =>
        -- Specialize the dict and remaining args, but not the spine itself
        let dictExpr := specializeExpr registry args[idx]!
        let implOpt := inlineFieldAccess dictExpr info.methodName info.fieldIdx
        let specialized := match implOpt with
          | some impl => specializeExpr registry impl
          | none => Expr.fieldAccess dictExpr info.methodName info.fieldIdx
          -- Keep only non-type-level args after the dict, recursively specialized
          let remainingArgs := (args.extract (idx + 1) args.size)
            |>.filter (!·.isTypeLevelExpr)
            |>.map (specializeExpr registry)
          Expr.rebuildAppSpine specialized remainingArgs
      | none =>
        Expr.rebuildAppSpine head (args.map (specializeExpr registry))
    | none =>
      Expr.rebuildAppSpine (specializeChildren registry head) (args.map (specializeExpr registry))
  | _ =>
    if args.isEmpty then
      specializeChildren registry e
    else
      Expr.rebuildAppSpine (specializeExpr registry head) (args.map (specializeExpr registry))

/-- Recursively specialize non-application children of an expression -/
private partial def specializeChildren (registry : ClassMethodRegistry) (e : Expr) : Expr :=
  match e with
  | .app fn arg => .app (specializeExpr registry fn) (specializeExpr registry arg)
  | .lam info name domain body =>
    .lam info name (specializeExpr registry domain) (specializeExpr registry body)
  | .let_ name ty val body =>
    .let_ name (specializeExpr registry ty) (specializeExpr registry val)
      (specializeExpr registry body)
  | .pi qty info name domain codomain =>
    .pi qty info name (specializeExpr registry domain) (specializeExpr registry codomain)
  | .sigma qty info name fst snd =>
    .sigma qty info name (specializeExpr registry fst) (specializeExpr registry snd)
  | .pair fst snd => .pair (specializeExpr registry fst) (specializeExpr registry snd)
  | .projFst e => .projFst (specializeExpr registry e)
  | .projSnd e => .projSnd (specializeExpr registry e)
  | .if_ c t e => .if_ (specializeExpr registry c) (specializeExpr registry t)
    (specializeExpr registry e)
  | .«case» scruts arms resultTy =>
    .«case» (scruts.map (specializeExpr registry))
      (arms.map fun arm => Arm.mk arm.patterns (specializeExpr registry arm.body))
      (specializeExpr registry resultTy)
  | .construct name tag args resultTy =>
    .construct name tag (args.map (specializeExpr registry)) (specializeExpr registry resultTy)
  | .fieldAccess expr field idx =>
    .fieldAccess (specializeExpr registry expr) field idx
  | .record _ =>
    -- Do NOT recurse into record literals. These are typically type class
    -- dictionaries, and their fields may contain self-referential method calls
    -- (e.g., >> defined in terms of >>=) where the dict context is not in scope.
    e
  | .recordUpdate base updates =>
    .recordUpdate (specializeExpr registry base)
      (updates.map fun (name, expr) => (name, specializeExpr registry expr))
  | .tuple elems => .tuple (elems.map (specializeExpr registry))
  | .array elems resultTy =>
    .array (elems.map (specializeExpr registry)) (specializeExpr registry resultTy)
  | .inject label args resultTy =>
    .inject label (args.map (specializeExpr registry)) (specializeExpr registry resultTy)
  | .closure name captures =>
    .closure name (captures.map (specializeExpr registry))
  | .ann expr ty => .ann (specializeExpr registry expr) (specializeExpr registry ty)
  | .bvar _ | .fvar _ _ | .mvar _ | .const _ _ | .lit _ | .sort _
  | .primTy _ | .rowSort | .labelSort | .rowEmpty | .rowExtend _ _ _
  | .recordTy _ | .variantTy _ | .labelLit _ | .dataTy _ _
  | .eqTy _ _ _ _ | .refl _ _ | .transport _ _ _ _ _ _ _
  | .proj _ _ _ | .panic _ => e

end

/-- Specialize all class method calls in a TypedFunction body -/
def specializeFunction (registry : ClassMethodRegistry) (fn : Soma.Core.TypedFunction)
    : Soma.Core.TypedFunction :=
  if registry.isEmpty then fn
  else
    let specialized := specializeExpr registry fn.body
    let reduced := specialized.betaReduce
    { fn with body := reduced }

/-- Check if the head of an expression refers to a specific wired-in QualifiedName -/
private partial def isWiredInRef (qn : QualifiedName) : Expr → Bool
  | .const qn' _ => qn' == qn
  | .app fn arg => arg.isTypeLevelExpr && isWiredInRef qn fn
  | _ => false

end Soma.Dependent.Specialize
