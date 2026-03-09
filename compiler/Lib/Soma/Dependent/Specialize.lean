import Soma.Core.Expr
import Soma.Core.Value
import Soma.Core.Quote
import Soma.Dependent.Monad

namespace Soma.Dependent.Specialize

open Soma.Core (Expr QualifiedName Value Closure Level Quantity Arm Pattern)
open Soma (Unique)

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

/-- Check if an expression is type-level (will be erased at runtime) -/
private def isTypeLevelExpr : Expr → Bool
  | .sort _ | .pi _ _ _ _ _ | .sigma _ _ _ _ _ | .primTy _
  | .rowSort | .labelSort | .rowEmpty | .rowExtend _ _ _
  | .recordTy _ | .variantTy _ | .labelLit _ | .dataTy _ _
  | .eqTy _ _ _ _ | .refl _ _ | .transport _ _ _ _ _ _ _
  | .mvar _ => true
  | _ => false

/-- Check if a const references a known IO intrinsic by original name -/
private def isIOIntrinsicName (name : String) : Bool :=
  name == "io_bind" || name == "pure_io"

/-- Check if an expression references IO intrinsics (io_bind, pure_io) -/
private partial def referencesIOIntrinsic : Expr → Bool
  | .const qn _ => isIOIntrinsicName qn.id.original
  | .app fn arg => referencesIOIntrinsic fn || referencesIOIntrinsic arg
  | .lam _ _ domain body => referencesIOIntrinsic domain || referencesIOIntrinsic body
  | .let_ _ ty val body =>
    referencesIOIntrinsic ty || referencesIOIntrinsic val || referencesIOIntrinsic body
  | .record fields => fields.any fun (_, e) => referencesIOIntrinsic e
  | .closure _ captures => captures.any referencesIOIntrinsic
  | .«case» scruts arms _ =>
    scruts.any referencesIOIntrinsic || arms.any fun arm => referencesIOIntrinsic arm.body
  | .construct _ _ args _ => args.any referencesIOIntrinsic
  | .fieldAccess e _ _ => referencesIOIntrinsic e
  | _ => false


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

/-- Collect application spine -/
private def collectAppSpine (e : Expr) : Expr × Array Expr :=
  go e #[]
where
  go (e : Expr) (args : Array Expr) : Expr × Array Expr :=
    match e with
    | .app fn arg => go fn (#[arg] ++ args)
    | _ => (e, args)

/-- Rebuild an application spine -/
private def rebuildAppSpine (fn : Expr) (args : Array Expr) : Expr :=
  args.foldl (init := fn) fun acc arg => .app acc arg

/-- Find the index of the first non-type-level argument -/
private def findDictArgIdx (args : Array Expr) : Option Nat :=
  args.findIdx? (!isTypeLevelExpr ·)

/-- Exhaustive beta-reduction -/
private partial def betaReduce (e : Expr) : Expr :=
  match e with
  | .app fn arg =>
    let fn' := betaReduce fn
    let arg' := betaReduce arg
    match fn' with
    | .lam _ _ _ body => betaReduce (body.instantiate arg')
    | _ =>
      -- Strip type-level arguments (mvar, primTy, dataTy) that remain
      if isTypeLevelExpr arg' then fn'
      else .app fn' arg'
  | .lam info name domain body =>
    .lam info name (betaReduce domain) (betaReduce body)
  | .let_ name ty val body =>
    .let_ name (betaReduce ty) (betaReduce val) (betaReduce body)
  | .pi qty info name domain codomain =>
    .pi qty info name (betaReduce domain) (betaReduce codomain)
  | .sigma qty info name fst snd =>
    .sigma qty info name (betaReduce fst) (betaReduce snd)
  | .pair fst snd => .pair (betaReduce fst) (betaReduce snd)
  | .projFst x => .projFst (betaReduce x)
  | .projSnd x => .projSnd (betaReduce x)
  | .if_ c t el => .if_ (betaReduce c) (betaReduce t) (betaReduce el)
  | .«case» scruts arms resultTy =>
    .«case» (scruts.map betaReduce)
      (arms.map fun arm => Arm.mk arm.patterns (betaReduce arm.body))
      (betaReduce resultTy)
  | .construct name tag args resultTy =>
    .construct name tag (args.map betaReduce) (betaReduce resultTy)
  | .fieldAccess expr field idx => .fieldAccess (betaReduce expr) field idx
  | .record fields => .record (fields.map fun (n, x) => (n, betaReduce x))
  | .recordUpdate base updates =>
    .recordUpdate (betaReduce base) (updates.map fun (n, x) => (n, betaReduce x))
  | .tuple elems => .tuple (elems.map betaReduce)
  | .array elems resultTy => .array (elems.map betaReduce) (betaReduce resultTy)
  | .inject label args resultTy => .inject label (args.map betaReduce) (betaReduce resultTy)
  | .closure name captures => .closure name (captures.map betaReduce)
  | .ann expr ty => .ann (betaReduce expr) (betaReduce ty)
  | _ => e


/-- Debug printer for Expr -/
partial def debugExpr : Expr → String
  | .bvar idx => s!"bvar({idx})"
  | .fvar name _ => s!"fvar({name.display})"
  | .mvar _ => "mvar"
  | .const qn _ => s!"const({qn.display})"
  | .app fn arg => s!"app({debugExpr fn}, {debugExpr arg})"
  | .lam _ name _ body => s!"λ{name}.{debugExpr body}"
  | .let_ name _ val body => s!"let {name}={debugExpr val} in {debugExpr body}"
  | .lit l => s!"lit({l})"
  | .sort _ => "sort"
  | .pi _ _ _ _ _ => "pi"
  | .sigma _ _ _ _ _ => "sigma"
  | .pair a b => s!"pair({debugExpr a},{debugExpr b})"
  | .projFst e => s!"fst({debugExpr e})"
  | .projSnd e => s!"snd({debugExpr e})"
  | .construct n _ _ _ => s!"ctor({n.display})"
  | .case _ _ _ => "case"
  | .record fields => s!"\{{String.intercalate ", " (fields.toList.map fun (n,e) => s!"{n}={debugExpr e}")}}"
  | .recordUpdate _ _ => "recordUpdate"
  | .fieldAccess e f idx => s!"fieldAccess({debugExpr e}, {f}, {idx})"
  | .inject _ _ _ => "inject"
  | .primTy p => s!"primTy({p})"
  | .rowSort => "rowSort"
  | .labelSort => "labelSort"
  | .rowEmpty => "rowEmpty"
  | .rowExtend _ _ _ => "rowExtend"
  | .recordTy _ => "recordTy"
  | .variantTy _ => "variantTy"
  | .labelLit s => s!"label({s})"
  | .dataTy n _ => s!"dataTy({n.display})"
  | .eqTy _ _ _ _ => "eqTy"
  | .refl _ _ => "refl"
  | .transport _ _ _ _ _ _ _ => "transport"
  | .if_ _ _ _ => "if"
  | .panic _ => "panic"
  | .closure n caps => s!"closure({n.display}, [{String.intercalate ", " (caps.toList.map debugExpr)}])"
  | .array _ _ => "array"
  | .tuple _ => "tuple"
  | .proj _ _ _ => "proj"
  | .ann e _ => debugExpr e

mutual

/-- Core specialization: transform a single expression node -/
private partial def specializeExpr (registry : ClassMethodRegistry) (e : Expr) : Expr :=
  let (head, args) := collectAppSpine e
  match head with
  | .const qn _ =>
    match registry.get? qn with
    | some info =>
      match findDictArgIdx args with
      | some idx =>
        -- Specialize the dict and remaining args, but not the spine itself
        let dictExpr := specializeExpr registry args[idx]!
        let implOpt := inlineFieldAccess dictExpr info.methodName info.fieldIdx
        -- Check if the inlined implementation references IO intrinsics
        let isIOMethod := match implOpt with
          | some impl => referencesIOIntrinsic impl
          | none => false
        if isIOMethod then
          -- Skip specialization for IO methods — recurse normally
          rebuildAppSpine (specializeChildren registry head) (args.map (specializeExpr registry))
        else
          let specialized := match implOpt with
            | some impl => specializeExpr registry impl
            | none => Expr.fieldAccess dictExpr info.methodName info.fieldIdx
          -- Keep only non-type-level args after the dict, recursively specialized
          let remainingArgs := (args.extract (idx + 1) args.size)
            |>.filter (!isTypeLevelExpr ·)
            |>.map (specializeExpr registry)
          rebuildAppSpine specialized remainingArgs
      | none =>
        rebuildAppSpine head (args.map (specializeExpr registry))
    | none =>
      rebuildAppSpine (specializeChildren registry head) (args.map (specializeExpr registry))
  | _ =>
    if args.isEmpty then
      specializeChildren registry e
    else
      rebuildAppSpine (specializeExpr registry head) (args.map (specializeExpr registry))

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
  else { fn with body := betaReduce (specializeExpr registry fn.body) }

end Soma.Dependent.Specialize
