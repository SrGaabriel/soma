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

/-- Resolved names for IO primitives used during inlining -/
structure IONames where
  bindName : QualifiedName
  pureName : QualifiedName

/-- Inline IO bind chains into flat let sequences with World token threading -/
private partial def inlineIOChain (io : IONames) (worldIdx : Nat) : Expr → Expr
  | .app fn arg =>
    -- First check: is the whole expression `pure_io arg` (possibly with type args)?
    if isWiredInRef io.pureName fn then
      .pair (.bvar worldIdx) arg
    else
    match fn with
    | .app ioBind action =>
      if isWiredInRef io.bindName ioBind then
        let cont := arg
        match cont with
        | .lam _ name _domain body =>
          -- action applied to current world
          let actionCall := Expr.app action (.bvar worldIdx)
          -- let io_r = action world
          .let_ "io_r" (.primTy .unit) actionCall (
            -- let x = projSnd io_r (extract value from Pair)
            .let_ name (.primTy .unit) (.projSnd (.bvar 0)) (
              -- let __w = projFst io_r (extract new World from Pair)
              .let_ "__w" (.primTy .world) (.projFst (.bvar 1)) (
                -- Recurse: world is now at bvar 0, x is at bvar 1
                -- body originally had x at bvar 0 (from lambda)
                -- In new scope: x at bvar 1, so shift bvar 0 → bvar 1
                -- Free vars at depth ≥ 1 shift by +2 (2 extra bindings)
                let bodyShifted := body.shift 1 0 |>.shift 1 2
                inlineIOChain io 0 bodyShifted
              )))
        | _ =>
          -- Non-lambda continuation (rare): apply action to world, bind result,
          -- then apply continuation to value and new world
          let actionCall := Expr.app action (.bvar worldIdx)
          .let_ "io_r" (.primTy .unit) actionCall (
            .let_ "__val" (.primTy .unit) (.projSnd (.bvar 0)) (
              .let_ "__w" (.primTy .world) (.projFst (.bvar 1)) (
                -- cont shifted by 3 (3 new let bindings)
                let contShifted := cont.shift 3 0
                -- Apply continuation to value, then apply result to world
                .app (.app contShifted (.bvar 1)) (.bvar 0)
              )))
      else
        .app (inlineIOChain io worldIdx fn) (inlineIOChain io worldIdx arg)
    | _ =>
      if isWiredInRef io.pureName fn then
        -- pure_io x: wrap value with current world into a Pair
        .pair (.bvar worldIdx) arg
      else
        .app (inlineIOChain io worldIdx fn) (inlineIOChain io worldIdx arg)
  | .lam info name domain body =>
    .lam info name (inlineIOChain io worldIdx domain) (inlineIOChain io (worldIdx + 1) body)
  | .let_ name ty val body =>
    .let_ name (inlineIOChain io worldIdx ty) (inlineIOChain io worldIdx val)
      (inlineIOChain io (worldIdx + 1) body)
  | .closure name captures =>
    .closure name (captures.map (inlineIOChain io worldIdx))
  | .«case» scruts arms resultTy =>
    .«case» (scruts.map (inlineIOChain io worldIdx))
      (arms.map fun arm => Arm.mk arm.patterns (inlineIOChain io worldIdx arm.body))
      (inlineIOChain io worldIdx resultTy)
  | .construct name tag args resultTy =>
    .construct name tag (args.map (inlineIOChain io worldIdx)) (inlineIOChain io worldIdx resultTy)
  | .if_ c t el => .if_ (inlineIOChain io worldIdx c) (inlineIOChain io worldIdx t) (inlineIOChain io worldIdx el)
  | .pair f s => .pair (inlineIOChain io worldIdx f) (inlineIOChain io worldIdx s)
  | .projFst x => .projFst (inlineIOChain io worldIdx x)
  | .projSnd x => .projSnd (inlineIOChain io worldIdx x)
  | .record fields => .record (fields.map fun (n, x) => (n, inlineIOChain io worldIdx x))
  | .recordUpdate base updates =>
    .recordUpdate (inlineIOChain io worldIdx base) (updates.map fun (n, x) => (n, inlineIOChain io worldIdx x))
  | .tuple elems => .tuple (elems.map (inlineIOChain io worldIdx))
  | .array elems resultTy => .array (elems.map (inlineIOChain io worldIdx)) (inlineIOChain io worldIdx resultTy)
  | .inject label args resultTy => .inject label (args.map (inlineIOChain io worldIdx)) (inlineIOChain io worldIdx resultTy)
  | .fieldAccess expr field idx => .fieldAccess (inlineIOChain io worldIdx expr) field idx
  | .ann expr ty => .ann (inlineIOChain io worldIdx expr) (inlineIOChain io worldIdx ty)
  | .pi qty info name domain codomain =>
    .pi qty info name (inlineIOChain io worldIdx domain) (inlineIOChain io worldIdx codomain)
  | .sigma qty info name fst snd =>
    .sigma qty info name (inlineIOChain io worldIdx fst) (inlineIOChain io worldIdx snd)
  | e => e

/-- Core IO bind inlining with optional world parameter index from an enclosing World lambda -/
private partial def inlineIOBindsCore (io : IONames) (worldVar? : Option Nat) (body : Expr) : Expr :=
  match body with
  | .app fn arg =>
    if isWiredInRef io.pureName fn then
      match worldVar? with
      | some worldIdx => .pair (.bvar worldIdx) arg
      | none => .lam .explicit "w" (.primTy .world) (.pair (.bvar 0) arg.shiftUp)
    else
    match fn with
    | .app ioBind _action =>
      if isWiredInRef io.bindName ioBind then
        match worldVar? with
        | some worldIdx =>
          -- World parameter already in scope so we inline directly without extra lambda
          inlineIOChain io worldIdx body
        | none =>
          -- No world parameter so we wrap in a lambda to introduce one
          .lam .explicit "w" (.primTy .world) (inlineIOChain io 0 body.shiftUp)
      else
        .app (inlineIOBindsCore io worldVar? fn) (inlineIOBindsCore io worldVar? arg)
    | _ =>
      if isWiredInRef io.pureName fn then
        match worldVar? with
        | some worldIdx =>
          -- World parameter already in scope so we construct pair directly
          .pair (.bvar worldIdx) arg
        | none =>
          .lam .explicit "w" (.primTy .world) (.pair (.bvar 0) arg.shiftUp)
      else
        .app (inlineIOBindsCore io worldVar? fn) (inlineIOBindsCore io worldVar? arg)
  | .lam info name domain innerBody =>
    -- If this lambda takes a World parameter, we record its index for IO inlining
    let isWorldLam := match domain with
      | .primTy .world => true
      | _ => false
    if isWorldLam then
      .lam info name domain (inlineIOBindsCore io (some 0) innerBody)
    else
      .lam info name domain (inlineIOBindsCore io (worldVar?.map (· + 1)) innerBody)
  | .let_ name ty val innerBody =>
    .let_ name ty (inlineIOBindsCore io worldVar? val)
      (inlineIOBindsCore io (worldVar?.map (· + 1)) innerBody)
  | _ => body

/-- Top-level IO bind inlining -/
partial def inlineIOBinds (io : IONames) (body : Expr) : Expr :=
  inlineIOBindsCore io none body

/-- Resolve IO primitive names from the global declarations -/
def resolveIONames? (globals : Globals) : Option IONames := Id.run do
  let mut bindName? : Option QualifiedName := none
  let mut pureName? : Option QualifiedName := none
  for (_, info) in globals.allDecls do
    if info.name.id.original == "pure_io" then pureName? := some info.name
    if info.name.id.original == "io_bind" then bindName? := some info.name
  match bindName?, pureName? with
  | some bindName, some pureName => return some { bindName, pureName }
  | _, _ => return none

/-- Inline IO binds in a TypedFunction body using pre-resolved IO names -/
def inlineIOBindsFunction (ioNames? : Option IONames)
    (fn : Soma.Core.TypedFunction) : Soma.Core.TypedFunction :=
  match ioNames? with
  | some io => { fn with body := inlineIOBinds io fn.body }
  | none => fn

end Soma.Dependent.Specialize
