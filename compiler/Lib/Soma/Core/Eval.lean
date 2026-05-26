import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Primitive
import Soma.Unique

namespace Soma.Core

/-- Global environment for looking up definitions -/
structure GlobalEnv where
  /-- Map from global names to their values -/
  defs : Std.HashMap QualifiedName Value := {}
  /-- Map from class unique IDs to their Pi-wrapped record types -/
  classRecordTypes : Std.HashMap Unique Value := {}
  /-- Map from data type unique IDs to their single constructor type -/
  recordCtorInfo : Std.HashMap Unique (Value × Array String) := {}
  /-- Map from wired-in primitive type kinds to their underlying inductive data-type unique IDs -/
  primTyToInductiveId : Std.HashMap PrimType Unique := {}
  /-- The id of the wired-in `Eq` inductive -/
  eqInductiveId : Option Unique := none
  /-- The refl constructor -/
  reflConstructor : Option (QualifiedName × Nat) := none
  deriving Inhabited

namespace GlobalEnv

def empty : GlobalEnv := {}

def insert (env : GlobalEnv) (name : QualifiedName) (v : Value) : GlobalEnv :=
  { env with defs := env.defs.insert name v }

def lookup (env : GlobalEnv) (name : QualifiedName) : Option Value :=
  env.defs.get? name

/-- Register a class's record type for pure field access resolution -/
def insertClassRecordType (env : GlobalEnv) (classId : Unique) (recordType : Value) : GlobalEnv :=
  { env with classRecordTypes := env.classRecordTypes.insert classId recordType }

/-- Look up a class record type by class unique ID -/
def lookupClassRecordType (env : GlobalEnv) (classId : Unique) : Option Value :=
  env.classRecordTypes.get? classId

/-- Register an inductive record's single-constructor info -/
def insertRecordCtorInfo (env : GlobalEnv) (typeId : Unique)
    (ctorType : Value) (fieldNames : Array String) : GlobalEnv :=
  { env with recordCtorInfo := env.recordCtorInfo.insert typeId (ctorType, fieldNames) }

/-- Look up record info by data-type unique ID -/
def lookupRecordCtorInfo (env : GlobalEnv) (typeId : Unique) : Option (Value × Array String) :=
  env.recordCtorInfo.get? typeId

/-- Register the inductive uid for a wired-in primitive type kind -/
def insertPrimTyInductive (env : GlobalEnv) (p : PrimType) (typeId : Unique) : GlobalEnv :=
  { env with primTyToInductiveId := env.primTyToInductiveId.insert p typeId }

/-- Look up the inductive uid that backs a wired-in primitive type kind -/
def lookupPrimTyInductive (env : GlobalEnv) (p : PrimType) : Option Unique :=
  env.primTyToInductiveId.get? p

/-- Return the canonical `vDataType` representation of a wired-in primitive type -/
def primTypeValue? (env : GlobalEnv) (p : PrimType) : Option Value :=
  env.lookupPrimTyInductive p |>.map fun uid => Value.vDataType uid []

end GlobalEnv

/-- Evaluation context -/
structure EvalCtx where
  /-- Local environment (De Bruijn levels to values) -/
  env : Env
  /-- Global definitions -/
  globals : GlobalEnv
  /-- Metavariable state -/
  metas : MetaState
  deriving Inhabited

namespace EvalCtx

def empty : EvalCtx := ⟨Env.empty, GlobalEnv.empty, MetaState.empty⟩

def extendEnv (ctx : EvalCtx) (name : String) (v : Value) : EvalCtx :=
  { ctx with env := ctx.env.extend name v }

end EvalCtx

/-- Field access on a record-style value -/
def vFieldAccess (v : Value) (field : String) (fieldIdx : Nat := 0) : Value :=
  match v with
  | .vRecordVal fields =>
    match fields.find? (·.1 == field) with
    | some (_, fieldVal) => fieldVal
    | none => v  -- Field not found
  | .vConstructor _ _ args _ =>
    match args.toArray[fieldIdx]? with
    | some fieldVal => fieldVal
    | none => v
  | .vNeutral ty neu => .vNeutral ty (.nFieldAccess neu field)
  | _ => v  -- Type error

/-- Helper to enumerate a list with indices -/
def listEnumerate (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (i, x) :: go (i + 1) xs
  go 0 xs

mutual

/-- Match a single Core `Pattern` against a `Value` -/
partial def matchPattern (pat : Pattern) (val : Value) : PatMatchResult :=
  match pat with
  | .wildcard => .matched #[]
  | .var none => .matched #[]
  | .var (some _) => .matched #[val]
  | .ctor _ tag fields =>
    match val with
    | .vConstructor _ vTag vArgs _ =>
      if tag != vTag then .mismatch
      else
        let vArgsArr := vArgs.toArray
        if fields.size != vArgsArr.size then .mismatch
        else matchPatternArrays fields vArgsArr
    | .vNeutral _ _ => .stuck
    | _ => .mismatch
  | .lit l =>
    match val with
    | .vIntLit n =>
      match l with
      | .int m => if n == m then .matched #[] else .mismatch
      | _ => .mismatch
    | .vStringLit s =>
      match l with
      | .string t => if s == t then .matched #[] else .mismatch
      | _ => .mismatch
    | .vFloatLit f =>
      match l with
      | .float g => if f == g then .matched #[] else .mismatch
      | _ => .mismatch
    | .vNeutral _ _ => .stuck
    | _ => .mismatch
  | .inject label argPat =>
    match val with
    | .vConstructor name _ vArgs _ =>
      if name.display != label then .mismatch
      else match argPat with
        | none => if vArgs.isEmpty then .matched #[] else .mismatch
        | some inner =>
          match vArgs with
          | arg :: _ => matchPattern inner arg
          | [] => .mismatch
    | .vNeutral _ _ => .stuck
    | _ => .mismatch

/-- Match a row of patterns against a row of values -/
partial def matchPatternArrays (pats : Array Pattern) (vals : Array Value)
    : PatMatchResult :=
  if pats.size != vals.size then .mismatch
  else matchPatternArraysGo pats vals 0 #[] false

partial def matchPatternArraysGo
    (pats : Array Pattern) (vals : Array Value)
    (i : Nat) (acc : Array Value) (stuck : Bool) : PatMatchResult :=
  if i >= pats.size then
    if stuck then .stuck else .matched acc
  else
    let pat := pats[i]!
    let val := vals[i]!
    match matchPattern pat val with
    | .matched bs => matchPatternArraysGo pats vals (i + 1) (acc ++ bs) stuck
    | .mismatch => .mismatch
    | .stuck => matchPatternArraysGo pats vals (i + 1) acc true

end

/-- Find the reducing arm for a case -/
partial def selectArm (scrutVals : Array Value) (arms : Array Arm)
    : Option (Array Value × Expr) :=
  let rec go (i : Nat) : Option (Array Value × Expr) :=
    if i >= arms.size then none
    else
      let arm := arms[i]!
      match matchPatternArrays arm.patterns scrutVals with
      | .matched bs => some (bs, arm.body)
      | .mismatch => go (i + 1)
      | .stuck => none
  go 0

mutual

/-- Evaluate a Core.Expr to a Value -/
partial def evalCoreExpr (ctx : EvalCtx) (e : Soma.Core.Expr) : Value :=
  match e with
  | .bvar idx =>
    let lvl := ctx.env.size - idx - 1
    match ctx.env.lookup ⟨lvl⟩ with
    | some v => v
    | none => .vNeutral .type0 (.nVar ⟨s!"bvar{idx}", ctx.env.level⟩)

  | .fvar id _ =>
    -- Free variables: look up by display name in environment
    match ctx.env.lookupByName id.original with
    | some v => v
    | none =>
      match ctx.globals.lookup ⟨id⟩ with
      | some v => v
      | none => .vNeutral .type0 (.nVar ⟨id.original, ctx.env.level⟩)

  | .tyvar lvl name =>
    .vNeutral .type0 (.nVar ⟨name, lvl⟩)

  | .mvar id =>
    match ctx.metas.lookup id with
    | some info =>
      match info.solution with
      | some v => v
      | none => .vNeutral .type0 (.nMeta id)
    | none => .vNeutral .type0 (.nMeta id)

  | .const name tyExpr =>
    match ctx.globals.lookup name with
    | some v => v
    | none =>
      let tyVal := evalCoreExpr ctx tyExpr
      .vNeutral tyVal (.nConst name tyVal)

  | .app fn arg =>
    let fnVal := evalCoreExpr ctx fn
    vApp fnVal (evalCoreExpr ctx arg) ctx

  | .lam _info name domain body =>
    let domainVal := evalCoreExpr ctx domain
    .vLam name domainVal (Closure.mkWithBody name ctx.env body)

  | .let_ _name _ty val body =>
    let valV := evalCoreExpr ctx val
    evalCoreExpr (ctx.extendEnv _name valV) body

  | .lit l =>
    match l with
    | .int n => .vIntLit n
    | .float f => .vFloatLit f
    | .string s => .vStringLit s

  | .sort level => .vType level

  | .pi qty _info name domain codomain =>
    let domVal := evalCoreExpr ctx domain
    .vPi qty _info name domVal (Closure.mkWithBody name ctx.env codomain)

  | .construct name tag args rty =>
    .vConstructor name tag (args.toList.map (evalCoreExpr ctx)) (evalCoreExpr ctx rty)

  | .«case» scruts motiveExpr arms =>
    let scrutVals := scruts.map (evalCoreExpr ctx)
    match selectArm scrutVals arms with
    | some (bindings, body) =>
      let ctx' := bindings.foldl (fun c v => c.extendEnv "_" v) ctx
      evalCoreExpr ctx' body
    | none =>
      let motiveVal := evalCoreExpr ctx motiveExpr
      let resultTy := scrutVals.foldl (fun m v => vApp m v ctx) motiveVal
      let hasNeutral := scrutVals.any fun
        | .vNeutral _ _ => true
        | _ => false
      if !hasNeutral then
        .vNeutral resultTy (.mk .hErrored #[])
      else
        let armClosures := arms.toList.map fun arm =>
          let binds := arm.patterns.foldl (fun acc p => acc + p.bindingCount) 0
          let patName := match arm.patterns[0]? with
            | some (Pattern.ctor qn _ _) => qn.id.original
            | some (Pattern.var (some uid)) => uid.original
            | _ => s!"pat{binds}"
          if binds == 0 then
            ArmClosure.mk patName (.const patName (evalCoreExpr ctx arm.body)) arm.patterns
          else
            ArmClosure.mk patName (Closure.mkWithBody patName ctx.env arm.body) arm.patterns
        .vNeutral resultTy (.nCase scrutVals motiveVal armClosures)

  | .record fields =>
    .vRecordVal (fields.toList.map fun (n, e) => (n, evalCoreExpr ctx e))

  | .recordUpdate base updates =>
    let baseVal := evalCoreExpr ctx base
    match baseVal with
    | .vRecordVal fields =>
      let updates' := updates.toList.map fun (n, e) => (n, evalCoreExpr ctx e)
      let merged := fields.map fun (n, v) =>
        match updates'.find? (·.1 == n) with
        | some (_, newV) => (n, newV)
        | none => (n, v)
      .vRecordVal merged
    | _ => baseVal

  | .fieldAccess e field idx =>
    vFieldAccess (evalCoreExpr ctx e) field idx

  | .inject _label _args _ =>
    -- Inject into variant: create a constructor-like value
    .vNeutral .type0 (.nVar ⟨s!"inject:{_label}", ctx.env.level⟩)

  | .rowSort => .vRowSort
  | .labelSort => .vLabelSort
  | .rowEmpty => .vRowEmpty
  | .rowExtend label fieldTy tail =>
    .vRowExtend (evalCoreExpr ctx label) (evalCoreExpr ctx fieldTy) (evalCoreExpr ctx tail)
  | .recordTy row => .vRecord (evalCoreExpr ctx row)
  | .variantTy row => .vVariant (evalCoreExpr ctx row)
  | .labelLit name => .vLabelLit name
  | .dataTy id params => .vDataType id (params.toList.map (evalCoreExpr ctx))

  | .if_ cond then_ else_ =>
    match evalCoreExpr ctx cond with
    | .vConstructor _ 0 _ _ => evalCoreExpr ctx then_
    | .vConstructor _ 1 _ _ => evalCoreExpr ctx else_
    | _ => .vNeutral .type0 (.nVar ⟨"if", ctx.env.level⟩)

  | .panic _msg =>
    .vNeutral .type0 (.mk .hErrored #[])

  | .closure name _captures _ =>
    -- Post lambda-lift closure: treated as global reference
    match ctx.globals.lookup name with
    | some v => v
    | none => .vNeutral .type0 (.nConst name .type0)

  | .array _elements _ => .vNeutral .type0 (.nVar ⟨"array", ctx.env.level⟩)
  | .tuple elements =>
    let vals := elements.toList.map (evalCoreExpr ctx)
    .vRecordVal (listEnumerate vals |>.map fun (i, v) => (s!"_{i}", v))

  | .proj _typeName _field _idx =>
    .vNeutral .type0 (.nVar ⟨s!"proj:{_field}", ctx.env.level⟩)

  | .ann expr _ty => evalCoreExpr ctx expr

/-- Apply a closure to an argument -/
partial def applyClosure (clos : Closure) (arg : Value) (ctx : EvalCtx) : Value :=
  match clos with
  | .const _ value => value
  | .term name env body =>
    let env' := env.extend name arg
    evalCoreExpr { ctx with env := env' } body

/-- Apply a value to an argument -/
partial def vApp (fn : Value) (arg : Value) (ctx : EvalCtx) : Value :=
  match fn with
  | .vLam _ _ body =>
    applyClosure body arg ctx
  | .vNeutral ty neu =>
    .vNeutral ty (.nApp neu arg)
  | .vDataType id params =>
    .vDataType id (params ++ [arg])
  | _ =>
    fn

end

/-- Apply a closure using only its captured environment (no external context needed).
    For Closure.const: returns the constant result directly.
    For Closure.term: evaluates the body with the closure's captured env extended by the argument. -/
def Closure.applyPure (clos : Closure) (arg : Value) : Value :=
  applyClosure clos arg EvalCtx.empty

partial def Value.isKind (v : Value) : Bool :=
  match v with
  | .vType _ | .vRowSort | .vLabelSort => true
  | .vPi _ _ name dom cod =>
    Value.isKind (cod.applyPure (Value.vNeutral dom (.nVar ⟨name, ⟨0⟩⟩)))
  | _ => false

/-- Evaluate an expression with no globals and no meta state, only a local environment -/
def evalExprPure (env : Env) (e : Soma.Core.Expr) : Value :=
  evalCoreExpr { env, globals := .empty, metas := .empty } e

/-- Apply a value to an argument with no global/meta context -/
def vAppPure (fn arg : Value) : Value :=
  vApp fn arg EvalCtx.empty

/-- Apply a Pi type to an argument, computing the codomain type.
    Works for both non-dependent (Closure.const) and dependent (Closure.term) Pi types. -/
def Value.piApply (v : Value) (arg : Value) : Option Value :=
  match v with
  | .vPi _ _ _ _ cod => some (cod.applyPure arg)
  | _ => none

/-- Count all Pi binders in a value type, evaluating dependent codomains as needed -/
partial def Value.arityFull (v : Value) (unfold? : Option (Value → Value) := none) : Nat :=
  match v with
  | .vPi _ _ _ dom cod =>
    match cod with
    | .const _ nextTy => 1 + Value.arityFull nextTy unfold?
    | .term name _ _ =>
      let dummyArg := Value.vNeutral dom (.nVar ⟨name, cod.env.level⟩)
      1 + Value.arityFull (cod.applyPure dummyArg) unfold?
  | other =>
    match unfold? with
    | some unfold =>
      let unfolded := unfold other
      match unfolded with
      | .vPi .. => Value.arityFull unfolded unfold?
      | _ => 0
    | none => 0

/-- Count explicit Pi binders, evaluating dependent codomains as needed -/
partial def Value.explicitArityFull (v : Value) (unfold? : Option (Value → Value) := none) : Nat :=
  match v with
  | .vPi _ binder _ dom cod =>
    let rest := match cod with
      | .const _ nextTy => Value.explicitArityFull nextTy unfold?
      | .term name _ _ =>
        let dummyArg := Value.vNeutral dom (.nVar ⟨name, cod.env.level⟩)
        Value.explicitArityFull (cod.applyPure dummyArg) unfold?
    if binder.isImplicit then rest else 1 + rest
  | other =>
    match unfold? with
    | some unfold =>
      let unfolded := unfold other
      match unfolded with
      | .vPi .. => Value.explicitArityFull unfolded unfold?
      | _ => 0
    | none => 0

/-- Evaluate a closed Core expression. -/
def evalClosed (e : Soma.Core.Expr) : Value :=
  evalCoreExpr EvalCtx.empty e

/-- Apply type arguments to a Pi-wrapped class record type, stripping one Pi per argument -/
partial def applyClassRecordType (recordType : Value) (args : List Value) : Option Value :=
  match args with
  | [] => some recordType
  | arg :: rest =>
    match recordType with
    | .vPi _ _ _ _ cod => applyClassRecordType (cod.applyPure arg) rest
    | _ => none

/-- Resolve field access on a class dictionary type -/
def resolveClassFieldType (globals : GlobalEnv) (classId : Unique) (args : List Value) (field : String) : Option Value := do
  let recordType ← globals.lookupClassRecordType classId
  let appliedTy ← applyClassRecordType recordType args
  let fields := appliedTy.recordFields
  fields.toList.find? (·.1 == field) |>.map (·.2)

/-- Walk a single-constructor type's Pi chain -/
private partial def fieldTypeFromCtorType (ctorTy : Value)
    (typeArgs : List Value) (fieldIdx : Nat) : Option Value :=
  go ctorTy typeArgs 0
where
  go (ty : Value) (remainingArgs : List Value) (explicitsSeen : Nat) : Option Value :=
    match ty with
    | .vPi _ binder name dom cod =>
      let isErasedImplicit : Bool :=
        match binder with
        | .implicit | .strictImplicit =>
          match dom with
          | .vType _ | .vRowSort | .vLabelSort => true
          | _ => false
        | _ => false
      if isErasedImplicit then
        match remainingArgs with
        | arg :: rest => go (cod.applyPure arg) rest explicitsSeen
        | [] =>
          let neutral := Value.vNeutral dom (.nVar ⟨name, ⟨0⟩⟩)
          go (cod.applyPure neutral) [] explicitsSeen
      else
        if explicitsSeen == fieldIdx then
          some dom
        else
          let neutral := Value.vNeutral dom (.nVar ⟨name, ⟨0⟩⟩)
          go (cod.applyPure neutral) remainingArgs (explicitsSeen + 1)
    | _ => none

/-- Resolve field access on an inductive record's `vDataType` value -/
def resolveRecordFieldType (globals : GlobalEnv) (typeId : Unique)
    (args : List Value) (field : String) : Option Value := do
  let (ctorTy, fieldNames) ← globals.lookupRecordCtorInfo typeId
  let fieldIdx ← fieldNames.findIdx? (· == field)
  fieldTypeFromCtorType ctorTy args fieldIdx

/-- Compute the type of a Core expression -/
partial def Expr.typeOfWith (bvarCtx : Array Value) (globals : GlobalEnv)
    (unfoldTy : Value → Value := id) (evalEnv : Env := .empty)
    (metas : MetaState) : Expr → Value
  | .ann _ ty => evalCoreExpr { env := evalEnv, globals, metas } ty

  | .fvar _ ty => evalCoreExpr { env := evalEnv, globals, metas } ty
  | .const _ ty => evalCoreExpr { env := evalEnv, globals, metas } ty

  | .bvar idx =>
    match bvarCtx[bvarCtx.size - idx - 1]? with
    | some ty => ty
    | none => panic! s!"Expr.typeOfWith: bvar({idx}) out of range (context size {bvarCtx.size})"

  | .lit (.int _) => globals.primTypeValue? .int |>.getD (.vType .zero)
  | .lit (.float _) => globals.primTypeValue? .double |>.getD (.vType .zero)
  | .lit (.string _) => globals.primTypeValue? .string |>.getD (.vType .zero)

  | .app fn arg =>
    let fnTy := typeOfWith bvarCtx globals unfoldTy evalEnv metas fn
    let argVal := evalCoreExpr { env := evalEnv, globals, metas } arg
    -- Try direct piApply, then unfold type aliases
    let applyResult := fnTy.piApply argVal |>.orElse fun _ =>
      (unfoldTy fnTy).piApply argVal
    match applyResult with
    | some codomainTy => codomainTy
    | none =>
      -- Try unfolding type abbreviations
      let unfolded := unfoldTy fnTy
      match unfolded.piApply argVal with
      | some codomainTy => codomainTy
      | none =>
        match fnTy with
        | .vType _ | .vNeutral _ _ => .vType .zero
        | _ => panic! s!"Expr.typeOfWith: app with non-Pi function type (fn={fn.ctorName}, arg={arg.ctorName})"

  | .lam _info name domain body =>
    let domTy := evalCoreExpr { env := evalEnv, globals, metas } domain
    let bodyTy := typeOfWith (bvarCtx.push domTy) globals unfoldTy evalEnv metas body
    .vPi Quantity.omega Soma.Core.BinderInfo.explicit name domTy (Closure.const name bodyTy)

  | .let_ _ ty _ body =>
    let letTy := evalCoreExpr { env := evalEnv, globals, metas } ty
    typeOfWith (bvarCtx.push letTy) globals unfoldTy evalEnv metas body

  | .if_ _ then_ _ => typeOfWith bvarCtx globals unfoldTy evalEnv metas then_

  | .«case» scruts motiveExpr _ =>
    let ctx : EvalCtx := { env := evalEnv, globals, metas }
    let motiveVal := evalCoreExpr ctx motiveExpr
    let scrutVals := scruts.map (evalCoreExpr ctx)
    scrutVals.foldl (fun m v => vApp m v ctx) motiveVal

  | .array _ resultTy => evalCoreExpr { env := evalEnv, globals, metas } resultTy

  | .construct _ _ _ resultTy => evalCoreExpr { env := evalEnv, globals, metas } resultTy

  | .inject _ _ resultTy => evalCoreExpr { env := evalEnv, globals, metas } resultTy

  | .tuple elems =>
    if elems.size = 1 then
      typeOfWith bvarCtx globals unfoldTy evalEnv metas elems[0]!
    else globals.primTypeValue? .unit |>.getD (.vType .zero)

  | .record fields =>
    let row := fields.foldr (init := Value.vRowEmpty) fun (name, expr) acc =>
      .vRowExtend (.vLabelLit name) (typeOfWith bvarCtx globals unfoldTy evalEnv metas expr) acc
    .vRecord row

  | .fieldAccess expr field _ =>
    let recTy := typeOfWith bvarCtx globals unfoldTy evalEnv metas expr
    let fields := recTy.recordFields
    match fields.toList.find? (·.1 == field) with
    | some (_, ty) => ty
    | none =>
      let unfoldedRecTy := unfoldTy recTy
      let resolved : Option Value :=
        match unfoldedRecTy with
        | .vDataType typeId args =>
          match resolveClassFieldType globals typeId args field with
          | some fieldTy => some fieldTy
          | none => resolveRecordFieldType globals typeId args field
        | _ => none
      match resolved with
      | some fieldTy => fieldTy
      | none =>
        match expr with
        | .record recFields =>
          match recFields.toList.find? (·.1 == field) with
          | some (_, fieldExpr) => typeOfWith bvarCtx globals unfoldTy evalEnv metas fieldExpr
          | none => .vType .zero
        | _ => .vType .zero

  | .closure _ _ ty => evalCoreExpr { env := evalEnv, globals, metas } ty

  | .sort _ | .pi _ _ _ _ _
  | .rowSort | .labelSort | .rowEmpty | .rowExtend _ _ _
  | .recordTy _ | .variantTy _ | .labelLit _ | .dataTy _ _
  | .proj _ _ _ | .tyvar _ _ => .vType .zero

  | .mvar _ | .recordUpdate _ _ | .panic _ => .vType .zero

/-- Compute the type of a Core expression using globals for resolving type annotations -/
partial def Expr.typeOf (e : Expr) (globals : GlobalEnv) (unfoldTy : Value → Value := id)
    (metas : MetaState) : Value :=
  Expr.typeOfWith #[] globals unfoldTy .empty metas e

end Soma.Core
