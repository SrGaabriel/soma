import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Primitive
import Soma.Unique

namespace Soma.Core

/-! ## Evaluation Context -/

/-- Global environment for looking up definitions -/
structure GlobalEnv where
  /-- Map from global names to their values -/
  defs : Std.HashMap QualifiedName Value := {}
  deriving Inhabited

namespace GlobalEnv

def empty : GlobalEnv := ⟨{}⟩

def insert (env : GlobalEnv) (name : QualifiedName) (v : Value) : GlobalEnv :=
  ⟨env.defs.insert name v⟩

def lookup (env : GlobalEnv) (name : QualifiedName) : Option Value :=
  env.defs.get? name

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

def withEnv (ctx : EvalCtx) (env : Env) : EvalCtx :=
  { ctx with env := env }

def extendEnv (ctx : EvalCtx) (name : String) (v : Value) : EvalCtx :=
  { ctx with env := ctx.env.extend name v }

/-- Create a fresh variable at the current level -/
def freshVar (ctx : EvalCtx) (name : String) : Value :=
  let lvl := ctx.env.level
  let bv : BoundVar := ⟨name, lvl⟩
  -- The type is unknown, use a placeholder
  .vNeutral .type0 (.nVar bv)

end EvalCtx

/-! ## Projections -/

/-- First projection -/
def vFst (v : Value) : Value :=
  match v with
  | .vPair fst _ => fst
  | .vNeutral ty neu => .vNeutral ty (.nFst neu)
  | _ => v  -- Type error

/-- Second projection -/
def vSnd (v : Value) : Value :=
  match v with
  | .vPair _ snd => snd
  | .vNeutral ty neu => .vNeutral ty (.nSnd neu)
  | _ => v  -- Type error

/-- Field access on a record -/
def vFieldAccess (v : Value) (field : String) : Value :=
  match v with
  | .vRecordVal fields =>
    match fields.find? (·.1 == field) with
    | some (_, fieldVal) => fieldVal
    | none => v  -- Field not found
  | .vNeutral ty neu => .vNeutral ty (.nFieldAccess neu field)
  | _ => v  -- Type error

/-- Convert a De Bruijn index to a level -/
def indexToLevel (ctx : EvalCtx) (idx : Nat) : DeBruijnLvl :=
  ⟨ctx.env.size - idx - 1⟩

/-- Helper to enumerate a list with indices -/
def listEnumerate (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (i, x) :: go (i + 1) xs
  go 0 xs

/-- Check if an arm matches a given constructor tag -/
private def matchArmTag (arm : Arm) (tag : Nat) : Bool :=
  let pat : Option Pattern := arm.patterns[0]?
  match pat with
  | some (Pattern.ctor _ t _) => t == tag
  | some Pattern.wildcard => true
  | some (Pattern.var _) => true
  | _ => false

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

  | .mvar id =>
    match ctx.metas.lookup id with
    | some info =>
      match info.solution with
      | some v => v
      | none => .vNeutral .type0 (.nMeta id)
    | none => .vNeutral .type0 (.nMeta id)

  | .const name _ =>
    match ctx.globals.lookup name with
    | some v => v
    | none => .vNeutral .type0 (.nVar ⟨name.display, ⟨0⟩⟩)

  | .app fn arg =>
    let fnVal := evalCoreExpr ctx fn
    vApp fnVal (evalCoreExpr ctx arg) ctx

  | .lam _info name _domain body =>
    .vLam name (Closure.mkWithBody name ctx.env body)

  | .let_ _name _ty val body =>
    let valV := evalCoreExpr ctx val
    evalCoreExpr (ctx.extendEnv _name valV) body

  | .lit l =>
    match l with
    | .int n => .vIntLit n
    | .string s => .vStringLit s
    | .bool true => .vConstructor ⟨⟨0, "", "True"⟩⟩ 0 [] (.vPrimTy .bool)
    | .bool false => .vConstructor ⟨⟨0, "", "False"⟩⟩ 1 [] (.vPrimTy .bool)

  | .sort level => .vType level

  | .pi qty _info name domain codomain =>
    let domVal := evalCoreExpr ctx domain
    .vPi qty _info name domVal (Closure.mkWithBody name ctx.env codomain)

  | .sigma qty _info name fst snd =>
    let fstVal := evalCoreExpr ctx fst
    .vSigma qty name fstVal (Closure.mkWithBody name ctx.env snd)

  | .pair fst snd => .vPair (evalCoreExpr ctx fst) (evalCoreExpr ctx snd)
  | .projFst e => vFst (evalCoreExpr ctx e)
  | .projSnd e => vSnd (evalCoreExpr ctx e)

  | .construct name tag args rty =>
    .vConstructor name tag (args.toList.map (evalCoreExpr ctx)) (evalCoreExpr ctx rty)

  | .«case» scruts arms _ =>
    -- Simplified: evaluate first scrutinee
    match scruts[0]? with
    | some scrut =>
      let scrutVal := evalCoreExpr ctx scrut
      match scrutVal with
      | .vConstructor _ tag ctorArgs _ =>
        -- Find matching arm by trying each arm's patterns
        match arms.toList.find? (fun arm => matchArmTag arm tag) with
        | some arm =>
          let ctx' := ctorArgs.foldl (fun c arg => c.extendEnv "_" arg) ctx
          evalCoreExpr ctx' arm.body
        | none => .vNeutral .type0 (.nVar ⟨"case", ctx.env.level⟩)
      | _ => .vNeutral .type0 (.nVar ⟨"case", ctx.env.level⟩)
    | none => .vNeutral .type0 (.nVar ⟨"case", ctx.env.level⟩)

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

  | .fieldAccess e field _idx =>
    vFieldAccess (evalCoreExpr ctx e) field

  | .inject _label _args _ =>
    -- Inject into variant: create a constructor-like value
    .vNeutral .type0 (.nVar ⟨s!"inject:{_label}", ctx.env.level⟩)

  | .primTy p => .vPrimTy p
  | .rowSort => .vRowSort
  | .labelSort => .vLabelSort
  | .rowEmpty => .vRowEmpty
  | .rowExtend label fieldTy tail =>
    .vRowExtend (evalCoreExpr ctx label) (evalCoreExpr ctx fieldTy) (evalCoreExpr ctx tail)
  | .recordTy row => .vRecord (evalCoreExpr ctx row)
  | .variantTy row => .vVariant (evalCoreExpr ctx row)
  | .labelLit name => .vLabelLit name
  | .dataTy id params => .vDataType id (params.toList.map (evalCoreExpr ctx))

  | .eqTy tyLevel ty lhs rhs =>
    .vEq tyLevel (evalCoreExpr ctx ty) (evalCoreExpr ctx lhs) (evalCoreExpr ctx rhs)
  | .refl ty x => .vRefl (evalCoreExpr ctx ty) (evalCoreExpr ctx x)
  | .transport tyLevel ty motive lhs rhs eq body =>
    let eqVal := evalCoreExpr ctx eq
    match eqVal with
    | .vRefl _ _ => evalCoreExpr ctx body
    | _ =>
      .vTransport tyLevel (evalCoreExpr ctx ty) (evalCoreExpr ctx motive)
                  (evalCoreExpr ctx lhs) (evalCoreExpr ctx rhs)
                  eqVal (evalCoreExpr ctx body)

  | .if_ cond then_ else_ =>
    match evalCoreExpr ctx cond with
    | .vConstructor _ 0 _ _ => evalCoreExpr ctx then_
    | .vConstructor _ 1 _ _ => evalCoreExpr ctx else_
    | _ => .vNeutral .type0 (.nVar ⟨"if", ctx.env.level⟩)

  | .panic msg => .vNeutral .type0 (.nVar ⟨s!"panic: {msg}", ctx.env.level⟩)

  | .closure name _captures =>
    -- Post lambda-lift closure: treated as global reference
    match ctx.globals.lookup name with
    | some v => v
    | none => .vNeutral .type0 (.nVar ⟨name.display, ⟨0⟩⟩)

  | .array _elements _ => .vNeutral .type0 (.nVar ⟨"array", ctx.env.level⟩)
  | .tuple elements =>
    let vals := elements.toList.map (evalCoreExpr ctx)
    match vals with
    | [a, b] => .vPair a b
    | _ => .vRecordVal (listEnumerate vals |>.map fun (i, v) => (s!"_{i}", v))

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
  | .vLam _ body =>
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

/-- Apply a Pi type to an argument, computing the codomain type.
    Works for both non-dependent (Closure.const) and dependent (Closure.term) Pi types. -/
def Value.piApply (v : Value) (arg : Value) : Option Value :=
  match v with
  | .vPi _ _ _ _ cod => some (cod.applyPure arg)
  | _ => none

/-- Count all Pi binders in a value type, evaluating dependent codomains as needed -/
partial def Value.arityFull (v : Value) : Nat :=
  match v with
  | .vPi _ _ _ dom cod =>
    match cod with
    | .const _ nextTy => 1 + Value.arityFull nextTy
    | .term name _ _ =>
      let dummyArg := Value.vNeutral dom (.nVar ⟨name, cod.env.level⟩)
      1 + Value.arityFull (cod.applyPure dummyArg)
  | _ => 0

/-- Count explicit Pi binders, evaluating dependent codomains as needed -/
partial def Value.explicitArityFull (v : Value) : Nat :=
  match v with
  | .vPi _ binder _ dom cod =>
    let rest := match cod with
      | .const _ nextTy => Value.explicitArityFull nextTy
      | .term name _ _ =>
        let dummyArg := Value.vNeutral dom (.nVar ⟨name, cod.env.level⟩)
        Value.explicitArityFull (cod.applyPure dummyArg)
    if binder.isImplicit then rest else 1 + rest
  | _ => 0

/-- Apply a Sigma type to a first-component value, computing the second-component type -/
def Value.sigmaApply (v : Value) (arg : Value) : Option Value :=
  match v with
  | .vSigma _ _ _ clos => some (clos.applyPure arg)
  | _ => none

/-- Extract the second component type from a Sigma type (non-dependent shortcut) -/
def Value.sigmaSnd? (v : Value) : Option Value :=
  match v with
  | .vSigma _ _ _ clos => some (clos.applyPure (.vPrimTy .unit))
  | _ => none

/-- Evaluate a closed Core expression. -/
def evalClosed (e : Soma.Core.Expr) : Value :=
  evalCoreExpr EvalCtx.empty e

/-- Evaluate a Core expression with a global environment. -/
def evalWithGlobals (globals : GlobalEnv) (e : Soma.Core.Expr) : Value :=
  evalCoreExpr { EvalCtx.empty with globals := globals } e

/-- Compute the type of a Core expression purely from its structure -/
partial def Expr.typeOfWith (bvarCtx : Array Value) : Expr → Value
  | .ann _ ty => evalClosed ty

  | .fvar _ ty => evalClosed ty
  | .const _ ty => evalClosed ty

  | .bvar idx =>
    match bvarCtx[bvarCtx.size - idx - 1]? with
    | some ty => ty
    | none => panic! s!"Expr.typeOfWith: bvar({idx}) out of range (context size {bvarCtx.size})"

  | .lit (.int _) => .vPrimTy .int
  | .lit (.string _) => .vPrimTy .string
  | .lit (.bool _) => .vPrimTy .bool

  | .app fn arg =>
    let fnTy := typeOfWith bvarCtx fn
    let argVal := evalClosed arg
    match fnTy.piApply argVal with
    | some codomainTy => codomainTy
    | none => panic! s!"Expr.typeOfWith: app with non-Pi function type (fn={fn.ctorName})"

  | .lam _info name domain body =>
    let domTy := evalClosed domain
    let bodyTy := typeOfWith (bvarCtx.push domTy) body
    .vPi Quantity.omega Soma.Core.BinderInfo.explicit name domTy (Closure.const name bodyTy)

  | .let_ _ ty _ body =>
    let letTy := evalClosed ty
    typeOfWith (bvarCtx.push letTy) body

  | .if_ _ then_ _ => typeOfWith bvarCtx then_

  | .«case» _ _ resultTy => evalClosed resultTy

  | .array _ resultTy => evalClosed resultTy

  | .construct _ _ _ resultTy => evalClosed resultTy

  | .inject _ _ resultTy => evalClosed resultTy

  | .pair fst snd =>
    let fstTy := typeOfWith bvarCtx fst
    let sndTy := typeOfWith bvarCtx snd
    Value.prod fstTy sndTy

  | .tuple elems =>
    if elems.size ≥ 2 then
      let fstTy := typeOfWith bvarCtx elems[0]!
      let sndTy := typeOfWith bvarCtx elems[1]!
      Value.prod fstTy sndTy
    else if elems.size = 1 then
      typeOfWith bvarCtx elems[0]!
    else .vPrimTy .unit

  | .projFst expr =>
    let sigTy := typeOfWith bvarCtx expr
    match sigTy.sigmaFst? with
    | some ty => ty
    | none => panic! s!"Expr.typeOfWith: projFst on non-Sigma type (expr={expr.ctorName})"
  | .projSnd expr =>
    let sigTy := typeOfWith bvarCtx expr
    let fstVal := evalClosed (.projFst expr)
    match sigTy.sigmaApply fstVal with
    | some ty => ty
    | none => panic! s!"Expr.typeOfWith: projSnd on non-Sigma type (expr={expr.ctorName})"

  | .record fields =>
    let row := fields.foldr (init := Value.vRowEmpty) fun (name, expr) acc =>
      .vRowExtend (.vLabelLit name) (typeOfWith bvarCtx expr) acc
    .vRecord row

  | .fieldAccess expr field _ =>
    let recTy := typeOfWith bvarCtx expr
    let fields := recTy.recordFields
    match fields.toList.find? (·.1 == field) with
    | some (_, ty) => ty
    | none =>
      -- For instance dicts, get field type from the record expression
      match expr with
      | .record recFields =>
        match recFields.toList.find? (·.1 == field) with
        | some (_, fieldExpr) => typeOfWith bvarCtx fieldExpr
        | none => panic! s!"Expr.typeOfWith: field '{field}' not found in record literal"
      | _ => panic! s!"Expr.typeOfWith: field '{field}' not found in record type (expr={expr.ctorName})"

  | .closure _name _captures => .vType .zero

  | .sort _ | .pi _ _ _ _ _ | .sigma _ _ _ _ _ | .primTy _
  | .rowSort | .labelSort | .rowEmpty | .rowExtend _ _ _
  | .recordTy _ | .variantTy _ | .labelLit _ | .dataTy _ _
  | .eqTy _ _ _ _ | .refl _ _ | .transport _ _ _ _ _ _ _
  | .proj _ _ _ => .vType .zero

  | .mvar _ | .recordUpdate _ _ | .panic _ => .vType .zero

/-- Compute the type of a Core expression purely from its structure -/
partial def Expr.typeOf (e : Expr) : Value :=
  Expr.typeOfWith #[] e

end Soma.Core
