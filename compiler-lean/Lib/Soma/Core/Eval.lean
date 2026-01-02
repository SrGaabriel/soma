import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Primitive
import Soma.Core.TypeId
import Soma.Core.Name
import Soma.Metal.Expr

namespace Soma.Core

open Soma.Metal (Expr ExprList Scope BinderInfo HoleId)
open Soma.Syntax (Span)

-- Inhabited instance for Expr
instance [Inhabited α] : Inhabited (Expr α scope) :=
  ⟨.panic "uninhabited" default default⟩

/-! ## Evaluation Context -/

/-- Global environment for looking up definitions -/
structure GlobalEnv where
  /-- Map from global names to their values -/
  defs : Std.HashMap String Value := {}
  deriving Inhabited

namespace GlobalEnv

def empty : GlobalEnv := ⟨{}⟩

def insert (env : GlobalEnv) (name : String) (v : Value) : GlobalEnv :=
  ⟨env.defs.insert name v⟩

def lookup (env : GlobalEnv) (name : String) : Option Value :=
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

/-- Find the index of a binding in a scope (De Bruijn index) -/
def findBindingIndex (scope : Scope) (binding : BindingId) : Nat :=
  match scope.findIdx? (· == binding) with
  | some idx => idx
  | none => 0 -- Shouldn't happen for well-scoped terms

mutual

/-- Convert an Expr to a Term, dropping annotations and spans.
    Variables are converted using their position in the scope (De Bruijn index). -/
def exprToTerm {scope : Scope} (e : Expr α scope) : Term :=
  match e with
  | .var v _ _ =>
    -- Compute De Bruijn index from the binding's position in scope
    let idx := findBindingIndex scope v.binding
    .var idx v.original
  | .lit l _ => .lit l
  | .call fn args _ _ => .app (exprToTerm fn) (exprListToTerms args)
  | .let_ _ name value body _ _ => .let_ name (exprToTerm value) (exprToTerm body)
  | .lam params body _ _ => .lam (params.toList.map (·.2.1)) (exprToTerm body)
  | .if_ cond then_ else_ _ _ => .if_ (exprToTerm cond) (exprToTerm then_) (exprToTerm else_)
  | .pair fst snd _ _ => .pair (exprToTerm fst) (exprToTerm snd)
  | .fst e _ _ => .fst (exprToTerm e)
  | .snd e _ _ => .snd (exprToTerm e)
  | .pi qty binder name dom cod _ => .pi qty binder name (exprToTerm dom) (exprToTerm cod)
  | .sigma qty name fst snd _ => .sigma qty name (exprToTerm fst) (exprToTerm snd)
  | .type level _ => .type level
  | .primTy p _ => .primTy p
  | .higherPrimTy p _ => .higherPrimTy p
  | .rowEmpty _ => .rowEmpty
  | .rowExtend label fieldTy tail _ => .rowExtend (exprToTerm label) (exprToTerm fieldTy) (exprToTerm tail)
  | .recordTy row _ => .recordTy (exprToTerm row)
  | .variantTy row _ => .variantTy (exprToTerm row)
  | .labelLit name _ => .labelLit name
  | .record fields _ _ => .record (recordFieldsToTerms fields)
  | .fieldAccess e field _ _ _ => .fieldAccess (exprToTerm e) field
  | .construct name tag args _ _ => .construct name tag (exprListToTerms args)
  | .global name _ _ => .global name
  | .eq tyLevel ty lhs rhs _ => .eq tyLevel (exprToTerm ty) (exprToTerm lhs) (exprToTerm rhs)
  | .refl ty x _ => .refl (exprToTerm ty) (exprToTerm x)
  | .transport tyLevel ty motive lhs rhs eq body _ =>
      .transport tyLevel (exprToTerm ty) (exprToTerm motive) (exprToTerm lhs)
                 (exprToTerm rhs) (exprToTerm eq) (exprToTerm body)
  | .mvar id _ _ => .mvar id
  | .hole _ _ => .panic "hole in term"
  | .panic msg _ _ => .panic msg
  | .ann e _ _ _ => exprToTerm e
  | .closure name _ _ _ => .global name
  | .recordUpdate base updates _ _ => .panic "recordUpdate not supported in Term"
  | .inject label args _ _ => .panic "inject not yet supported"
  | .array elems _ _ => .panic "array not yet supported"
  | .case scrutinees arms _ _ => .panic "case not yet converted"
  | .tuple elems _ _ => .panic "tuple not yet converted"
  | .proj _ field _ _ _ => .panic s!"proj {field}"
  | .typeApp _ _ _ => .panic "typeApp not supported"
  | .dataTy _ _ _ => .panic "dataTy not supported"

/-- Convert ExprList to list of Terms -/
def exprListToTerms {scope : Scope} (es : ExprList α scope) : List Term :=
  match es with
  | .nil => []
  | .cons e rest => exprToTerm e :: exprListToTerms rest

/-- Convert record fields to list of (name, Term) pairs -/
def recordFieldsToTerms {scope : Scope} (fields : Soma.Metal.RecordFieldList α scope) : List (String × Term) :=
  match fields with
  | .nil => []
  | .cons name e rest => (name, exprToTerm e) :: recordFieldsToTerms rest

end

mutual

/-- Evaluate a Term to a Value.
    Terms use De Bruijn indices, which we resolve using the environment. -/
partial def evalTerm (ctx : EvalCtx) (t : Term) : Value :=
  match t with
  | .var idx name =>
    -- Look up by index: environment stores values in order, idx 0 is most recent
    let lvl := ctx.env.size - idx - 1
    match ctx.env.lookup ⟨lvl⟩ with
    | some v => v
    | none =>
      -- Fall back to name lookup for globals or error
      match ctx.env.lookupByName name with
      | some v => v
      | none => .vNeutral .type0 (.nVar ⟨name, ctx.env.level⟩)

  | .lit l =>
    match l with
    | .int n => .vIntLit n
    | .string s => .vStringLit s
    | .bool true => .vConstructor (.user ⟨0, "", "True"⟩) 0 []
    | .bool false => .vConstructor (.user ⟨0, "", "False"⟩) 1 []

  | .app fn args =>
    let fnVal := evalTerm ctx fn
    args.foldl (fun acc arg => vApp acc (evalTerm ctx arg) ctx) fnVal

  | .lam names body =>
    match names with
    | [] => evalTerm ctx body
    | name :: rest =>
      let innerBody := if rest.isEmpty then body else .lam rest body
      .vLam .omega .explicit name .type0 (Closure.mkWithBody name ctx.env innerBody)

  | .let_ name value body =>
    let valV := evalTerm ctx value
    let ctx' := ctx.extendEnv name valV
    evalTerm ctx' body

  | .if_ cond then_ else_ =>
    match evalTerm ctx cond with
    | .vConstructor _ 0 _ => evalTerm ctx then_  -- True
    | .vConstructor _ 1 _ => evalTerm ctx else_  -- False
    | condV => .vNeutral .type0 (.nVar ⟨"if", ctx.env.level⟩)  -- Stuck

  | .pair fst snd =>
    .vPair (evalTerm ctx fst) (evalTerm ctx snd)

  | .fst e =>
    match evalTerm ctx e with
    | .vPair f _ => f
    | v => .vNeutral .type0 (.nFst (.nVar ⟨"fst", ctx.env.level⟩))

  | .snd e =>
    match evalTerm ctx e with
    | .vPair _ s => s
    | v => .vNeutral .type0 (.nSnd (.nVar ⟨"snd", ctx.env.level⟩))

  | .pi qty binder name domain codomain =>
    let domVal := evalTerm ctx domain
    .vPi qty binder name domVal (Closure.mkWithBody name ctx.env codomain)

  | .sigma qty name fst snd =>
    let fstVal := evalTerm ctx fst
    .vSigma qty name fstVal (Closure.mkWithBody name ctx.env snd)

  | .type level => .vType level
  | .primTy p => .vPrimTy p
  | .higherPrimTy p => .vHigherPrim p
  | .intLit n => .vIntLit n
  | .stringLit s => .vStringLit s
  | .rowEmpty => .vRowEmpty
  | .labelLit name => .vLabelLit name

  | .recordTy row => .vRecord (evalTerm ctx row)
  | .variantTy row => .vVariant (evalTerm ctx row)

  | .rowExtend label fieldTy tail =>
    .vRowExtend (evalTerm ctx label) (evalTerm ctx fieldTy) (evalTerm ctx tail)

  | .record fields =>
    .vRecordVal (fields.map fun (name, t) => (name, evalTerm ctx t))

  | .fieldAccess e field =>
    match evalTerm ctx e with
    | .vRecordVal fields =>
      match fields.find? (·.1 == field) with
      | some (_, v) => v
      | none => .vNeutral .type0 (.nFieldAccess (.nVar ⟨"rec", ctx.env.level⟩) field)
    | v => .vNeutral .type0 (.nFieldAccess (.nVar ⟨"rec", ctx.env.level⟩) field)

  | .construct name tag args =>
    .vConstructor name tag (args.map (evalTerm ctx))

  | .case scrutinee arms =>
    -- Simplified case evaluation
    let scrut := evalTerm ctx scrutinee
    match scrut with
    | .vConstructor _ tag ctorArgs =>
      match arms.find? (fun (_, t, _) => t == tag) with
      | some (_, _, body) =>
        -- Extend environment with constructor arguments
        -- For now, just evaluate the body
        evalTerm ctx body
      | none => .vNeutral .type0 (.nVar ⟨"case", ctx.env.level⟩)
    | _ => .vNeutral .type0 (.nVar ⟨"case", ctx.env.level⟩)

  | .global name =>
    match ctx.globals.lookup name.display with
    | some v => v
    | none => .vNeutral .type0 (.nVar ⟨name.display, ⟨0⟩⟩)

  | .eq tyLevel ty lhs rhs =>
    .vEq tyLevel (evalTerm ctx ty) (evalTerm ctx lhs) (evalTerm ctx rhs)

  | .refl ty x =>
    .vRefl (evalTerm ctx ty) (evalTerm ctx x)

  | .transport tyLevel ty motive lhs rhs eq body =>
    -- Transport along equality: if the equality proof is refl, just return the body
    let eqVal := evalTerm ctx eq
    match eqVal with
    | .vRefl _ _ =>
      -- When proof is refl, the lhs and rhs are definitionally equal
      -- so transport reduces to the body
      evalTerm ctx body
    | _ =>
      -- Otherwise, transport is stuck (neutral)
      .vTransport tyLevel (evalTerm ctx ty) (evalTerm ctx motive)
                  (evalTerm ctx lhs) (evalTerm ctx rhs) eqVal (evalTerm ctx body)

  | .mvar id =>
    match ctx.metas.lookup ⟨id⟩ with
    | some info =>
      match info.solution with
      | some v => v
      | none => .vNeutral .type0 (.nMeta ⟨id⟩)
    | none => .vNeutral .type0 (.nMeta ⟨id⟩)

  | .panic msg =>
    .vNeutral .type0 (.nVar ⟨s!"panic: {msg}", ctx.env.level⟩)

/-- Apply a closure to an argument, we extend the environment and evaluate the body. -/
partial def applyClosure (clos : Closure) (arg : Value) (ctx : EvalCtx) : Value :=
  -- Extend the closure's environment with the argument
  let env' := clos.env.extend clos.name arg
  -- Evaluate the Term body under the extended environment
  match clos.body with
  | some body =>
    evalTerm { ctx with env := env' } body
  | none =>
    .vNeutral .type0 (.nVar ⟨clos.name, env'.level⟩)

/-- Apply a value to an argument -/
partial def vApp (fn : Value) (arg : Value) (ctx : EvalCtx) : Value :=
  match fn with
  | .vLam _ _ _ _ body =>
    applyClosure body arg ctx
  | .vNeutral ty neu =>
    -- Application is stuck, create neutral application
    -- The result type would be the codomain applied to arg
    .vNeutral ty (.nApp neu arg)
  | .vDataType id params =>
    -- Type application: accumulate type parameters
    .vDataType id (params ++ [arg])
  | .vHigherPrim hp =>
    -- Higher-kinded primitive applied to type argument
    -- Use a proper builtin TypeId with deterministic unique to avoid collisions
    let typeId := TypeId.builtin hp.name hp.uniqueId
    .vDataType typeId [arg]
  | _ =>
    -- Type error: applying non-function
    fn

/-- Evaluate an expression to a value -/
partial def eval (ctx : EvalCtx) : {scope : Scope} → Expr Unit scope → Value
  -- Variables
  | _, .var v _ _ =>
    -- Convert De Bruijn index to level and look up
    -- For now, use the variable name to look up in environment
    match ctx.env.lookupByName v.original with
    | some val => val
    | none => .vNeutral .type0 (.nVar ⟨v.original, ctx.env.level⟩)

  -- Literals
  | _, .lit (.int n) _ => .vIntLit n
  | _, .lit (.string s) _ => .vStringLit s
  | _, .lit (.bool true) _ => .vConstructor (.user ⟨0, "", "True"⟩) 0 []
  | _, .lit (.bool false) _ => .vConstructor (.user ⟨0, "", "False"⟩) 1 []

  -- Function application
  | _, .call fn args _ _ =>
    let fnVal := eval ctx fn
    evalArgs ctx args |>.foldl (fun acc arg => vApp acc arg ctx) fnVal

  -- Let binding
  | _, .let_ _ name value body _ _ =>
    let valV := eval ctx value
    let ctx' := ctx.extendEnv name valV
    eval ctx' body

  -- Lambda
  | _, .lam params body _ _ =>
    -- Create a closure capturing the current environment
    match params.toList with
    | [] => eval ctx body
    | (_, name, _) :: rest =>
      -- Convert the body to a Term for storage in the closure
      let termBody := exprToTerm body
      if rest.isEmpty then
        -- Single parameter lambda
        .vLam .omega .explicit name .type0 (Closure.mkWithBody name ctx.env termBody)
      else
        -- Multi-param: the body includes all parameters, so we store it once
        -- When applied, we'll extend the environment with each argument
        .vLam .omega .explicit name .type0 (Closure.mkWithBody name ctx.env termBody)

  -- Global reference
  | _, .global name _ _ =>
    match ctx.globals.lookup name.display with
    | some v => v
    | none => .vNeutral .type0 (.nVar ⟨name.display, ⟨0⟩⟩)

  -- Constructors
  | _, .construct name tag args _ _ =>
    let argVals := evalArgs ctx args
    .vConstructor name tag argVals

  -- Tuples (as pairs for 2-tuples)
  | _, .tuple elems _ _ =>
    let vals := evalArgs ctx elems
    match vals with
    | [a, b] => .vPair a b
    | _ => .vRecordVal (listEnumerate vals |>.map fun (i, v) => (s!"_{i}", v))

  -- Records
  | _, .record fields _ _ =>
    let fieldVals := evalRecordFields ctx fields
    .vRecordVal fieldVals

  -- Field access
  | _, .fieldAccess e fieldName _ _ _ =>
    let v := eval ctx e
    vFieldAccess v fieldName

  -- If-then-else
  | _, .if_ cond then_ else_ _ _ =>
    match eval ctx cond with
    | .vConstructor _ 0 _ => eval ctx then_  -- True
    | .vConstructor _ 1 _ => eval ctx else_  -- False
    | _ => .vNeutral .type0 (.nVar ⟨"if", ⟨0⟩⟩)  -- Stuck

  -- Dependent type constructors
  | _, .type level _ => .vType level

  | _, .pi qty binder name domain codomain _ =>
    let domV := eval ctx domain
    let codomainTerm := exprToTerm codomain
    .vPi qty binder name domV (Closure.mkWithBody name ctx.env codomainTerm)

  | _, .sigma qty name fst snd _ =>
    let fstV := eval ctx fst
    let sndTerm := exprToTerm snd
    .vSigma qty name fstV (Closure.mkWithBody name ctx.env sndTerm)

  | _, .pair fst snd _ _ =>
    .vPair (eval ctx fst) (eval ctx snd)

  | _, .fst e _ _ => vFst (eval ctx e)

  | _, .snd e _ _ => vSnd (eval ctx e)

  | _, .primTy p _ => .vPrimTy p

  | _, .higherPrimTy p _ => .vHigherPrim p

  | _, .rowEmpty _ => .vRowEmpty

  | _, .rowExtend label fieldTy tail _ =>
    .vRowExtend (eval ctx label) (eval ctx fieldTy) (eval ctx tail)

  | _, .recordTy row _ => .vRecord (eval ctx row)

  | _, .variantTy row _ => .vVariant (eval ctx row)

  | _, .labelLit name _ => .vLabelLit name

  | _, .dataTy id params _ =>
    let paramVals := evalArgs ctx params
    .vDataType id paramVals

  | _, .ann expr _ _ _ => eval ctx expr  -- Annotations are erased

  | _, .hole id _ =>
    -- Holes become metavariables
    .vNeutral .type0 (.nMeta ⟨id.id⟩)

  | _, .mvar id _ _ =>
    -- Look up metavariable solution
    match ctx.metas.lookup ⟨id⟩ with
    | some info =>
      match info.solution with
      | some v => v
      | none => .vNeutral .type0 (.nMeta ⟨id⟩)
    | none => .vNeutral .type0 (.nMeta ⟨id⟩)

  | _, .eq tyLevel ty lhs rhs _ =>
    .vEq tyLevel (eval ctx ty) (eval ctx lhs) (eval ctx rhs)

  | _, .refl ty x _ =>
    .vRefl (eval ctx ty) (eval ctx x)

  | _, .transport tyLevel ty motive lhs rhs eq body _ =>
    -- Transport along equality: if the equality proof is refl, just return the body
    let eqVal := eval ctx eq
    match eqVal with
    | .vRefl _ _ =>
      -- When proof is refl, the lhs and rhs are definitionally equal
      -- so transport reduces to the body
      eval ctx body
    | _ =>
      -- Otherwise, transport is stuck (neutral)
      .vTransport tyLevel (eval ctx ty) (eval ctx motive)
                  (eval ctx lhs) (eval ctx rhs) eqVal (eval ctx body)

  -- Fallback for other constructors
  | _, _ => .vNeutral .type0 (.nVar ⟨"_", ⟨0⟩⟩)

/-- Evaluate an expression list to a list of values -/
partial def evalArgs (ctx : EvalCtx) : {scope : Scope} → ExprList Unit scope → List Value
  | _, .nil => []
  | _, .cons e es => eval ctx e :: evalArgs ctx es

/-- Evaluate record fields to a list of (name, value) pairs -/
partial def evalRecordFields (ctx : EvalCtx) :
    {scope : Scope} → Soma.Metal.RecordFieldList Unit scope → List (String × Value)
  | _, .nil => []
  | _, .cons name expr rest =>
    (name, eval ctx expr) :: evalRecordFields ctx rest

end

/-- Evaluate a closed expression -/
def evalClosed (e : Expr Unit []) : Value :=
  eval EvalCtx.empty e

/-- Evaluate with a global environment -/
def evalWithGlobals (globals : GlobalEnv) (e : Expr Unit []) : Value :=
  eval { EvalCtx.empty with globals := globals } e

end Soma.Core
