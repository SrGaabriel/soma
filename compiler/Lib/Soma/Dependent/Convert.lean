import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Core.Expr
import Soma.Dependent.Monad
import Soma.Dependent.Error

namespace Soma.Dependent

open Soma.Core

/-- Check if two levels are equal -/
def convertLevel (l1 l2 : Level) : TCM Bool := do
  -- Simplify both levels first
  let l1' := l1.simplify
  let l2' := l2.simplify
  return l1' == l2'

mutual

/-- Apply a single eliminator to a value, performing canonical reduction -/
partial def applyElim (v : Value) (e : Elim) : TCM Value := do
  match v, e with
  | .vLam _ body, .eApp arg => applyClosure body arg
  | .vDataType id params, .eApp arg =>
    return .vDataType id (params ++ [arg])
  | .vPair a _, .eFst => pure a
  | .vPair _ b, .eSnd => pure b
  | .vRecordVal fields, .eField name =>
    match fields.find? (·.1 == name) with
    | some (_, v') => pure v'
    | none => pure v
  | .vNeutral ty neu, _ =>
    return .vNeutral ty (neu.pushElim e)
  | _, _ => pure v

/-- Fold a spine of eliminators over a value in order -/
partial def applySpine (v : Value) (spine : Array Elim) : TCM Value := do
  let mut result := v
  for e in spine do
    result ← applyElim result e
  return result

/-- Force a value to weak head normal form -/
partial def force (v : Value) : TCM Value := do
  match v with
  | .vNeutral _ neu =>
    match neu.head with
    | .hMeta id =>
      let info? ← TCM.lookupMeta id
      match info? with
      | some info =>
        match info.solution with
        | some sol =>
          let forced ← force sol
          match sol, forced with
          | .vNeutral _ solNeu, _ =>
            if solNeu.isBareHead then
              match solNeu.head, forced with
              | .hMeta _, .vNeutral _ finNeu =>
                if !finNeu.isBareHead then
                  TCM.updateMetaSolution id forced
                else
                  match finNeu.head with
                  | .hMeta _ => pure ()
                  | _ => TCM.updateMetaSolution id forced
              | .hMeta _, _ => TCM.updateMetaSolution id forced
              | _, _ => pure ()
            else
              pure ()
          | _, _ => pure ()
          let result ← applySpine forced neu.spine
          force result
        | none => return v
      | none => return v
    | _ => return v
  | .vDataType dId params =>
    let abbrev? ← TCM.lookupAbbrev ⟨dId⟩
    match abbrev? with
    | some abbrevInfo =>
      if params.length == abbrevInfo.arity then
        let mut result := abbrevInfo.expansion
        for arg in params do
          match result with
          | .vLam _ body => result ← applyClosure body arg
          | .vPi _ _ _ _ cod => result ← applyClosure cod arg
          | _ => return v
        force result
      else return v
    | none => return v
  | _ => return v

/-- Apply a closure to an argument -/
partial def applyClosure (clos : Closure) (arg : Value) : TCM Value := do
  match clos with
  | .const _name value =>
    return value
  | .term name env body =>
    let env' := env.extend name arg
    let state ← TCM.getState
    let ctx ← TCM.getCtx
    let evalCtx : EvalCtx := {
      env := env'
      globals := ctx.globals.toGlobalEnvWithClasses ctx.instanceEnv
      metas := state.metas
    }
    return Soma.Core.evalCoreExpr evalCtx body

end

/-- Eta-expand a value to a lambda if checking against a Pi type
    For a value v and Pi type (x : A) -> B, we create λx. v x -/
def etaExpandLam (v : Value) (piTy : Value) : TCM Value := do
  match v with
  | .vLam _ _ => return v
  | _ =>
    match piTy with
    | .vPi _qty _binder name _domain _codomain =>
      -- η-expand: v becomes λx. v x
      -- We need to create a closure that, when applied to an argument,
      -- applies v to that argument.
      let env ← TCM.getEnv
      -- Create the body Expr: application of v to the bound variable
      -- After closure application, env has _eta_fn(lvl=env.size) and param(lvl=env.size+1)
      -- bvar 0 = param (the closure arg), bvar 1 = _eta_fn (= v)
      let bodyExpr := Soma.Core.Expr.app (.bvar 1) (.bvar 0)
      -- Extend environment with v so it's available in the closure
      let env' := env.extend "_eta_fn" v
      let closure := Closure.term name env' bodyExpr
      return .vLam name closure
    | _ => return v

/-- Eta-expand a value to a pair if checking against a Sigma type -/
def etaExpandPair (v : Value) (sigmaTy : Value) : TCM Value := do
  match v with
  | .vPair _ _ => return v -- Already a pair
  | .vNeutral ty neu =>
    match sigmaTy with
    | .vSigma _ _ _ _ =>
      -- η-expand: v becomes (v.1, v.2)
      let fst := Value.vNeutral ty (.nFst neu)
      let snd := Value.vNeutral ty (.nSnd neu)
      return .vPair fst snd
    | _ => return v
  | _ => return v

/-- Find a label in a row and return the field type and remaining row -/
partial def findAndRemoveLabel (label : String) (row : Value) : TCM (Option (Value × Value)) := do
  match row with
  | .vRowEmpty => return none
  | .vRowExtend (.vLabelLit l) ty tail =>
    if l == label then
      return some (ty, tail)
    else
      match ← findAndRemoveLabel label tail with
      | some (foundTy, restTail) =>
        -- Reconstruct: { l : ty | restTail }
        return some (foundTy, .vRowExtend (.vLabelLit l) ty restTail)
      | none => return none
  | .vNeutral _ _ =>
    -- Can't search in a neutral row (would need unification)
    return none
  | _ => return none

mutual

/-- Normalize wired primitive data type wrappers into canonical primitive types -/
private partial def normalizeWiredPrimitiveValue (v : Value) : TCM Value := do
  match v with
  | .vDataType u [] =>
    match ← TCM.lookupWiredPrimitiveOfTypeUnique u with
    | some prim => if prim.isNullary then pure (.vPrimTy prim) else pure v
    | none => pure v
  | _ => pure v

/-- Check if two values are convertible (definitionally equal) -/
partial def convert (v1 v2 : Value) : TCM Bool := do
  -- Force both values to resolve metavariables
  let v1f ← force v1
  let v2f ← force v2
  let v1' ← normalizeWiredPrimitiveValue v1f
  let v2' ← normalizeWiredPrimitiveValue v2f

  match v1', v2' with
  -- Type universes
  | .vType l1, .vType l2 =>
    convertLevel l1 l2

  -- Pi types: compare binders, domains, and codomains
  | .vPi q1 b1 n1 d1 c1, .vPi q2 b2 _ d2 c2 =>
    if q1 != q2 then return false
    if b1 != b2 then return false -- Binder info must match
    let domEq ← convert d1 d2
    if !domEq then return false
    -- Compare codomains under a fresh variable
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral d1 (.nVar ⟨n1, lvl⟩)
    let cod1 ← applyClosure c1 x
    let cod2 ← applyClosure c2 x
    convert cod1 cod2

  -- Lambdas: compare bodies under a fresh variable
  | .vLam n1 body1, .vLam _ body2 =>
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral .type0 (.nVar ⟨n1, lvl⟩)
    let b1Val ← applyClosure body1 x
    let b2Val ← applyClosure body2 x
    convert b1Val b2Val

  -- Sigma types
  | .vSigma q1 n1 f1 s1, .vSigma q2 _ f2 s2 =>
    if q1 != q2 then return false
    let fstEq ← convert f1 f2
    if !fstEq then return false
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral f1 (.nVar ⟨n1, lvl⟩)
    let snd1 ← applyClosure s1 x
    let snd2 ← applyClosure s2 x
    convert snd1 snd2

  -- Pairs
  | .vPair a1 b1, .vPair a2 b2 =>
    let fstEq ← convert a1 a2
    if !fstEq then return false
    convert b1 b2

  -- Primitives
  | .vPrimTy p1, .vPrimTy p2 => return p1 == p2

  -- Literals
  | .vIntLit n1, .vIntLit n2 => return n1 == n2
  | .vFloatLit f1, .vFloatLit f2 => return f1 == f2
  | .vStringLit s1, .vStringLit s2 => return s1 == s2
  | .vLabelLit l1, .vLabelLit l2 => return l1 == l2

  -- Row/label sorts
  | .vRowSort, .vRowSort => return true
  | .vLabelSort, .vLabelSort => return true

  -- Rows
  | .vRowEmpty, .vRowEmpty => return true
  | .vRowExtend l1 t1 r1, .vRowExtend l2 t2 r2 =>
    -- Row types are considered equal up to permutation
    -- todo: full row unification
    let labelEq ← convert l1 l2
    if !labelEq then
      -- Try row rewriting
      convertRowsWithRewriting v1' v2'
    else
      let tyEq ← convert t1 t2
      if !tyEq then return false
      convert r1 r2

  -- Record and variant types
  | .vRecord r1, .vRecord r2 => convert r1 r2
  | .vVariant r1, .vVariant r2 => convert r1 r2

  -- Record values
  | .vRecordVal fs1, .vRecordVal fs2 =>
    if fs1.length != fs2.length then return false
    -- Fields can be in different order
    convertRecordFields fs1 fs2

  -- Data types
  | .vDataType id1 ps1, .vDataType id2 ps2 =>
    if id1 != id2 then return false
    if ps1.length != ps2.length then return false
    convertValueLists ps1 ps2

  -- Constructors
  | .vConstructor n1 t1 as1 _, .vConstructor n2 t2 as2 _ =>
    if n1 != n2 || t1 != t2 then return false
    if as1.length != as2.length then return false
    convertValueLists as1 as2

  -- Equality types
  | .vEq l1 t1 a1 b1, .vEq l2 t2 a2 b2 =>
    let lvlEq ← convertLevel l1 l2
    if !lvlEq then return false
    let tyEq ← convert t1 t2
    if !tyEq then return false
    let lhsEq ← convert a1 a2
    if !lhsEq then return false
    convert b1 b2

  -- Refl
  | .vRefl t1 x1, .vRefl t2 x2 =>
    let tyEq ← convert t1 t2
    if !tyEq then return false
    convert x1 x2

  -- Transport
  | .vTransport l1 t1 m1 lhs1 rhs1 eq1 b1, .vTransport l2 t2 m2 lhs2 rhs2 eq2 b2 =>
    let lvlEq ← convertLevel l1 l2
    if !lvlEq then return false
    let tyEq ← convert t1 t2
    if !tyEq then return false
    let motiveEq ← convert m1 m2
    if !motiveEq then return false
    let lhsEq ← convert lhs1 lhs2
    if !lhsEq then return false
    let rhsEq ← convert rhs1 rhs2
    if !rhsEq then return false
    let eqEq ← convert eq1 eq2
    if !eqEq then return false
    convert b1 b2

  -- Neutral terms
  | .vNeutral _ n1, .vNeutral _ n2 =>
    convertNeutral n1 n2

  -- Eta rules for functions: v1 = λx. v2 x  iff  v1 x = v2 x for fresh x
  | .vLam n1 b1, .vNeutral ty neu =>
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral .type0 (.nVar ⟨n1, lvl⟩)
    let body1 ← applyClosure b1 x
    let body2 := Value.vNeutral ty (.nApp neu x)
    convert body1 body2

  | .vNeutral ty neu, .vLam n2 b2 =>
    let lvl ← TCM.currentLevel
    let x := Value.vNeutral .type0 (.nVar ⟨n2, lvl⟩)
    let body1 := Value.vNeutral ty (.nApp neu x)
    let body2 ← applyClosure b2 x
    convert body1 body2

  -- Eta rules for pairs
  | .vPair a1 b1, .vNeutral ty neu =>
    let fst := Value.vNeutral ty (.nFst neu)
    let snd := Value.vNeutral ty (.nSnd neu)
    let fstEq ← convert a1 fst
    if !fstEq then return false
    convert b1 snd

  | .vNeutral ty neu, .vPair a2 b2 =>
    let fst := Value.vNeutral ty (.nFst neu)
    let snd := Value.vNeutral ty (.nSnd neu)
    let fstEq ← convert fst a2
    if !fstEq then return false
    convert snd b2

  -- Different constructors
  | _, _ => return false

/-- Check if two neutral heads are convertible -/
partial def convertHead (h1 h2 : Head) : TCM Bool := do
  match h1, h2 with
  | .hVar v1, .hVar v2 => return v1.level == v2.level
  | .hMeta m1, .hMeta m2 => return m1 == m2
  | .hConst c1 _, .hConst c2 _ => return c1 == c2
  | .hCase ss1 as1 _, .hCase ss2 as2 _ =>
    if ss1.size != ss2.size then return false
    for (s1, s2) in ss1.zip ss2 do
      let eq ← convert s1 s2
      if !eq then return false
    if as1.length != as2.length then return false
    for (arm1, arm2) in as1.zip as2 do
      if arm1.pattern != arm2.pattern then return false
      let lvl ← TCM.currentLevel
      let freshArg := Value.vNeutral .type0 (.nVar ⟨"_case_arg", lvl⟩)
      let body1 ← applyClosure arm1.closure freshArg
      let body2 ← applyClosure arm2.closure freshArg
      let bodiesEq ← convert body1 body2
      if !bodiesEq then return false
    return true
  | _, _ => return false

/-- Check if two eliminators are convertible -/
partial def convertElim (e1 e2 : Elim) : TCM Bool := do
  match e1, e2 with
  | .eApp a1, .eApp a2 => convert a1 a2
  | .eFst, .eFst => return true
  | .eSnd, .eSnd => return true
  | .eField f1, .eField f2 => return f1 == f2
  | _, _ => return false

/-- Check if two neutral terms are convertible: same head, same spine -/
partial def convertNeutral (n1 n2 : Neutral) : TCM Bool := do
  let headEq ← convertHead n1.head n2.head
  if !headEq then return false
  if n1.spine.size != n2.spine.size then return false
  for (e1, e2) in n1.spine.zip n2.spine do
    let eq ← convertElim e1 e2
    if !eq then return false
  return true

/-- Convert rows with rewriting (find label in one row, match with other) -/
partial def convertRowsWithRewriting (r1 r2 : Value) : TCM Bool := do
  -- Extract the first label from r1 and try to find it in r2
  match r1 with
  | .vRowExtend (.vLabelLit label) ty1 tail1 =>
    -- Try to find this label in r2
    match ← findAndRemoveLabel label r2 with
    | some (ty2, tail2) =>
      let tyEq ← convert ty1 ty2
      if !tyEq then return false
      convert tail1 tail2
    | none => return false
  | _ => return false

/-- Convert two lists of values pairwise -/
partial def convertValueLists (vs1 vs2 : List Value) : TCM Bool := do
  match vs1, vs2 with
  | [], [] => return true
  | v1 :: rest1, v2 :: rest2 =>
    let eq ← convert v1 v2
    if !eq then return false
    convertValueLists rest1 rest2
  | _, _ => return false

/-- Convert record fields (order-independent) -/
partial def convertRecordFields (fs1 fs2 : List (String × Value)) : TCM Bool := do
  for (name, val1) in fs1 do
    match fs2.find? (·.1 == name) with
    | some (_, val2) =>
      let eq ← convert val1 val2
      if !eq then return false
    | none => return false
  return true

end

/-- Check if v1 is a subtype of v2 (for now, just conversion) -/
def subtype (v1 v2 : Value) : TCM Bool :=
  convert v1 v2

/-- Check if two values have structurally incompatible heads -/
partial def structurallyIncompatible (v1 v2 : Value) : TCM Bool := do
  let v1' ← force v1
  let v2' ← force v2
  match v1', v2' with
  | .vConstructor n1 _ args1 _, .vConstructor n2 _ args2 _ =>
    if n1 != n2 then return true
    if args1.length != args2.length then return true
    incompatPairwise args1 args2
  | .vIntLit n1, .vIntLit n2 => return n1 != n2
  | .vFloatLit f1, .vFloatLit f2 => return f1 != f2
  | .vStringLit s1, .vStringLit s2 => return s1 != s2
  | .vPrimTy p1, .vPrimTy p2 => return p1 != p2
  | .vDataType id1 ps1, .vDataType id2 ps2 =>
    if id1 != id2 then return true
    if ps1.length != ps2.length then return true
    incompatPairwise ps1 ps2
  | _, _ => return false
where
  /-- True when any positional pair of values is structurally incompatible -/
  incompatPairwise (l1 l2 : List Value) : TCM Bool := do
    match l1, l2 with
    | a1 :: rest1, a2 :: rest2 =>
      if ← structurallyIncompatible a1 a2 then return true
      incompatPairwise rest1 rest2
    | _, _ => return false

/-- Assert that two values are convertible, throwing an error if not -/
def assertConvert (v1 v2 : Value) (purpose : CheckPurpose) : TCM Unit := do
  let eq ← convert v1 v2
  if !eq then
    let span ← TCM.getSpan
    TCM.throw (.typeMismatch v2 v1 purpose span span #[])

/-- Check conversion and return the result as an Option -/
def tryConvert (v1 v2 : Value) : TCM (Option Unit) := do
  let eq ← convert v1 v2
  if eq then return some () else return none

end Soma.Dependent
