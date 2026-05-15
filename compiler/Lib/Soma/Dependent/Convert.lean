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

partial def patternAlphaEq : Pattern → Pattern → Bool
  | .var (some _), .var (some _) => true
  | .var none, .var none => true
  | .var none, .wildcard => true
  | .wildcard, .var none => true
  | .wildcard, .wildcard => true
  | .ctor n1 t1 fs1, .ctor n2 t2 fs2 =>
    n1 == n2 && t1 == t2 && patternsAlphaEq fs1 fs2
  | .lit l1, .lit l2 => l1 == l2
  | .inject l1 a1, .inject l2 a2 =>
    l1 == l2 &&
      match a1, a2 with
      | none, none => true
      | some p1, some p2 => patternAlphaEq p1 p2
      | _, _ => false
  | _, _ => false

partial def patternsAlphaEq (ps1 ps2 : Array Pattern) : Bool := Id.run do
  if ps1.size != ps2.size then return false
  for _h : i in [:ps1.size] do
    if !patternAlphaEq ps1[i]! ps2[i]! then return false
  return true

end

def freshCasePatternArg (baseLvl : DeBruijnLvl) (idx : Nat) : Value :=
  Value.vNeutral .type0 (.nVar ⟨s!"_arm_arg_{idx}", ⟨baseLvl.lvl + idx⟩⟩)

partial def freshPatternBindingArgsFrom
    (p : Pattern) (baseLvl : DeBruijnLvl) (next : Nat) : Array Value × Nat :=
  match p with
  | .var (some _) => (#[freshCasePatternArg baseLvl next], next + 1)
  | .var none | .lit _ | .wildcard | .inject _ none => (#[], next)
  | .ctor _ _ fields =>
    fields.foldl
      (fun (acc, n) field =>
        let (args, n') := freshPatternBindingArgsFrom field baseLvl n
        (acc ++ args, n'))
      (#[], next)
  | .inject _ (some p) => freshPatternBindingArgsFrom p baseLvl next

partial def alignPatternBindings
    (small big : Pattern) (baseLvl : DeBruijnLvl) (next : Nat)
    : Option (Array Value × Array Value × Nat) :=
  match small, big with
  | .var (some _), .var (some _) =>
    let v := freshCasePatternArg baseLvl next
    some (#[v], #[v], next + 1)
  | .var none, _
  | .wildcard, _ =>
    let (bigArgs, next') := freshPatternBindingArgsFrom big baseLvl next
    some (#[], bigArgs, next')
  | .lit l1, .lit l2 =>
    if l1 == l2 then some (#[], #[], next) else none
  | .ctor n1 t1 fs1, .ctor n2 t2 fs2 =>
    if n1 != n2 || t1 != t2 || fs1.size != fs2.size then none
    else
      fs1.zip fs2 |>.foldl
        (fun acc? (p1, p2) =>
          match acc? with
          | none => none
          | some (smallAcc, bigAcc, n) =>
            match alignPatternBindings p1 p2 baseLvl n with
            | none => none
            | some (smallArgs, bigArgs, n') =>
              some (smallAcc ++ smallArgs, bigAcc ++ bigArgs, n'))
        (some (#[], #[], next))
  | .inject l1 a1, .inject l2 a2 =>
    if l1 != l2 then none
    else
      match a1, a2 with
      | none, none => some (#[], #[], next)
      | some p1, some p2 => alignPatternBindings p1 p2 baseLvl next
      | _, _ => none
  | _, _ => none

def trivialExtraPatternArgs
    (patterns : Array Pattern) (scruts : Array Value) (start : Nat)
    : Option (Array Value) := Id.run do
  if patterns.size != scruts.size then return none
  let mut args : Array Value := #[]
  for i in [start:patterns.size] do
    match patterns[i]! with
    | .wildcard => pure ()
    | .var none => pure ()
    | .var (some _) => args := args.push scruts[i]!
    | _ => return none
  return some args

/-- Apply an arm closure to a spine of pattern bindings -/
partial def applyArmClosureSpine (clos : Closure) (args : Array Value) : TCM Value := do
  match clos with
  | .const _ v => return v
  | .term _ env body =>
    let mut env' := env
    for arg in args do
      env' := env'.extend "_" arg
    let state ← TCM.getState
    let ctx ← TCM.getCtx
    let evalCtx : EvalCtx := {
      env := env'
      globals := ctx.globals.toGlobalEnvWithClasses ctx.instanceEnv
      metas := state.metas
    }
    return Soma.Core.evalCoreExpr evalCtx body

/-- Apply an arm closure for structural comparison of arm bodies -/
partial def applyArmClosureSpineOpaque (clos : Closure) (args : Array Value)
    : TCM Value := do
  match clos with
  | .const _ v => return v
  | .term _ env body =>
    let mut env' := env
    for arg in args do
      env' := env'.extend "_" arg
    let state ← TCM.getState
    let evalCtx : EvalCtx := {
      env := env'
      globals := .empty
      metas := state.metas
    }
    return Soma.Core.evalCoreExpr evalCtx body

mutual

/-- Apply a single eliminator to a value, performing canonical reduction -/
partial def applyElim (v : Value) (e : Elim) : TCM Value := do
  match v, e with
  | .vLam _ body, .eApp arg => applyClosure body arg
  | .vDataType id params, .eApp arg =>
    return .vDataType id (params ++ [arg])
  | .vRecordVal fields, .eField name =>
    match fields.find? (·.1 == name) with
    | some (_, v') => pure v'
    | none => pure v
  | .vConstructor _ _ _ _, .eField name =>
    let ctx ← TCM.getCtx
    match v with
    | .vConstructor ctorName _ args _ =>
      match ctx.globals.lookupInductiveByCtor ctorName with
      | some indMeta =>
        match indMeta.fieldNames.findIdx? (· == name) with
        | some idx =>
          match args.toArray[idx]? with
          | some fieldVal => pure fieldVal
          | none => pure v
        | none => pure v
      | none => pure v
    | _ => pure v
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
  | .vNeutral ty neu =>
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
    | .hConst qn _ =>
      let ctx ← TCM.getCtx
      match ctx.globals.defs.get? qn with
      | some info =>
        match info.value with
        | some bodyVal =>
          let result ← applySpine bodyVal neu.spine
          let forced ← force result
          match forced with
          | .vNeutral _ ⟨.hCase _ _ _, _⟩ => return v
          | _ => return forced
        | none => return v
      | none => return v
    | .hCase scruts motive arms =>
      let scruts' ← scruts.mapM force
      let rec findArm : List ArmClosure → TCM (Option Value)
        | [] => pure none
        | arm :: rest => do
          match matchPatternArrays arm.patterns scruts' with
          | .matched bindings => do
            let reduced ← applyArmClosureSpine arm.closure bindings
            pure (some reduced)
          | .mismatch => findArm rest
          | .stuck => pure none
      match ← findArm arms with
      | some reduced => do
        let result ← applySpine reduced neu.spine
        force result
      | none =>
        return .vNeutral ty (.mk (.hCase scruts' motive arms) neu.spine)
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

/-- Try to expand a `vDataType` head once when it refers to a fully-applied type abbreviation -/
partial def tryUnfoldOneStep (v : Value) : TCM (Option (Value × String)) := do
  match v with
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
          | _ => return none
        return some (result, s!"abbrev {dId.original}")
      else return none
    | none => return none
  | _ => return none

abbrev LevelSubst := Std.HashMap Nat Value

namespace LevelSubst

def empty : LevelSubst := {}

def isEmpty (σ : LevelSubst) : Bool := σ.toList.isEmpty

def extend (σ : LevelSubst) (lvl : DeBruijnLvl) (v : Value) : LevelSubst :=
  Std.HashMap.insert σ lvl.lvl v

def lookup (σ : LevelSubst) (lvl : DeBruijnLvl) : Option Value :=
  σ.get? lvl.lvl

end LevelSubst

mutual

/-- Apply a level substitution to a Value -/
partial def substValue (σ : LevelSubst) (v : Value) : TCM Value := do
  if σ.isEmpty then return v
  match v with
  | .vType _| .vIntLit _ | .vFloatLit _ | .vStringLit _
  | .vLabelLit _ | .vRowSort | .vLabelSort | .vRowEmpty => return v
  | .vPi q b n d c =>
    let d' ← substValue σ d
    let c' ← substClosure σ c
    return .vPi q b n d' c'
  | .vLam n c =>
    let c' ← substClosure σ c
    return .vLam n c'
  | .vRowExtend l t tail =>
    let l' ← substValue σ l
    let t' ← substValue σ t
    let tail' ← substValue σ tail
    return .vRowExtend l' t' tail'
  | .vRecord r => do let r' ← substValue σ r; return .vRecord r'
  | .vVariant r => do let r' ← substValue σ r; return .vVariant r'
  | .vRecordVal fields =>
    let fields' ← fields.mapM fun (n, v) => do
      let v' ← substValue σ v
      return (n, v')
    return .vRecordVal fields'
  | .vDataType id params =>
    let params' ← params.mapM (substValue σ)
    return .vDataType id params'
  | .vConstructor name tag args rty =>
    let args' ← args.mapM (substValue σ)
    let rty' ← substValue σ rty
    return .vConstructor name tag args' rty'
  | .vNeutral ty neu =>
    let ty' ← substValue σ ty
    substNeutral σ ty' neu

partial def substNeutral (σ : LevelSubst) (refinedTy : Value) (neu : Neutral) : TCM Value := do
  match neu.head with
  | .hVar bv =>
    match σ.lookup bv.level with
    | some replacement =>
      -- Spine may itself reference substituted variables
      let spine' ← neu.spine.mapM (substElim σ)
      -- Apply original spine of eliminators to the replacement value
      let mut result := replacement
      for e in spine' do
        result ← applyElim result e
      return result
    | none =>
      let spine' ← neu.spine.mapM (substElim σ)
      return .vNeutral refinedTy (.mk neu.head spine')
  | _ =>
    let head' ← substHead σ neu.head
    let spine' ← neu.spine.mapM (substElim σ)
    return .vNeutral refinedTy (.mk head' spine')

partial def substHead (σ : LevelSubst) (h : Head) : TCM Head := do
  match h with
  | .hVar _ | .hMeta _ | .hErrored => return h
  | .hConst name ty =>
    let ty' ← substValue σ ty
    return .hConst name ty'
  | .hCase scruts motive arms =>
    let scruts' ← scruts.mapM (substValue σ)
    let motive' ← substValue σ motive
    let arms' ← arms.mapM fun arm => do
      let clos' ← substClosure σ arm.closure
      return ArmClosure.mk arm.pattern clos' arm.patterns
    return .hCase scruts' motive' arms'

partial def substElim (σ : LevelSubst) (e : Elim) : TCM Elim := do
  match e with
  | .eApp arg => do let arg' ← substValue σ arg; return .eApp arg'
  | e => pure e

partial def substClosure (σ : LevelSubst) (c : Closure) : TCM Closure := do
  match c with
  | .const name v =>
    let v' ← substValue σ v
    return .const name v'
  | .term name env body =>
    -- Substitute inside env values
    let values' ← env.values.mapM fun (n, v) => do
      let v' ← substValue σ v
      return (n, v')
    return .term name (Env.mk values' env.size) body

end

private def scrutineeTypeOf (v : Value) : Value :=
  match v with
  | .vNeutral ty _ => ty
  | .vConstructor _ _ _ ty => ty
  | .vIntLit _ | .vFloatLit _ | .vStringLit _ => .type0
  | _ => .type0

private def literalPatternValue? : Literal → Option Value
  | .int n => some (.vIntLit n)
  | .float f => some (.vFloatLit f)
  | .string s => some (.vStringLit s)

mutual

private partial def refinedPatternValue
    (p : Pattern) (scrutTy : Value) (baseLvl : DeBruijnLvl) (next : Nat)
    : Option (Value × Array Value × Nat) :=
  match p with
  | .var (some _) =>
    let v := freshCasePatternArg baseLvl next
    some (v, #[v], next + 1)
  | .var none | .wildcard =>
    let v := freshCasePatternArg baseLvl next
    some (v, #[], next + 1)
  | .lit lit =>
    match literalPatternValue? lit with
    | some v => some (v, #[], next)
    | none => none
  | .ctor name tag fields =>
    match refinedPatternValues fields baseLvl next with
    | none => none
    | some (fieldVals, bindingArgs, next') =>
      some (.vConstructor name tag fieldVals.toList scrutTy, bindingArgs, next')
  | .inject _ _ =>
    none

private partial def refinedPatternValues
    (ps : Array Pattern) (baseLvl : DeBruijnLvl) (next : Nat)
    : Option (Array Value × Array Value × Nat) := Id.run do
  let mut vals : Array Value := #[]
  let mut args : Array Value := #[]
  let mut cur := next
  for _h : i in [:ps.size] do
    match refinedPatternValue ps[i]! .type0 baseLvl cur with
    | none => return none
    | some (v, bindingArgs, next') =>
      vals := vals.push v
      args := args ++ bindingArgs
      cur := next'
  return some (vals, args, cur)

end

private def bareScrutineeLevel? (v : Value) : Option DeBruijnLvl :=
  match v with
  | .vNeutral _ neu =>
    if neu.isBareHead then
      match neu.head with
      | .hVar bv => some bv.level
      | _ => none
    else none
  | _ => none

mutual

partial def alignPatternBindingsWithRefinement
    (small big : Pattern) (scrutTy : Value) (scrutVal? : Option Value)
    (baseLvl : DeBruijnLvl) (next : Nat)
    : Option (Array Value × Array Value × Value × Nat) :=
  match small, big with
  | .var (some _), .var (some _) =>
    match scrutVal? with
    | some v => some (#[v], #[v], v, next)
    | none =>
      let v := freshCasePatternArg baseLvl next
      some (#[v], #[v], v, next + 1)
  | .var (some _), .var none
  | .var (some _), .wildcard =>
    match scrutVal? with
    | some v => some (#[v], #[], v, next)
    | none =>
      let v := freshCasePatternArg baseLvl next
      some (#[v], #[], v, next + 1)
  | .var none, .var (some _)
  | .wildcard, .var (some _) =>
    match scrutVal? with
    | some v => some (#[], #[v], v, next)
    | none =>
      let v := freshCasePatternArg baseLvl next
      some (#[], #[v], v, next + 1)
  | .var none, .var none
  | .var none, .wildcard
  | .wildcard, .var none
  | .wildcard, .wildcard =>
    match scrutVal? with
    | some v => some (#[], #[], v, next)
    | none =>
      let v := freshCasePatternArg baseLvl next
      some (#[], #[], v, next + 1)
  | .var (some _), _ =>
    match refinedPatternValue big scrutTy baseLvl next with
    | none => none
    | some (bigVal, bigArgs, next') => some (#[bigVal], bigArgs, bigVal, next')
  | .var none, _
  | .wildcard, _ =>
    match refinedPatternValue big scrutTy baseLvl next with
    | none => none
    | some (bigVal, bigArgs, next') => some (#[], bigArgs, bigVal, next')
  | .lit l1, .lit l2 =>
    if l1 != l2 then none
    else
      match literalPatternValue? l2 with
      | some v => some (#[], #[], v, next)
      | none => none
  | .ctor n1 t1 fs1, .ctor n2 t2 fs2 =>
    if n1 != n2 || t1 != t2 || fs1.size != fs2.size then none
    else
      let fieldScruts :=
        match scrutVal? with
        | some (.vConstructor _ _ args _) => args.toArray
        | _ => #[]
      match alignPatternArraysWithRefinement fs1 fs2 fieldScruts baseLvl next with
      | none => none
      | some (smallArgs, bigArgs, fieldVals, next') =>
        some (smallArgs, bigArgs, .vConstructor n2 t2 fieldVals.toList scrutTy, next')
  | .inject _ _, .inject _ _ =>
    none
  | _, _ => none

partial def alignPatternArraysWithRefinement
    (small big : Array Pattern) (scruts : Array Value) (baseLvl : DeBruijnLvl) (next : Nat)
    : Option (Array Value × Array Value × Array Value × Nat) := Id.run do
  if small.size != big.size then return none
  let mut smallArgs : Array Value := #[]
  let mut bigArgs : Array Value := #[]
  let mut refinedVals : Array Value := #[]
  let mut cur := next
  for _h : i in [:small.size] do
    let scrutTy :=
      match scruts[i]? with
      | some scrut => scrutineeTypeOf scrut
      | none => .type0
    match alignPatternBindingsWithRefinement small[i]! big[i]! scrutTy scruts[i]? baseLvl cur with
    | none => return none
    | some (sArgs, bArgs, refinedVal, next') =>
      smallArgs := smallArgs ++ sArgs
      bigArgs := bigArgs ++ bArgs
      refinedVals := refinedVals.push refinedVal
      cur := next'
  return some (smallArgs, bigArgs, refinedVals, cur)

end

def refinementSubstForScruts
    (scruts refinedVals : Array Value) : LevelSubst := Id.run do
  let mut σ := LevelSubst.empty
  for _h : i in [:scruts.size] do
    if let some refined := refinedVals[i]? then
      if let some lvl := bareScrutineeLevel? scruts[i]! then
        σ := σ.extend lvl refined
  return σ

/-- Apply a value to a sequence of ordinary arguments -/
partial def applyValueArgs (v : Value) (args : Array Value) : TCM Value := do
  let mut result := v
  for arg in args do
    result ← applyElim result (.eApp arg)
  return result

/-- Apply arguments only when the current value is visibly function-typed -/
partial def applyValueArgsAsFunction? (v : Value) (args : Array Value) : TCM (Option Value) := do
  let mut result := v
  for arg in args do
    let fn ← force result
    match fn with
    | .vLam _ _ =>
      result ← applyElim fn (.eApp arg)
    | .vNeutral ty _ =>
      match ← force ty with
      | .vPi _ _ _ _ _ =>
        result ← applyElim fn (.eApp arg)
      | _ => return none
    | _ => return none
  return some result

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

/-- Does a value live in the `Prop` universe -/
partial def valueInPropUniverse (v : Value) : TCM Bool := do
  let v' ← force v
  match v' with
  | .vType .prop => return true
  | .vDataType uid _ =>
    let ctx ← TCM.getCtx
    let qn : Soma.Core.QualifiedName := ⟨uid⟩
    match ctx.globals.lookupInductive qn with
    | some info => return info.headSort.isProp
    | none => return false
  | .vPi _ _ name _ cod =>
    let lvl ← TCM.currentLevel
    let dummy := Value.vNeutral (.vType .zero) (.nVar ⟨name, lvl⟩)
    let codVal ← applyClosure cod dummy
    valueInPropUniverse codVal
  | .vNeutral ty _ =>
    -- A stuck term lives in Prop exactly when its type is Prop
    match (← force ty) with
    | .vType .prop => return true
    | _ => return false
  | _ => return false

/-- Auto-erasure predicate for Pi / lambda binders -/
partial def shouldAutoEraseBinder (domVal : Value) : TCM Bool := do
  match (← force domVal) with
  | .vType _ => return true
  | _ => valueInPropUniverse domVal

/-- Walk a constructor's Pi chain and check every field -/
partial def allCtorFieldsInProp (ctorType : Value) (skipParams : Nat) : TCM Bool := do
  match (← force ctorType) with
  | .vPi _ _ name dom cod =>
    let lvl ← TCM.currentLevel
    let dummy := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
    let codVal ← applyClosure cod dummy
    if skipParams > 0 then
      allCtorFieldsInProp codVal (skipParams - 1)
    else
      if !(← valueInPropUniverse dom) then return false
      allCtorFieldsInProp codVal 0
  | _ => return true

/-- Is a Prop-kinded inductive small -/
partial def isInductiveSmall (info : InductiveMeta) : TCM Bool := do
  if !info.headSort.isProp then return false
  match info.ctors.size with
  | 0 => return true
  | 1 => allCtorFieldsInProp info.ctors[0]!.type info.typeVarNames.size
  | _ => return false

/-- Does a value seen at the type level name a small Prop inductive -/
partial def valueIsSmallProp (v : Value) : TCM Bool := do
  match (← force v) with
  | .vDataType uid _ =>
    let ctx ← TCM.getCtx
    match ctx.globals.lookupInductive ⟨uid⟩ with
    | some info => isInductiveSmall info
    | none => return false
  | _ => return false

/-- Theorem-result-type predicate -/
partial def isTheoremType (v : Value) : TCM Bool := do
  if (← valueInPropUniverse v) then return true
  match (← force v) with
  | .vPi _ _ name dom cod =>
    if (← valueIsSmallProp dom) then return true
    let lvl ← TCM.currentLevel
    let dummy := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
    let codVal ← applyClosure cod dummy
    isTheoremType codVal
  | _ => return false

/-- Check if two values are convertible (definitionally equal) -/
partial def convert (v1 v2 : Value) : TCM Bool := do
  -- Force both values to resolve metavariables
  let v1' ← force v1
  let v2' ← force v2

  -- Proof-irrelevance short-circuit
  let irrelevanceTy? : Option Value ←
    match v1', v2' with
    | .vNeutral t _, _ => pure (some t)
    | _, .vNeutral t _ => pure (some t)
    | _, _            => pure none
  match irrelevanceTy? with
  | some t =>
    if (← valueInPropUniverse t) then return true
  | none => pure ()

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

  | .vConstructor _ 0 ctorArgs ctorRty, .vNeutral neuTy neu =>
    recordEtaConvert ctorArgs ctorRty neuTy neu (ctorOnLeft := true)

  | .vNeutral neuTy neu, .vConstructor _ 0 ctorArgs ctorRty =>
    recordEtaConvert ctorArgs ctorRty neuTy neu (ctorOnLeft := false)

  -- Different constructors
  | _, _ => return false

/-- Compare equal-length scrutinee prefixes -/
partial def convertScrutPrefix (ss1 ss2 : Array Value) (count : Nat) : TCM Bool := do
  if ss1.size < count || ss2.size < count then return false
  for _h : i in [:count] do
    let eq ← convert ss1[i]! ss2[i]!
    if !eq then return false
  return true

/-- Compare two values via syntactic-quote equality -/
partial def convertBodies (body1 body2 : Value) : TCM Bool := do
  let lvl ← TCM.currentLevel
  if Soma.Core.quoteExpr lvl body1 == Soma.Core.quoteExpr lvl body2 then
    pure true
  else
    convert body1 body2

/-- Same-shape stuck-case comparison -/
partial def compareHCaseSameShape
    (ss1 : Array Value) (as1 : List ArmClosure)
    (ss2 : Array Value) (as2 : List ArmClosure)
    (compareBodies : Value → Value → TCM Bool)
    : TCM Bool := do
  if ss1.size != ss2.size then return false
  let scrutsEq ← convertScrutPrefix ss1 ss2 ss1.size
  if !scrutsEq then return false
  if as1.length != as2.length then return false
  for (arm1, arm2) in as1.zip as2 do
    if arm1.patterns.size != arm2.patterns.size then return false
    let baseLvl ← TCM.currentLevel
    let aligned? :=
      alignPatternArraysWithRefinement arm1.patterns arm2.patterns ss1 baseLvl 0
    match aligned? with
    | none => return false
    | some (args1, args2, refinedVals, _) =>
      let body1 ← applyArmClosureSpineOpaque arm1.closure args1
      let body2 ← applyArmClosureSpineOpaque arm2.closure args2
      let body1 ← substValue (refinementSubstForScruts ss1 refinedVals) body1
      let body2 ← substValue (refinementSubstForScruts ss2 refinedVals) body2
      let bodiesEq ← compareBodies body1 body2
      if !bodiesEq then return false
  return true

/-- Commuting-conversion stuck-case comparison -/
partial def compareHCasePrefixExpansion
    (smallScruts : Array Value) (smallArms : List ArmClosure)
    (bigScruts : Array Value) (bigArms : List ArmClosure)
    (compareBodies : Value → Value → TCM Bool)
    : TCM Bool := do
  if smallArms.length != bigArms.length then return false
  for (smallArm, bigArm) in smallArms.zip bigArms do
    let prefixPatterns := smallArm.patterns.size
    if prefixPatterns >= bigArm.patterns.size then return false
    if bigArm.patterns.size != bigScruts.size then return false
    let bigPrefix := bigArm.patterns.extract 0 prefixPatterns
    let smallShapeOk :=
      smallScruts.size == prefixPatterns || smallScruts.size == bigScruts.size
    if !smallShapeOk then return false
    let scrutsEq ← convertScrutPrefix smallScruts bigScruts prefixPatterns
    if !scrutsEq then return false
    let extraArgs? := trivialExtraPatternArgs bigArm.patterns bigScruts prefixPatterns
    match extraArgs? with
    | none => return false
    | some extraPatternArgs =>
      let baseLvl ← TCM.currentLevel
      let prefixScruts := bigScruts.extract 0 prefixPatterns
      let aligned? := alignPatternArraysWithRefinement
        smallArm.patterns bigPrefix prefixScruts baseLvl 0
      match aligned? with
      | none => return false
      | some (smallPatternArgs, bigPrefixArgs, refinedVals, _) =>
        let extraScruts := bigScruts.extract prefixPatterns bigScruts.size
        let smallBody ← applyArmClosureSpineOpaque smallArm.closure smallPatternArgs
        let smallBody ← substValue (refinementSubstForScruts prefixScruts refinedVals) smallBody
        let smallBodyAdjusted? ←
          if smallScruts.size == bigScruts.size then
            pure (some smallBody)
          else
            applyValueArgsAsFunction? smallBody extraScruts
        match smallBodyAdjusted? with
        | none => return false
        | some smallBodyApplied =>
          let bigBody ← applyArmClosureSpineOpaque bigArm.closure (bigPrefixArgs ++ extraPatternArgs)
          let bigBody ← substValue (refinementSubstForScruts prefixScruts refinedVals) bigBody
          let bodiesEq ← compareBodies smallBodyApplied bigBody
          if !bodiesEq then return false
  return true

/-- Stuck-case structural comparison -/
partial def compareHCase
    (ss1 : Array Value) (as1 : List ArmClosure)
    (ss2 : Array Value) (as2 : List ArmClosure)
    (compareBodies : Value → Value → TCM Bool)
    : TCM Bool := do
  let same ← compareHCaseSameShape ss1 as1 ss2 as2 compareBodies
  if same then return true
  let leftSmall ← compareHCasePrefixExpansion ss1 as1 ss2 as2 compareBodies
  if leftSmall then return true
  compareHCasePrefixExpansion ss2 as2 ss1 as1 compareBodies

/-- Stuck-case definitional convertibility -/
partial def convertHCase
    (ss1 : Array Value) (as1 : List ArmClosure)
    (ss2 : Array Value) (as2 : List ArmClosure) : TCM Bool := do
  compareHCase ss1 as1 ss2 as2 convertBodies

/-- Check if two neutral heads are convertible -/
partial def convertHead (h1 h2 : Head) : TCM Bool := do
  match h1, h2 with
  | .hVar v1, .hVar v2 => return v1.level == v2.level
  | .hMeta m1, .hMeta m2 => return m1 == m2
  | .hConst c1 _, .hConst c2 _ => return c1 == c2
  | .hCase ss1 _m1 as1, .hCase ss2 _m2 as2 =>
    convertHCase ss1 as1 ss2 as2
  | _, _ => return false

/-- Check if two eliminators are convertible -/
partial def convertElim (e1 e2 : Elim) : TCM Bool := do
  match e1, e2 with
  | .eApp a1, .eApp a2 => convert a1 a2
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

/-- Resolve the unique type identifier for an inductive `record` declaration -/
partial def recordTypeId? (ty : Value) : TCM (Option Soma.Unique) := do
  let ty' ← force ty
  let ctx ← TCM.getCtx
  match ty' with
  | .vDataType uid _ =>
    match ctx.globals.lookupInductive ⟨uid⟩ with
    | some indMeta =>
      if indMeta.ctors.size == 1 && indMeta.fieldNames.size > 0 then
        return some uid
      else
        return none
    | none => return none
  | _ => return none

/-- Eta-expand a value of an inductive `record` type into a list of field projections -/
partial def recordEtaProjections (neu : Neutral) (fieldNames : Array String)
    : Array Value :=
  fieldNames.map fun field =>
    Value.vNeutral .type0 (neu.pushElim (.eField field))

/-- Record-eta convertibility -/
partial def recordEtaConvert
    (ctorArgs : List Value) (ctorRty : Value)
    (neuTy : Value) (neu : Neutral)
    (ctorOnLeft : Bool) : TCM Bool := do
  let some ctorTypeId ← recordTypeId? ctorRty | return false
  let some neuTypeId ← recordTypeId? neuTy | return false
  if ctorTypeId != neuTypeId then return false
  let ctx ← TCM.getCtx
  let some indMeta := ctx.globals.lookupInductive ⟨ctorTypeId⟩ | return false
  if ctorArgs.length != indMeta.fieldNames.size then return false
  let projections := recordEtaProjections neu indMeta.fieldNames
  let argsArr := ctorArgs.toArray
  for _h : i in [:argsArr.size] do
    let arg := argsArr[i]!
    let proj := projections[i]!
    let eq ← if ctorOnLeft then convert arg proj else convert proj arg
    if !eq then return false
  return true

end

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

end Soma.Dependent
