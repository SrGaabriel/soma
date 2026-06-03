import Soma.Dependent.Totality.Core

namespace Soma.Dependent.Totality

open Soma.Core
open Soma.Syntax (Span)

/-- Result of positivity check -/
inductive PositivityResult where
  | ok
  | violated (reason : String) (span : Span)
  deriving Repr, Inhabited

mutual

partial def checkSP (unique : Unique) (allowed : Bool) (v : Value) : PositivityResult :=
  match v with
  | .vType _ | .vIntLit _ | .vFloatLit _ | .vStringLit _
  | .vLabelLit _ | .vRowSort | .vLabelSort | .vRowEmpty => .ok
  | .vDataType id params =>
    if id == unique && !allowed then
      .violated "recursive type occurs to the left of '→' (not strictly positive)" Span.uninhabited
    else
      checkSPList unique allowed params
  | .vConstructor _ _ args _ => checkSPList unique allowed args
  | .vRecord row => checkSP unique allowed row
  | .vVariant row => checkSP unique allowed row
  | .vRowExtend label fieldTy tail => checkSPList unique allowed [label, fieldTy, tail]
  | .vRecordVal fields => checkSPList unique allowed (fields.map (·.2))
  | .vNeutral _ neu => checkSPNeutral unique allowed neu
  | .vLam _ dom body =>
    match checkSP unique allowed dom with
    | .violated reason span => .violated reason span
    | .ok => checkSPClosure unique allowed body
  | .vPi _ _ _ dom cod =>
    match checkSP unique false dom with
    | .violated reason span => .violated reason span
    | .ok => checkSPClosure unique allowed cod

partial def checkSPClosure (unique : Unique) (allowed : Bool) (clos : Closure) : PositivityResult :=
  match clos with
  | .const _ value => checkSP unique allowed value
  | .term name env body =>
    let freshVar := Value.vNeutral (Value.vType Level.zero) (.nVar ⟨name, ⟨env.size⟩⟩)
    let env' := env.extend name freshVar
    let evalCtx : EvalCtx := { env := env', globals := GlobalEnv.empty, metas := MetaState.empty }
    checkSP unique allowed (evalCoreExpr evalCtx body)

partial def checkSPList (unique : Unique) (allowed : Bool) : List Value → PositivityResult
  | [] => .ok
  | v :: rest =>
    match checkSP unique allowed v with
    | .violated reason span => .violated reason span
    | .ok => checkSPList unique allowed rest

partial def checkSPNeutral (unique : Unique) (allowed : Bool) (neu : Neutral) : PositivityResult :=
  match neu with
  | .mk head spine =>
    let spineArgs : List Value :=
      spine.foldr (fun e acc => match e with | .eApp a => a :: acc | .eField _ => acc) []
    match head with
    | .hCase scrutinees motive arms =>
      match checkSPList unique allowed (motive :: scrutinees.toList ++ spineArgs) with
      | .violated reason span => .violated reason span
      | .ok => checkSPArms unique allowed arms
    | _ => checkSPList unique allowed spineArgs

partial def checkSPArms (unique : Unique) (allowed : Bool) : List ArmClosure → PositivityResult
  | [] => .ok
  | arm :: rest =>
    match checkSPClosure unique allowed arm.closure with
    | .violated reason span => .violated reason span
    | .ok => checkSPArms unique allowed rest

end

/-- Walk the outer Pi chain of a constructor type -/
partial def checkConstructorType (unique : Unique) (ctorTy : Value) : PositivityResult :=
  match ctorTy with
  | .vPi _ _ _ dom cod =>
    match checkSP unique true dom with
    | .violated reason span => .violated reason span
    | .ok =>
      match cod with
      | .const _ rest => checkConstructorType unique rest
      | .term name env body =>
        let freshVar := Value.vNeutral dom (.nVar ⟨name, ⟨env.size⟩⟩)
        let env' := env.extend name freshVar
        let evalCtx : EvalCtx := { env := env', globals := GlobalEnv.empty, metas := MetaState.empty }
        checkConstructorType unique (evalCoreExpr evalCtx body)
  | _ => .ok

/-- Check strict positivity for a data type definition -/
def checkDataTypePositivity (unique : Unique) (constructors : Array Value)
    (span : Span) : PositivityResult :=
  constructors.foldl (init := PositivityResult.ok) fun acc ctorTy =>
    match acc with
    | .violated _ _ => acc
    | .ok =>
      match checkConstructorType unique ctorTy with
      | .violated reason _ => .violated reason span
      | .ok => .ok

/-- Check index value for totality -/
private partial def checkIndexValue (v : Value) (reg : TotalityRegistry) : List String :=
  match v with
  | .vNeutral _ neu => checkNeutral neu reg
  | .vConstructor _ _ args _ => args.flatMap (checkIndexValue · reg)
  | .vDataType _ params => params.flatMap (checkIndexValue · reg)
  | .vPi _ _ _ dom _ => checkIndexValue dom reg
  | .vRowExtend label ty tail =>
      checkIndexValue label reg ++ checkIndexValue ty reg ++ checkIndexValue tail reg
  | .vRecord row => checkIndexValue row reg
  | .vVariant row => checkIndexValue row reg
  | _ => []
where
  checkHead (h : Head) (reg : TotalityRegistry) : List String :=
    match h with
    | .hVar v =>
      match reg.lookup v.name with
      | some .isPartial => [v.name]
      | some .isUnknown => [v.name]
      | _ => []
    | .hConst _ _ => []
    | .hMeta _ => []
    | .hErrored => []
    | .hCase scrutinees motive _ =>
      scrutinees.foldl (fun acc s => acc ++ checkIndexValue s reg) [] ++
      checkIndexValue motive reg
  checkElim (e : Elim) (reg : TotalityRegistry) : List String :=
    match e with
    | .eApp arg => checkIndexValue arg reg
    | .eField _ => []
  checkNeutral (neu : Neutral) (reg : TotalityRegistry) : List String :=
    checkHead neu.head reg ++
      neu.spine.foldl (fun acc e => acc ++ checkElim e reg) []

end Soma.Dependent.Totality
