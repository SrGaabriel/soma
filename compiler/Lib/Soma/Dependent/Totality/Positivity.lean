import Soma.Dependent.Totality.Core

namespace Soma.Dependent.Totality

open Soma.Core
open Soma.Syntax (Span)

/-- Polarity for positivity checking -/
inductive Polarity where
  | positive
  | negative
  | mixed
  deriving Repr, BEq, Inhabited

def Polarity.flip : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive
  | .mixed => .mixed

/-- Result of positivity check -/
inductive PositivityResult where
  | ok
  | violated (reason : String) (span : Span)
  deriving Repr, Inhabited

mutual

partial def checkPositivityClosure (unique : Unique) (pol : Polarity) (clos : Closure)
    (argTy : Value) : PositivityResult :=
  let freshVar := Value.vNeutral argTy (.nVar ⟨clos.name, ⟨clos.env.size⟩⟩)
  match clos.body with
  | some body =>
    let env' := clos.env.extend clos.name freshVar
    let evalCtx : EvalCtx := { env := env', globals := GlobalEnv.empty, metas := MetaState.empty }
    let bodyVal := evalCoreExpr evalCtx body
    checkPositivityValue unique pol bodyVal
  | none =>
    let envVals := clos.env.values.map (·.2)
    envVals.foldl (fun acc v =>
      match acc with
      | .violated _ _ => acc
      | .ok => checkPositivityValue unique pol v
    ) .ok

partial def checkPositivityList (unique : Unique) (pol : Polarity)
    (values : List Value) : PositivityResult :=
  match values with
  | [] => .ok
  | v :: rest =>
    match checkPositivityValue unique pol v with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityList unique pol rest

partial def checkPositivityFields (unique : Unique) (pol : Polarity)
    (fields : List (String × Value)) : PositivityResult :=
  match fields with
  | [] => .ok
  | (_, v) :: rest =>
    match checkPositivityValue unique pol v with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityFields unique pol rest

partial def checkPositivityValue (unique : Unique) (pol : Polarity) (ty : Value) : PositivityResult :=
  match ty with
  | .vType _ => .ok
  | .vPrimTy _ => .ok
  | .vIntLit _ => .ok
  | .vStringLit _ => .ok
  | .vLabelLit _ => .ok
  | .vRowSort | .vLabelSort => .ok

  | .vDataType id params =>
    if id == unique then
      match pol with
      | .positive => .ok
      | .negative => .violated "type appears in negative position" Span.uninhabited
      | .mixed => .violated "type appears in mixed position" Span.uninhabited
    else
      checkPositivityList unique pol params

  | .vPi _ _ _ dom cod =>
    match checkPositivityValue unique pol.flip dom with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityClosure unique pol cod dom

  | .vSigma _ _ fst snd =>
    match checkPositivityValue unique pol fst with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityClosure unique pol snd fst

  | .vLam _ body =>
    checkPositivityClosure unique pol body (.vType .zero)

  | .vPair a b =>
    match checkPositivityValue unique pol a with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityValue unique pol b

  | .vRowEmpty => .ok

  | .vRowExtend label fieldTy tail =>
    match checkPositivityValue unique pol label with
    | .violated reason span => .violated reason span
    | .ok =>
      match checkPositivityValue unique pol fieldTy with
      | .violated reason span => .violated reason span
      | .ok => checkPositivityValue unique pol tail

  | .vRecord row => checkPositivityValue unique pol row
  | .vVariant row => checkPositivityValue unique pol row

  | .vConstructor _ _ args _ => checkPositivityList unique pol args

  | .vNeutral _ _ => .ok

  | .vEq _ eqTy lhs rhs =>
    match checkPositivityValue unique pol eqTy with
    | .violated reason span => .violated reason span
    | .ok =>
      match checkPositivityValue unique pol lhs with
      | .violated reason span => .violated reason span
      | .ok => checkPositivityValue unique pol rhs

  | .vRefl reflTy x =>
    match checkPositivityValue unique pol reflTy with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityValue unique pol x

  | .vTransport _ transTy motive lhs rhs eq body =>
    match checkPositivityValue unique pol transTy with
    | .violated reason span => .violated reason span
    | .ok =>
      match checkPositivityValue unique pol motive with
      | .violated reason span => .violated reason span
      | .ok =>
        match checkPositivityValue unique pol lhs with
        | .violated reason span => .violated reason span
        | .ok =>
          match checkPositivityValue unique pol rhs with
          | .violated reason span => .violated reason span
          | .ok =>
            match checkPositivityValue unique pol eq with
            | .violated reason span => .violated reason span
            | .ok => checkPositivityValue unique pol body

  | .vRecordVal fields => checkPositivityFields unique pol fields

end

/-- Check positivity for a data type definition -/
def checkDataTypePositivity (unique : Unique) (constructors : Array Value)
    (span : Span) : PositivityResult :=
  constructors.foldl (init := PositivityResult.ok) fun acc ctorTy =>
    match acc with
    | .violated _ _ => acc
    | .ok =>
      match checkPositivityValue unique .positive ctorTy with
      | .violated reason _ => .violated reason span
      | .ok => .ok

/-- Check index value for totality -/
private partial def checkIndexValue (v : Value) (reg : TotalityRegistry) : List String :=
  match v with
  | .vNeutral _ neu => checkNeutral neu reg
  | .vPair a b => checkIndexValue a reg ++ checkIndexValue b reg
  | .vConstructor _ _ args _ => args.flatMap (checkIndexValue · reg)
  | .vDataType _ params => params.flatMap (checkIndexValue · reg)
  | .vPi _ _ _ dom _ => checkIndexValue dom reg
  | .vSigma _ _ fst _ => checkIndexValue fst reg
  | .vRowExtend label ty tail =>
      checkIndexValue label reg ++ checkIndexValue ty reg ++ checkIndexValue tail reg
  | .vRecord row => checkIndexValue row reg
  | .vVariant row => checkIndexValue row reg
  | .vEq _ ty lhs rhs =>
      checkIndexValue ty reg ++ checkIndexValue lhs reg ++ checkIndexValue rhs reg
  | _ => []
where
  checkNeutral (neu : Neutral) (reg : TotalityRegistry) : List String :=
    match neu with
    | .nVar v =>
      match reg.lookup v.name with
      | some .isPartial => [v.name]
      | some .isUnknown => [v.name]
      | _ => []
    | .nMeta _ => []
    | .nApp fn arg => checkNeutral fn reg ++ checkIndexValue arg reg
    | .nFst pair => checkNeutral pair reg
    | .nSnd pair => checkNeutral pair reg
    | .nFieldAccess rec _ => checkNeutral rec reg
    | .nCase scrut _ _ => checkNeutral scrut reg

/-- Check that a type index only uses total functions -/
def checkTypeIndexTotality (idx : Value) (registry : TotalityRegistry) : List String :=
  checkIndexValue idx registry

/-- Validate a type index (TCM version) -/
def validateTypeIndex (idx : Value) (registry : TotalityRegistry) (span : Span) : TCM Unit := do
  let partials := checkTypeIndexTotality idx registry
  match partials with
  | [] => pure ()
  | name :: _ =>
    let u ← TCM.freshUnique name
    TCM.throw (.partialInTypeIndex ⟨u⟩ span)

/-- Check and report positivity for a data type definition -/
def checkAndReportPositivity (typeName : String) (unique : Unique)
    (constructorTypes : Array Value) (span : Span) : TCM Unit := do
  match checkDataTypePositivity unique constructorTypes span with
  | .ok => pure ()
  | .violated reason violationSpan =>
    TCM.throw (.positivityViolation typeName reason violationSpan none)

end Soma.Dependent.Totality
