import Soma.Dependent.Totality.Core

namespace Soma.Dependent.Totality

open Soma.Core
open Soma.Metal (Name)
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

partial def checkPositivityClosure (typeId : TypeId) (pol : Polarity) (clos : Closure)
    (argTy : Value) : PositivityResult :=
  let freshVar := Value.vNeutral argTy (.nVar ⟨clos.name, ⟨clos.env.size⟩⟩)
  match clos.body with
  | some body =>
    let env' := clos.env.extend clos.name freshVar
    let evalCtx : EvalCtx := { env := env', globals := GlobalEnv.empty, metas := MetaState.empty }
    let bodyVal := evalTerm evalCtx body
    checkPositivityValue typeId pol bodyVal
  | none =>
    let envVals := clos.env.values.map (·.2)
    envVals.foldl (fun acc v =>
      match acc with
      | .violated _ _ => acc
      | .ok => checkPositivityValue typeId pol v
    ) .ok

partial def checkPositivityList (typeId : TypeId) (pol : Polarity)
    (values : List Value) : PositivityResult :=
  match values with
  | [] => .ok
  | v :: rest =>
    match checkPositivityValue typeId pol v with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityList typeId pol rest

partial def checkPositivityFields (typeId : TypeId) (pol : Polarity)
    (fields : List (String × Value)) : PositivityResult :=
  match fields with
  | [] => .ok
  | (_, v) :: rest =>
    match checkPositivityValue typeId pol v with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityFields typeId pol rest

partial def checkPositivityValue (typeId : TypeId) (pol : Polarity) (ty : Value) : PositivityResult :=
  match ty with
  | .vType _ => .ok
  | .vPrimTy _ => .ok
  | .vHigherPrim _ => .ok
  | .vIntLit _ => .ok
  | .vStringLit _ => .ok
  | .vLabelLit _ => .ok

  | .vDataType id params =>
    if id == typeId then
      match pol with
      | .positive => .ok
      | .negative => .violated "type appears in negative position" Span.uninhabited
      | .mixed => .violated "type appears in mixed position" Span.uninhabited
    else
      checkPositivityList typeId pol params

  | .vPi _ _ _ dom cod =>
    match checkPositivityValue typeId pol.flip dom with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityClosure typeId pol cod dom

  | .vSigma _ _ fst snd =>
    match checkPositivityValue typeId pol fst with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityClosure typeId pol snd fst

  | .vLam _ _ _ dom body =>
    match checkPositivityValue typeId pol.flip dom with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityClosure typeId pol body dom

  | .vPair a b =>
    match checkPositivityValue typeId pol a with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityValue typeId pol b

  | .vRowEmpty => .ok

  | .vRowExtend label fieldTy tail =>
    match checkPositivityValue typeId pol label with
    | .violated reason span => .violated reason span
    | .ok =>
      match checkPositivityValue typeId pol fieldTy with
      | .violated reason span => .violated reason span
      | .ok => checkPositivityValue typeId pol tail

  | .vRecord row => checkPositivityValue typeId pol row
  | .vVariant row => checkPositivityValue typeId pol row

  | .vConstructor _ _ args => checkPositivityList typeId pol args

  | .vNeutral _ _ => .ok

  | .vEq _ eqTy lhs rhs =>
    match checkPositivityValue typeId pol eqTy with
    | .violated reason span => .violated reason span
    | .ok =>
      match checkPositivityValue typeId pol lhs with
      | .violated reason span => .violated reason span
      | .ok => checkPositivityValue typeId pol rhs

  | .vRefl reflTy x =>
    match checkPositivityValue typeId pol reflTy with
    | .violated reason span => .violated reason span
    | .ok => checkPositivityValue typeId pol x

  | .vTransport _ transTy motive lhs rhs eq body =>
    match checkPositivityValue typeId pol transTy with
    | .violated reason span => .violated reason span
    | .ok =>
      match checkPositivityValue typeId pol motive with
      | .violated reason span => .violated reason span
      | .ok =>
        match checkPositivityValue typeId pol lhs with
        | .violated reason span => .violated reason span
        | .ok =>
          match checkPositivityValue typeId pol rhs with
          | .violated reason span => .violated reason span
          | .ok =>
            match checkPositivityValue typeId pol eq with
            | .violated reason span => .violated reason span
            | .ok => checkPositivityValue typeId pol body

  | .vRecordVal fields => checkPositivityFields typeId pol fields

end

/-- Check positivity for a data type definition -/
def checkDataTypePositivity (typeId : TypeId) (constructors : Array Value)
    (span : Span) : PositivityResult :=
  constructors.foldl (init := PositivityResult.ok) fun acc ctorTy =>
    match acc with
    | .violated _ _ => acc
    | .ok =>
      match checkPositivityValue typeId .positive ctorTy with
      | .violated reason _ => .violated reason span
      | .ok => .ok

/-- Check index value for totality -/
private partial def checkIndexValue (v : Value) (reg : TotalityRegistry) : List String :=
  match v with
  | .vNeutral _ neu => checkNeutral neu reg
  | .vPair a b => checkIndexValue a reg ++ checkIndexValue b reg
  | .vConstructor _ _ args => args.flatMap (checkIndexValue · reg)
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
    | .nCase scrut _ => checkNeutral scrut reg

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
    TCM.throw (.partialInTypeIndex (Name.user u) span)

/-- Check and report positivity for a data type definition -/
def checkAndReportPositivity (typeName : String) (typeId : TypeId)
    (constructorTypes : Array Value) (span : Span) : TCM Unit := do
  match checkDataTypePositivity typeId constructorTypes span with
  | .ok => pure ()
  | .violated reason violationSpan =>
    TCM.throw (.positivityViolation typeName reason violationSpan none)

end Soma.Dependent.Totality
