-- import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Primitive
import Soma.Core.Quote
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Error
import Soma.Syntax.Ast

namespace Soma.Dependent.Elaborate

open Soma.Core
open Soma.Syntax (TypeExpr Span)

/-- Environment for tracking type variables during elaboration -/
structure ElabEnv where
  /-- Type variables in scope: name -> (level, kind) -/
  tyVars : List (String × DeBruijnLvl × Value)
  /-- Current De Bruijn level -/
  level : Nat := 0
  /-- Value overrides: type variable name -> pre-allocated Value -/
  overrides : List (String × Value) := []
  deriving Inhabited

namespace ElabEnv

def empty : ElabEnv := { tyVars := [], level := 0, overrides := [] }

/-- Extend the environment with a new type variable -/
def extend (env : ElabEnv) (name : String) (kind : Value) : ElabEnv :=
  { env with
    tyVars := (name, ⟨env.level⟩, kind) :: env.tyVars
  , level := env.level + 1
  }

/-- Add a value override for a type variable name -/
def addOverride (env : ElabEnv) (name : String) (val : Value) : ElabEnv :=
  { env with overrides := (name, val) :: env.overrides }

/-- Look up a type variable by name -/
def lookup (env : ElabEnv) (name : String) : Option (DeBruijnLvl × Value) :=
  env.tyVars.find? (·.1 == name) |>.map (fun (_, lvl, k) => (lvl, k))

/-- Look up a value override by name -/
def lookupOverride (env : ElabEnv) (name : String) : Option Value :=
  env.overrides.find? (·.1 == name) |>.map (·.2)

end ElabEnv

/-- Resolve "Type" to a universe -/
def resolveType (name : String) : Option Value :=
  if name == "Type" then some (Value.vType Level.zero)
  else if name == "Type0" then some (Value.vType Level.zero)
  else if name == "Type1" then some (Value.vType Level.one)
  else if name == "Row" then some Value.vRowSort
  else if name == "Label" then some Value.vLabelSort
  else none

/-- Create an empty closure from the current environment -/
def mkElabClosure (name : String) : TCM Closure := do
  let env ← TCM.getEnv
  return Closure.mkEmpty name env

/-- Quote a value to an Expr at a given depth (pure, no TCM needed) -/
def quoteValue (v : Value) (depth : Nat) : Soma.Core.Expr :=
  quoteExpr ⟨depth⟩ v

/-- Create a closure that returns a constant value (for non-dependent types).
    Uses HOAS-style representation: stores the result Value directly instead of
    converting to an Expr. This eliminates De Bruijn index bugs for non-dependent types.
    The depth parameter is kept for API compatibility but is ignored. -/
def mkConstClosureWithDepth (name : String) (result : Value) (_depth : Nat) : TCM Closure := do
  return Closure.const name result

/-- Create a closure that returns a constant value (for non-dependent types) -/
def mkConstClosure (name : String) (result : Value) : TCM Closure := do
  return Closure.const name result

/-- Convert an ElabEnv to an evaluation Env by extracting variable bindings.
    Each type variable in ElabEnv becomes a neutral variable in the Env.

    Env stores bindings with newest at front, oldest at back.
    ElabEnv.tyVars is also newest first (via cons in extend).
    Env.lookup uses: idx = size - level - 1
      - level 0 → idx = size-1 → last element (oldest)
      - level size-1 → idx = 0 → first element (newest)
    So we keep tyVars order as-is (newest first = front of list). -/
def elabEnvToEnv (elabEnv : ElabEnv) : Env :=
  -- tyVars is already in correct order: newest first
  let bindings := elabEnv.tyVars.map fun (name, lvl, kind) =>
    (name, Value.vNeutral kind (Neutral.nVar ⟨name, lvl⟩))
  Env.mk bindings elabEnv.level

/-- Create a term-based closure for dependent types.
    Quotes the result Value to an Expr and creates a closure that will
    evaluate it with the argument bound.

    The key insight from defunctionalized NbE: we must capture the current
    environment so that outer variable bindings are preserved. The Expr uses
    De Bruijn indices relative to this captured environment.

    The `elabEnv` is the current elaboration environment with outer bindings.
    The `depth` is the total number of binders (= elabEnv.level). -/
def mkDependentClosure (name : String) (result : Value) (elabEnv : ElabEnv) : TCM Closure := do
  let depth := elabEnv.level
  -- Convert ElabEnv to evaluation Env
  let env := elabEnvToEnv elabEnv
  -- Quote the result Value to an Expr.
  -- IMPORTANT: Use depth + 1 because when the closure is applied, the environment
  -- will be extended with one more binding (the closure's parameter).
  -- De Bruijn index = (depth + 1) - varLevel - 1 = depth - varLevel
  -- This ensures indices point to the correct bindings after extension.
  let bodyExpr := quoteValue result (depth + 1)
  -- Create a closure capturing the environment
  -- When applied, the argument will be added to this environment
  return Closure.term name env bodyExpr

/-- Rebuild a row with a new tail -/
partial def rebuildRowWithTail (row : Value) (newTail : Value) : Value :=
  match row with
  | .vRowEmpty => newTail
  | .vRowExtend label ty tail =>
    .vRowExtend label ty (rebuildRowWithTail tail newTail)
  | other => other -- If it's already a variable/meta, just return it

/-- Elaborate a type expression to a Value -/
partial def elaborateType (env : ElabEnv) (ty : TypeExpr) : TCM Value := do
  match ty with
  -- Type variable
  | .var name =>
    match env.lookup name.name with
    | some (lvl, kind) =>
      -- Return a neutral variable
      return Value.vNeutral kind (Neutral.nVar ⟨name.name, lvl⟩)
    | none =>
      -- Check for a pre-allocated value override (used by instance elaboration to share metavariables across type args and constraints)
      match env.lookupOverride name.name with
      | some val => return val
      | none =>
        TCM.freshMetaVal (Value.vType Level.zero)

  -- Type constructor (uppercase identifier)
  | .con name =>
    -- Try Type/Row/Label sort names first (builtins)
    if let some tyVal := resolveType name.name then
      return tyVal
    -- Resolve through the namespace tree
    else match ← TCM.resolve name.path name.name with
    | some qn =>
      -- Check if it's a type abbreviation
      if let some abbrevInfo ← TCM.lookupAbbrev qn then
        return abbrevInfo.expansion
      -- Check globals for constructors/types
      else if let some globalInfo ← TCM.lookupGlobal name.path name.name then
        if globalInfo.isConstructor then
          return Value.vConstructor globalInfo.name globalInfo.ctorTag [] globalInfo.type
        else
          if let some primTy ← TCM.lookupWiredPrimitiveOfGlobal globalInfo.name then
            if primTy.isNullary then
              return Value.vPrimTy primTy
            else
              return Value.vDataType globalInfo.name.id []
          else
            return Value.vDataType globalInfo.name.id []
      else
        return Value.vDataType qn.id []
    | none =>
      TCM.throw (.cannotInfer
        s!"unknown type constructor `{name.name}` (no builtin/intrinsic binding in context)"
        name.span
        none)

  -- Type application: F A
  | .app fn arg span =>
    let fnVal ← elaborateType env fn
    let argVal ← elaborateType env arg
    -- Apply the type function to the argument
    match fnVal with
    | .vDataType id params =>
      -- Accumulate type parameters for data types
      return Value.vDataType id (params ++ [argVal])
    | .vConstructor name tag args rty =>
      -- Constructor application in type position
      -- Accumulate arguments to the constructor
      return Value.vConstructor name tag (args ++ [argVal]) rty
    | .vPi _ _ _ _ cod =>
      -- Apply function type - evaluate the closure with TCM's applyClosure
      Soma.Dependent.applyClosure cod argVal
    | .vNeutral ty neu =>
      -- Stuck application; if the function kind is Pi, compute codomain kind.
      let resultTy ← match ty with
        | .vPi _ _ _ _ cod => Soma.Dependent.applyClosure cod argVal
        | _ => pure ty
      return Value.vNeutral resultTy (Neutral.nApp neu argVal)
    | _ =>
      TCM.throw (.cannotInfer s!"cannot apply non-function type" span none)

  -- Arrow type: A -> B (non-dependent function)
  | .arrow from_ to _ =>
    let fromVal ← elaborateType env from_
    let toVal ← elaborateType env to
    -- Arrow codomains are non-dependent on the arrow binder itself.
    return Value.vPi .omega .explicit "_" fromVal (Closure.const "_" toVal)

  -- Tuple type: (A, B, C) -> nested Sigma types
  | .tuple elements _ =>
    if elements.isEmpty then
      return Value.vPrimTy .unit
    else if h : elements.size = 1 then
      elaborateType env elements[0]
    else
      -- Convert to nested pairs: (A, B, C) -> (A × (B × C))
      -- Build right-to-left so (A, B, C) becomes Sigma A (Sigma B C)
      let vals ← elements.toList.mapM (elaborateType env)
      match vals.reverse with
      | [] => return Value.vPrimTy .unit
      | [v] => return v
      | last :: rest =>
        -- Build from the end: start with last element, wrap in Sigmas
        -- Tuple Sigmas are non-dependent, so use const closures
        let result ← rest.foldlM (init := last) fun acc elem => do
          return Value.vSigma .omega "_" elem (Closure.const "_" acc)
        return result

  -- List type: [A]
  | .list elem span =>
    let elemVal ← elaborateType env elem
    match ← TCM.lookupWiredIn .typeList with
    | some info =>
      return Value.vDataType info.name.id [elemVal]
    | none =>
      TCM.throw (.unboundGlobal "List (no @[wired_in \"type.list\"] type in scope)" span #[])

  -- Universal quantification: forall a b. T
  | .forall_ vars body _ =>
    -- For forall quantifiers, we need proper closures because
    -- the body references the bound type variables.

    -- First, elaborate the body in an extended environment with all type vars
    let env' ← vars.foldlM (init := env) fun acc v => do
      let kind ← match v.kind with
        | some k => elaborateType acc k
        | none => pure (Value.vType Level.zero)
      return acc.extend v.name.name kind

    let bodyVal ← elaborateType env' body

    -- Quote the body Value to an Expr
    -- The depth must be the FULL environment level (env'.level), not just vars.size,
    -- because the body may reference outer type variables (like `f` in a trait method).
    let bodyExpr := quoteValue bodyVal env'.level

    -- Build nested Pi types from right to left using Expr representation
    -- For `forall a b. T`, we build: Π{a:*}. Π{b:*}. T[indices adjusted]
    let mut accExpr := bodyExpr
    for v in vars.toList.reverse do
      let kind ← match v.kind with
        | some k => elaborateType env k
        | none => pure (Value.vType Level.zero)
      let kindExpr := quoteValue kind env.level
      accExpr := Soma.Core.Expr.pi .omega .implicit v.name.name kindExpr accExpr

    TCM.evalExprInEnv (elabEnvToEnv env) accExpr

  -- Constrained type: T with (C1, C2)
  | .constrained constraints body _ =>
    -- Elaborate the body first
    let bodyVal ← elaborateType env body
    -- For each constraint, wrap in an implicit instance argument
    -- (Show a) => becomes {{Show a}} ->
    -- Constraints don't introduce new bound variables that the body depends on,
    -- so we use const closures here (the body doesn't reference the instance arg)
    let result ← constraints.foldrM (init := bodyVal) fun (className, args, classSpan) acc => do
      -- Elaborate constraint arguments
      let argVals ← args.toList.mapM (elaborateType env)
      -- Create the constraint type (e.g., Show Int)
      let classQN ← match ← TCM.resolve #[] className.name with
        | some qn => pure qn
        | none =>
          TCM.throw (.unboundGlobal s!"{className.name} (unknown type class)" classSpan #[])
      let constraintTy := Value.vDataType classQN.id argVals
      -- Use const closure since the body doesn't depend on the instance parameter
      return Value.vPi .omega .instance_ "_" constraintTy (Closure.const "_" acc)
    return result

  -- Parenthesized type
  | .parens inner _ =>
    elaborateType env inner

  -- Kind annotation: T :: K (we just elaborate T, ignoring K for now)
  | .kinded inner _ _ =>
    -- Could check that elaborated type has the expected kind
    elaborateType env inner

  -- Record type: { x :: Int, y :: Bool }
  | .record fields tail _ =>
    -- Build row type from fields
    let mut row := Value.vRowEmpty
    for (name, fieldTy) in fields.toList.reverse do
      let tyVal ← elaborateType env fieldTy
      -- Check if the field name is a bound label variable (for label polymorphism)
      -- If so, use the variable reference; otherwise use a literal label
      let labelVal := match env.lookup name.name with
        | some (lvl, _) =>
          -- Field name is a bound variable - use as label variable
          Value.vNeutral Value.vLabelSort (Neutral.nVar ⟨name.name, lvl⟩)
        | none =>
          -- Field name is a literal label
          Value.vLabelLit name.name
      row := Value.vRowExtend labelVal tyVal row
    -- Handle row tail (for polymorphism)
    -- The tail represents a row variable that can be unified with other rows
    match tail with
    | some tailName =>
      match env.lookup tailName.name with
      | some (lvl, _) =>
        -- The tail is a known row variable - use it directly as the row tail
        -- (not as a labeled field, but as the actual tail of the row)
        let tailVar := Value.vNeutral Value.vRowSort (Neutral.nVar ⟨tailName.name, lvl⟩)
        -- Properly concatenate: prepend our fields to the tail row
        -- We need to rebuild the row with the tail as the base
        row := rebuildRowWithTail row tailVar
      | none =>
        -- Unknown tail variable - create metavariable for the tail
        let tailMeta ← TCM.freshMetaVal Value.vRowSort
        row := rebuildRowWithTail row tailMeta
    | none => pure ()
    return Value.vRecord row

  -- Variant type: < Ok :: Int | Err :: String >
  | .variant cases tail _ =>
    -- Build row type from cases
    let mut row := Value.vRowEmpty
    for (name, caseTy) in cases.toList.reverse do
      let tyVal ← elaborateType env caseTy
      -- Check if the case name is a bound label variable (for label polymorphism)
      let labelVal := match env.lookup name.name with
        | some (lvl, _) =>
          Value.vNeutral Value.vLabelSort (Neutral.nVar ⟨name.name, lvl⟩)
        | none =>
          Value.vLabelLit name.name
      row := Value.vRowExtend labelVal tyVal row
    -- Handle row tail (for polymorphism)
    match tail with
    | some tailName =>
      match env.lookup tailName.name with
      | some (lvl, _) =>
        let tailVar := Value.vNeutral Value.vRowSort (Neutral.nVar ⟨tailName.name, lvl⟩)
        row := rebuildRowWithTail row tailVar
      | none =>
        let tailMeta ← TCM.freshMetaVal Value.vRowSort
        row := rebuildRowWithTail row tailMeta
    | none => pure ()
    return Value.vVariant row

  -- Dependent function type (Pi): (q x : A) -> B
  | .pi qty name domain codomain _ =>
    let domVal ← elaborateType env domain
    -- Extend env with the bound variable for the codomain
    let env' := env.extend name.name domVal
    let codVal ← elaborateType env' codomain
    -- Create a term-based closure for dependent substitution
    -- IMPORTANT: Pass env (not env') - the closure should NOT capture its own parameter.
    -- When applied, the closure will be extended with the argument.
    let codClosure ← mkDependentClosure name.name codVal env
    return Value.vPi qty .explicit name.name domVal codClosure

  -- Dependent pair type (Sigma): (x : A) × B
  | .sigma qty name fst snd _ =>
    let fstVal ← elaborateType env fst
    let env' := env.extend name.name fstVal
    let sndVal ← elaborateType env' snd
    -- Create a term-based closure for dependent substitution
    -- Pass env (not env') - the closure should NOT capture its own parameter.
    let sndClosure ← mkDependentClosure name.name sndVal env
    return Value.vSigma qty name.name fstVal sndClosure

  -- Instance-implicit parameter: {{x : A}} -> B
  -- Uses BinderInfo.instance_ so that instance resolution kicks in
  | .implicit name domain codomain _ =>
    let domVal ← elaborateType env domain
    let bindName := name.map (·.name) |>.getD "_"
    let env' := env.extend bindName domVal
    let codVal ← elaborateType env' codomain
    -- Create a term-based closure for dependent substitution
    -- Pass env (not env') - the closure should NOT capture its own parameter.
    let codClosure ← mkDependentClosure bindName codVal env
    return Value.vPi .omega .instance_ bindName domVal codClosure

/-! ## Function Signature Elaboration -/

/-- Elaborate a function's declared type signature.
    Returns the elaborated type as a Value, or creates fresh metavariables
    for functions without signatures. -/
def elaborateSignature (sig : Option TypeExpr) (paramNames : Array String)
    : TCM Value := do
  match sig with
  | some tyExpr =>
    elaborateType ElabEnv.empty tyExpr
  | none =>
    -- No signature: create a function type with metavariables
    -- For each parameter, create ?A_i, then ?Result
    let mut ty ← TCM.freshMetaVal (Value.vType Level.zero)
    for name in paramNames.reverse do
      let paramTy ← TCM.freshMetaVal (Value.vType Level.zero)
      let codClosure ← mkConstClosure name ty
      ty := Value.vPi .omega .explicit name paramTy codClosure
    return ty

/-- Elaborate a data type definition's constructor types for positivity checking -/
def elaborateConstructorTypes (typeName : String) (params : Array String)
    (constructors : Array (String × Array TypeExpr)) : TCM (Array Value) := do
  -- Create environment with type parameters
  let env := params.foldl (fun acc p =>
    acc.extend p (Value.vType Level.zero)
  ) ElabEnv.empty

  -- Elaborate each constructor's field types
  constructors.mapM fun (_, fieldTys) => do
    -- For positivity, we care about the function type from fields to result
    let unique ← match ← TCM.resolve #[] typeName with
      | some qn => pure qn.id
      | none => TCM.freshUnique typeName
    let mut ty := Value.vDataType unique []
    for fieldTy in fieldTys.reverse do
      let fieldVal ← elaborateType env fieldTy
      let codClosure ← mkConstClosure "_" ty
      ty := Value.vPi .omega .explicit "_" fieldVal codClosure
    return ty

end Soma.Dependent.Elaborate
