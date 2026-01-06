import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Primitive
import Soma.Core.TypeId
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Error
import Soma.Syntax.Ast

namespace Soma.Dependent.Elaborate

open Soma.Core
open Soma.Syntax (TypeExpr KindExpr Span)

/-- Environment for tracking type variables during elaboration -/
structure ElabEnv where
  /-- Type variables in scope: name -> (level, kind) -/
  tyVars : List (String × DeBruijnLvl × Value)
  /-- Current De Bruijn level -/
  level : Nat := 0
  deriving Inhabited

namespace ElabEnv

def empty : ElabEnv := { tyVars := [], level := 0 }

/-- Extend the environment with a new type variable -/
def extend (env : ElabEnv) (name : String) (kind : Value) : ElabEnv :=
  { tyVars := (name, ⟨env.level⟩, kind) :: env.tyVars
  , level := env.level + 1
  }

/-- Look up a type variable by name -/
def lookup (env : ElabEnv) (name : String) : Option (DeBruijnLvl × Value) :=
  env.tyVars.find? (·.1 == name) |>.map (fun (_, lvl, k) => (lvl, k))

end ElabEnv

/-- Resolve a type constructor name to a primitive type (todo: find where the fuck was the original bc i swear this was already done) -/
def resolvePrimitive (name : String) : Option StarPrimitive :=
  match name with
  | "Int" => some .int
  | "Long" => some .long
  | "Short" => some .short
  | "Byte" => some .byte
  | "String" => some .string
  | "Bool" => some .bool
  | "Float" => some .float
  | "Double" => some .double
  | "Unit" => some .unit
  | "Int8" => some .int8
  | "Int16" => some .int16
  | "Int32" => some .int32
  | "Int64" => some .int64
  | "Word8" => some .word8
  | "Word16" => some .word16
  | "Word32" => some .word32
  | "Word64" => some .word64
  | _ => none

/-- Resolve a higher-kinded primitive type -/
def resolveHigherPrimitive (name : String) : Option HigherPrimitive :=
  match name with
  | "IO" => some .io
  | "Array" => some .array
  | "List" => some .list
  | "Ref" => some .ref
  | "Ptr" => some .ptr
  | _ => none

/-- Resolve "Type" to a universe -/
def resolveType (name : String) : Option Value :=
  if name == "Type" then some (Value.vType Level.zero)
  else if name == "Type0" then some (Value.vType Level.zero)
  else if name == "Type1" then some (Value.vType Level.one)
  else none

/-- Create an empty closure from the current environment -/
def mkElabClosure (name : String) : TCM Closure := do
  let env ← TCM.getEnv
  return Closure.mkEmpty name env

/-- Convert a Value to a Term (for use in closures).
    This handles the common cases needed for type elaboration.
    Uses TCM to generate proper unique identifiers when needed.
    The depth parameter represents the number of binders we're inside relative
    to the closure body we're building. -/
partial def valueToTermWithDepth (v : Value) (depth : Nat) : TCM Term := do
  match v with
  | .vType level => return .type level
  | .vPrimTy p => return .primTy p
  | .vHigherPrim p => return .higherPrimTy p
  | .vIntLit n => return .intLit n
  | .vStringLit s => return .stringLit s
  | .vRowEmpty => return .rowEmpty
  | .vRowExtend label fieldTy tail =>
    let labelTerm ← valueToTermWithDepth label depth
    let fieldTyTerm ← valueToTermWithDepth fieldTy depth
    let tailTerm ← valueToTermWithDepth tail depth
    return .rowExtend labelTerm fieldTyTerm tailTerm
  | .vRecord row =>
    let rowTerm ← valueToTermWithDepth row depth
    return .recordTy rowTerm
  | .vVariant row =>
    let rowTerm ← valueToTermWithDepth row depth
    return .variantTy rowTerm
  | .vLabelLit name => return .labelLit name
  | .vPi qty binder name dom cod =>
    let domTerm ← valueToTermWithDepth dom depth
    -- For the codomain, we need to apply the closure to get a value, then convert
    -- Use a fresh variable at the current depth level
    let dummyArg := Value.vNeutral dom (.nVar ⟨name, ⟨depth⟩⟩)
    let codVal ← Soma.Dependent.applyClosure cod dummyArg
    -- Increment depth since we're going under a binder
    let codTerm ← valueToTermWithDepth codVal (depth + 1)
    return .pi qty binder name domTerm codTerm
  | .vSigma qty name fst snd =>
    let fstTerm ← valueToTermWithDepth fst depth
    let dummyArg := Value.vNeutral fst (.nVar ⟨name, ⟨depth⟩⟩)
    let sndVal ← Soma.Dependent.applyClosure snd dummyArg
    let sndTerm ← valueToTermWithDepth sndVal (depth + 1)
    return .sigma qty name fstTerm sndTerm
  | .vDataType id params =>
    -- Use the existing TypeId's unique - don't generate a new one!
    -- Reconstruct the Unique from TypeId fields
    let unique : Unique := { id := id.unique, module := id.module, original := id.name }
    let baseTerm := Term.global (Name.user unique)
    let paramTerms ← params.mapM (valueToTermWithDepth · depth)
    return paramTerms.foldl (fun acc p => .app acc [p]) baseTerm
  | .vNeutral _ (.nVar v) =>
    -- Convert De Bruijn level to De Bruijn index
    -- index = depth - varLevel - 1
    -- depth is like the "current level" within the Term we're building
    let idx := depth - v.level.lvl - 1
    return .var idx v.name
  | .vNeutral _ (.nMeta m) => return .mvar m.id
  | .vNeutral ty (.nApp fn arg) =>
    -- Handle neutral application
    let fnTerm ← valueToTermWithDepth (.vNeutral ty fn) depth
    let argTerm ← valueToTermWithDepth arg depth
    return .app fnTerm [argTerm]
  | .vNeutral ty (.nFst inner) =>
    let innerTerm ← valueToTermWithDepth (.vNeutral ty inner) depth
    return .fst innerTerm
  | .vNeutral ty (.nSnd inner) =>
    let innerTerm ← valueToTermWithDepth (.vNeutral ty inner) depth
    return .snd innerTerm
  | .vNeutral ty (.nFieldAccess inner field) =>
    let innerTerm ← valueToTermWithDepth (.vNeutral ty inner) depth
    return .fieldAccess innerTerm field
  | .vEq tyLevel ty lhs rhs =>
    let tyTerm ← valueToTermWithDepth ty depth
    let lhsTerm ← valueToTermWithDepth lhs depth
    let rhsTerm ← valueToTermWithDepth rhs depth
    return .eq tyLevel tyTerm lhsTerm rhsTerm
  | .vRefl ty x =>
    let tyTerm ← valueToTermWithDepth ty depth
    let xTerm ← valueToTermWithDepth x depth
    return .refl tyTerm xTerm
  | .vTransport tyLevel ty motive lhs rhs eq body =>
    let tyTerm ← valueToTermWithDepth ty depth
    let motiveTerm ← valueToTermWithDepth motive depth
    let lhsTerm ← valueToTermWithDepth lhs depth
    let rhsTerm ← valueToTermWithDepth rhs depth
    let eqTerm ← valueToTermWithDepth eq depth
    let bodyTerm ← valueToTermWithDepth body depth
    return .transport tyLevel tyTerm motiveTerm lhsTerm rhsTerm eqTerm bodyTerm
  | .vConstructor name tag args =>
    let argTerms ← args.mapM (valueToTermWithDepth · depth)
    return .construct name tag argTerms
  | .vPair fst snd =>
    let fstTerm ← valueToTermWithDepth fst depth
    let sndTerm ← valueToTermWithDepth snd depth
    return .pair fstTerm sndTerm
  | .vRecordVal fields =>
    let fieldTerms ← fields.mapM fun (n, v) => do
      let term ← valueToTermWithDepth v depth
      return (n, term)
    return .record fieldTerms
  | .vLam _qty _binder name dom body =>
    -- Apply the closure to get the body, then convert
    let dummyArg := Value.vNeutral dom (.nVar ⟨name, ⟨depth⟩⟩)
    let bodyVal ← Soma.Dependent.applyClosure body dummyArg
    let bodyTerm ← valueToTermWithDepth bodyVal (depth + 1)
    return .lam [name] bodyTerm
  | .vNeutral _ (.nCase scrut arms) =>
    -- Handle neutral case expressions
    let scrutTerm ← valueToTermWithDepth (.vNeutral .type0 scrut) depth
    let armTerms ← arms.mapM fun arm => do
      let dummyArg := Value.vNeutral .type0 (.nVar ⟨"_", ⟨depth⟩⟩)
      let bodyVal ← Soma.Dependent.applyClosure arm.closure dummyArg
      let bodyTerm ← valueToTermWithDepth bodyVal (depth + 1)
      return (arm.pattern, 0, bodyTerm)
    return .case scrutTerm armTerms

/-- Convert a Value to a Term (for use in closures). Uses depth 0 as default. -/
def valueToTerm (v : Value) : TCM Term := valueToTermWithDepth v 0

/-- Create a closure that returns a constant value (for non-dependent types).
    Uses HOAS-style representation: stores the result Value directly instead of
    converting to a Term. This eliminates De Bruijn index bugs for non-dependent types.
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
    Converts the result Value back to a Term and creates a closure that will
    evaluate it with the argument bound.

    The key insight from defunctionalized NbE: we must capture the current
    environment so that outer variable bindings are preserved. The Term uses
    De Bruijn indices relative to this captured environment.

    The `elabEnv` is the current elaboration environment with outer bindings.
    The `depth` is the total number of binders (= elabEnv.level). -/
def mkDependentClosure (name : String) (result : Value) (elabEnv : ElabEnv) : TCM Closure := do
  let depth := elabEnv.level
  -- Convert ElabEnv to evaluation Env
  let env := elabEnvToEnv elabEnv
  -- Convert the result Value to a Term.
  -- IMPORTANT: Use depth + 1 because when the closure is applied, the environment
  -- will be extended with one more binding (the closure's parameter).
  -- De Bruijn index = (depth + 1) - varLevel - 1 = depth - varLevel
  -- This ensures indices point to the correct bindings after extension.
  let bodyTerm ← valueToTermWithDepth result (depth + 1)
  -- Create a term closure capturing the environment
  -- When applied, the argument will be added to this environment
  return Closure.term name env bodyTerm

/-- Rebuild a row with a new tail -/
partial def rebuildRowWithTail (row : Value) (newTail : Value) : Value :=
  match row with
  | .vRowEmpty => newTail
  | .vRowExtend label ty tail =>
    .vRowExtend label ty (rebuildRowWithTail tail newTail)
  | other => other -- If it's already a variable/meta, just return it

/-- Elaborate a kind expression to a Value.
    Kinds become types in CQC:
    - * (star) becomes Type₀
    - # (label) becomes Label (represented as a type)
    - % (row) becomes Row (represented as a type)
    - k1 -> k2 becomes a Pi type -/
def elaborateKind (kind : KindExpr) : TCM Value := do
  match kind with
  | .atom name =>
    match name.value with
    | "*" => return Value.vType Level.zero
    | "Type" => return Value.vType Level.zero
    | "#" | "Label" =>
      -- Labels are type-level strings, we represent them as a special type
      return Value.vType Level.zero  -- Label : Type₀
    | "%" | "Row" =>
      -- Rows are type-level constructs
      return Value.vType Level.zero  -- Row : Type₀
    | other =>
      TCM.throw (.cannotInfer s!"unknown kind '{other}'" name.span none)
  | .arrow from_ to _ =>
    let fromVal ← elaborateKind from_
    let toVal ← elaborateKind to
    -- Kind arrow becomes a non-dependent Pi type
    let cod ← mkConstClosure "_" toVal
    return Value.vPi .omega .explicit "_" fromVal cod

/-- Elaborate a type expression to a Value -/
partial def elaborateType (env : ElabEnv) (ty : TypeExpr) : TCM Value := do
  match ty with
  -- Type variable
  | .var name =>
    match env.lookup name.value with
    | some (lvl, _kind) =>
      -- Return a neutral variable
      return Value.vNeutral (Value.vType Level.zero) (Neutral.nVar ⟨name.value, lvl⟩)
    | none =>
      -- Unknown type variable - create a metavariable
      TCM.freshMetaVal (Value.vType Level.zero)

  -- Type constructor
  | .con name =>
    -- First check if this is a type abbreviation (e.g., CInt = Int32)
    if let some abbrevInfo ← TCM.lookupAbbrev name.value then
      -- Return the elaborated expansion directly.
      -- For non-parameterized: this is the final type (e.g., vPrimTy Int32)
      -- For parameterized: this is a Pi type that will be applied via .app
      return abbrevInfo.expansion
    -- Then try primitive types
    else if let some prim := resolvePrimitive name.value then
      return Value.vPrimTy prim
    -- Then try higher-kinded primitives
    else if let some hprim := resolveHigherPrimitive name.value then
      return Value.vHigherPrim hprim
    -- Then try Type
    else if let some tyVal := resolveType name.value then
      return tyVal
    -- Check if it's a constructor (for indexed type families like Fin (Succ m))
    else if let some globalInfo ← TCM.lookupGlobal name.value then
      if globalInfo.isConstructor then
        -- It's a constructor, return as vConstructor with no args yet
        return Value.vConstructor globalInfo.name globalInfo.ctorTag []
      else
        -- It's a defined value or data type - look up TypeId
        let typeId ← match ← TCM.lookupTypeId name.value with
          | some id => pure id
          | none =>
            let u ← TCM.freshUnique name.value
            let id := TypeId.fromUnique u
            TCM.registerTypeId name.value id
            pure id
        return Value.vDataType typeId []
    -- Otherwise, treat as a user-defined type (data type)
    else
      -- Look up the registered TypeId, or create a fresh one if not found
      let typeId ← match ← TCM.lookupTypeId name.value with
        | some id => pure id
        | none =>
          let u ← TCM.freshUnique name.value
          let id := TypeId.fromUnique u
          TCM.registerTypeId name.value id
          pure id
      return Value.vDataType typeId []

  -- Type application: F A
  | .app fn arg span =>
    let fnVal ← elaborateType env fn
    let argVal ← elaborateType env arg
    -- Apply the type function to the argument
    match fnVal with
    | .vDataType id params =>
      -- Accumulate type parameters for data types
      return Value.vDataType id (params ++ [argVal])
    | .vConstructor name tag args =>
      -- Constructor application in type position
      -- Accumulate arguments to the constructor
      return Value.vConstructor name tag (args ++ [argVal])
    | .vHigherPrim hp =>
      -- Higher-kinded primitive applied to arg
      let typeId := TypeId.builtin hp.name hp.uniqueId
      return Value.vDataType typeId [argVal]
    | .vPi _ _ _ _ cod =>
      -- Apply function type - evaluate the closure with TCM's applyClosure
      Soma.Dependent.applyClosure cod argVal
    | .vNeutral ty neu =>
      -- Stuck application
      return Value.vNeutral ty (Neutral.nApp neu argVal)
    | _ =>
      TCM.throw (.cannotInfer s!"cannot apply non-function type" span none)

  -- Arrow type: A -> B (non-dependent function)
  | .arrow from_ to _ =>
    let fromVal ← elaborateType env from_
    let toVal ← elaborateType env to
    -- For arrow types, the codomain doesn't depend on the arrow's own parameter.
    -- However, if we're inside a dependent Pi (env.level > 0), the codomain might
    -- reference outer bound variables. In that case, we need a term-based closure
    -- so that outer variable substitutions propagate correctly.
    if env.level > 0 then
      -- Inside dependent context: create term-based closure to allow substitution
      let codClosure ← mkDependentClosure "_" toVal env
      return Value.vPi .omega .explicit "_" fromVal codClosure
    else
      -- At top level: no outer variables to substitute
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
  | .list elem _ =>
    let elemVal ← elaborateType env elem
    -- Use a stable builtin TypeId for List
    let listId := TypeId.builtin "List" HigherPrimitive.list.uniqueId
    return Value.vDataType listId [elemVal]

  -- Universal quantification: forall a b. T
  | .forall_ vars body _ =>
    -- For forall quantifiers, we need proper term-based closures because
    -- the body references the bound type variables.

    -- First, elaborate the body in an extended environment with all type vars
    let env' := vars.foldl (fun acc v =>
      let kind := match v.kind with
        | some _ => Value.vType Level.zero  -- TODO: elaborate kind properly
        | none => Value.vType Level.zero
      acc.extend v.name.value kind
    ) env

    let bodyVal ← elaborateType env' body

    -- Convert the body Value to a Term
    -- The depth must be the FULL environment level (env'.level), not just vars.size,
    -- because the body may reference outer type variables (like `f` in a trait method).
    let bodyTerm ← valueToTermWithDepth bodyVal env'.level

    -- Build nested Pi types from right to left using Term representation
    -- For `forall a b. T`, we build: Π{a:*}. Π{b:*}. T[indices adjusted]
    let mut accTerm := bodyTerm
    for v in vars.toList.reverse do
      let kind ← match v.kind with
        | some k => elaborateKind k
        | none => pure (Value.vType Level.zero)
      let kindTerm ← valueToTermWithDepth kind 0
      accTerm := Term.pi .omega .implicit v.name.value kindTerm accTerm

    -- Evaluate the final term to get a Value
    TCM.evalTerm accTerm

  -- Constrained type: T with (C1, C2)
  | .constrained constraints body _ =>
    -- Elaborate the body first
    let bodyVal ← elaborateType env body
    -- For each constraint, wrap in an implicit instance argument
    -- (Show a) => becomes {{Show a}} ->
    -- Constraints don't introduce new bound variables that the body depends on,
    -- so we use const closures here (the body doesn't reference the instance arg)
    let result ← constraints.foldrM (init := bodyVal) fun (className, args, _) acc => do
      -- Elaborate constraint arguments
      let argVals ← args.toList.mapM (elaborateType env)
      -- Create the constraint type (e.g., Show Int)
      let classId ← match ← TCM.lookupTypeId className.value with
        | some id => pure id
        | none =>
          let u ← TCM.freshUnique className.value
          pure (TypeId.fromUnique u)
      let constraintTy := Value.vDataType classId argVals
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
      let labelVal := match env.lookup name.value with
        | some (lvl, _) =>
          -- Field name is a bound variable - use as label variable
          Value.vNeutral (Value.vType Level.zero) (Neutral.nVar ⟨name.value, lvl⟩)
        | none =>
          -- Field name is a literal label
          Value.vLabelLit name.value
      row := Value.vRowExtend labelVal tyVal row
    -- Handle row tail (for polymorphism)
    -- The tail represents a row variable that can be unified with other rows
    match tail with
    | some tailName =>
      match env.lookup tailName.value with
      | some (lvl, _) =>
        -- The tail is a known row variable - use it directly as the row tail
        -- (not as a labeled field, but as the actual tail of the row)
        let tailVar := Value.vNeutral (Value.vType Level.zero) (Neutral.nVar ⟨tailName.value, lvl⟩)
        -- Properly concatenate: prepend our fields to the tail row
        -- We need to rebuild the row with the tail as the base
        row := rebuildRowWithTail row tailVar
      | none =>
        -- Unknown tail variable - create metavariable for the tail
        let tailMeta ← TCM.freshMetaVal (Value.vType Level.zero)
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
      let labelVal := match env.lookup name.value with
        | some (lvl, _) =>
          Value.vNeutral (Value.vType Level.zero) (Neutral.nVar ⟨name.value, lvl⟩)
        | none =>
          Value.vLabelLit name.value
      row := Value.vRowExtend labelVal tyVal row
    -- Handle row tail (for polymorphism)
    match tail with
    | some tailName =>
      match env.lookup tailName.value with
      | some (lvl, _) =>
        let tailVar := Value.vNeutral (Value.vType Level.zero) (Neutral.nVar ⟨tailName.value, lvl⟩)
        row := rebuildRowWithTail row tailVar
      | none =>
        let tailMeta ← TCM.freshMetaVal (Value.vType Level.zero)
        row := rebuildRowWithTail row tailMeta
    | none => pure ()
    return Value.vVariant row

  -- Dependent function type (Pi): (q x : A) -> B
  | .pi qty name domain codomain _ =>
    let domVal ← elaborateType env domain
    -- Extend env with the bound variable for the codomain
    let env' := env.extend name.value domVal
    let codVal ← elaborateType env' codomain
    -- Create a term-based closure for dependent substitution
    -- IMPORTANT: Pass env (not env') - the closure should NOT capture its own parameter.
    -- When applied, the closure will be extended with the argument.
    let codClosure ← mkDependentClosure name.value codVal env
    return Value.vPi qty .explicit name.value domVal codClosure

  -- Dependent pair type (Sigma): (x : A) × B
  | .sigma qty name fst snd _ =>
    let fstVal ← elaborateType env fst
    let env' := env.extend name.value fstVal
    let sndVal ← elaborateType env' snd
    -- Create a term-based closure for dependent substitution
    -- Pass env (not env') - the closure should NOT capture its own parameter.
    let sndClosure ← mkDependentClosure name.value sndVal env
    return Value.vSigma qty name.value fstVal sndClosure

  -- Instance-implicit parameter: {{x : A}} -> B
  -- Uses BinderInfo.instance_ so that instance resolution kicks in
  | .implicit name domain codomain _ =>
    let domVal ← elaborateType env domain
    let bindName := name.map (·.value) |>.getD "_"
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
    let typeId ← match ← TCM.lookupTypeId typeName with
      | some id => pure id
      | none =>
        let u ← TCM.freshUnique typeName
        pure (TypeId.fromUnique u)
    let mut ty := Value.vDataType typeId []
    for fieldTy in fieldTys.reverse do
      let fieldVal ← elaborateType env fieldTy
      let codClosure ← mkConstClosure "_" ty
      ty := Value.vPi .omega .explicit "_" fieldVal codClosure
    return ty

end Soma.Dependent.Elaborate
