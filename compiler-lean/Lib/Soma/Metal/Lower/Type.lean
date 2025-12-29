import Soma.Metal.Lower.Monad
import Soma.Syntax.Ast
import Std.Data.HashSet

namespace Soma.Metal.Lower

open Soma.Typing
open Soma.Syntax (Span TypeExpr)

/-- Create a Ty from a user TypeId at a given kind -/
private def userTyOfKind (id : TypeId) (k : Kind) : Ty k :=
  .userCon k id

/-- Count the maximum number of type arguments a variable is applied to -/
private partial def inferVarArity (ty : TypeExpr) : Std.HashMap String Nat :=
  go ty 0 {}
where
  /-- Traverse type, tracking application depth for variables -/
  go (ty : TypeExpr) (appDepth : Nat) (acc : Std.HashMap String Nat) : Std.HashMap String Nat :=
    match ty with
    | .var name =>
      -- Record this variable at current application depth
      let current := acc.getD name.value 0
      acc.insert name.value (max current appDepth)
    | .con _ => acc
    | .app fn arg _ =>
      -- The function is being applied to one more argument
      let acc' := go fn (appDepth + 1) acc
      -- The argument is in a fresh context (depth 0)
      go arg 0 acc'
    | .arrow from_ to _ =>
      let acc' := go from_ 0 acc
      go to 0 acc'
    | .tuple elems _ =>
      elems.foldl (fun a e => go e 0 a) acc
    | .list elem _ =>
      go elem 0 acc
    | .forall_ _ body _ =>
      go body 0 acc
    | .constrained _ body _ =>
      go body 0 acc
    | .parens inner _ =>
      go inner appDepth acc
    | .kinded inner _ _ =>
      go inner appDepth acc
    | .record fields tail _ =>
      let acc' := fields.foldl (fun a (_, t) => go t 0 a) acc
      match tail with
      | some tailName => acc'.insert tailName.value (max (acc'.getD tailName.value 0) 0)
      | none => acc'

/-- Build a Kind from an arity (number of type arguments) -/
private def kindOfArity : Nat → Kind
  | 0 => .star
  | n + 1 => .arrow .star (kindOfArity n)

/-- Environment mapping type variable names to their inferred kinds -/
abbrev KindEnv := Std.HashMap String Kind

/-- Environment mapping type variable names to their resolved TyVarIds -/
abbrev TyVarEnv := Std.HashMap String TyVarId

/-- Infer kinds for all type variables in a type expression -/
def inferKinds (ty : TypeExpr) : KindEnv :=
  let arities := inferVarArity ty
  arities.fold (init := {}) fun acc name arity =>
    acc.insert name (kindOfArity arity)

mutual
  /-- Resolve a type expression from Syntax to a MonoTy using inferred kinds and bound type variables -/
  partial def resolveTypeWithEnv (kindEnv : KindEnv) (tyVarEnv : TyVarEnv) (ty : TypeExpr) : LowerM (Option MonoTy) := do
    match ty with
    | .var name =>
      -- Type variable - check if already bound, otherwise create fresh
      match tyVarEnv.get? name.value with
      | some tyVarId => pure (some (.var tyVarId))
      | none =>
        -- Unbound variable - create fresh (this shouldn't happen in well-formed types)
        let kind := kindEnv.getD name.value .star
        let id ← LowerM.freshUniqueId
        let tyVarId : TyVarId := { name := name.value, id := id, kind := kind }
        pure (some (.var tyVarId))

    | .con name =>
      -- Type constructor - look up in environment
      resolveTypeCon name.value name.span

    | .app fn arg span =>
      -- Type application
      let fnTy? ← resolveTypeAnyWithEnv kindEnv tyVarEnv fn
      let argTy? ← resolveTypeWithEnv kindEnv tyVarEnv arg
      match fnTy?, argTy? with
      | some fnTy, some argTy =>
        applyType fnTy argTy span
      | _, _ => pure none

    | .arrow from_ to _ =>
      -- Function type
      let fromTy? ← resolveTypeWithEnv kindEnv tyVarEnv from_
      let toTy? ← resolveTypeWithEnv kindEnv tyVarEnv to
      match fromTy?, toTy? with
      | some fromTy, some toTy => pure (some (.arrow fromTy toTy))
      | _, _ => pure none

    | .tuple elements _ =>
      -- Tuple type
      let elemTys ← elements.mapM (resolveTypeWithEnv kindEnv tyVarEnv)
      if elemTys.all Option.isSome then
        let tys := elemTys.filterMap id
        pure (some (Ty.mkTuple tys))
      else
        pure none

    | .list elem _ =>
      -- List type (sugar for Array)
      let elemTy? ← resolveTypeWithEnv kindEnv tyVarEnv elem
      match elemTy? with
      | some elemTy => pure (some (Ty.array elemTy))
      | none => pure none

    | .forall_ binders body _ =>
      -- Extend tyVarEnv with the bound variables, then resolve body
      let mut newEnv := tyVarEnv
      for binder in binders do
        let varName := binder.name.value
        -- Use explicit kind annotation if provided, otherwise fall back to inferred kind
        let kind := match binder.kind with
          | some kindName => Kind.fromString kindName.value
          | none => kindEnv.getD varName .star
        let id ← LowerM.freshUniqueId
        let tyVarId : TyVarId := { name := varName, id := id, kind := kind }
        newEnv := newEnv.insert varName tyVarId
      resolveTypeWithEnv kindEnv newEnv body

    | .constrained _ body _ =>
      -- Constraints handled at QualifiedType level
      resolveTypeWithEnv kindEnv tyVarEnv body

    | .parens inner _ =>
      resolveTypeWithEnv kindEnv tyVarEnv inner

    | .kinded ty _ _ =>
      -- Kind annotations - just resolve the type for now
      resolveTypeWithEnv kindEnv tyVarEnv ty

    | .record fields tail _ =>
      -- First, determine the base row (either empty or a row variable for polymorphism)
      let baseRow : Ty .row ← match tail with
        | some tailName =>
          -- Row polymorphic: { x :: Int | r }
          match tyVarEnv.get? tailName.value with
          | some tyVarId =>
            -- Use the existing row variable
            pure (.var { tyVarId with kind := .row })
          | none =>
            -- Create a fresh row variable
            let id ← LowerM.freshUniqueId
            let tyVarId : TyVarId := { name := tailName.value, id := id, kind := .row }
            pure (.var tyVarId)
        | none =>
          pure .rowEmpty
      -- Build the row type from fields, extending the base row
      let mut rowTy := baseRow
      for (fieldName, fieldTy) in fields.reverse do
        let fieldMonoTy? ← resolveTypeWithEnv kindEnv tyVarEnv fieldTy
        match fieldMonoTy? with
        | some fieldMonoTy =>
          rowTy := .rowExtend (.labelLit fieldName.value) fieldMonoTy rowTy
        | none => return none
      pure (some (.record rowTy))

  /-- Resolve a type that might have non-star kind, using inferred kinds and bound type variables -/
  private partial def resolveTypeAnyWithEnv (kindEnv : KindEnv) (tyVarEnv : TyVarEnv) (ty : TypeExpr) : LowerM (Option SomeTy) := do
    match ty with
    | .var name =>
      -- Type variable in function position - check if bound, otherwise create fresh
      match tyVarEnv.get? name.value with
      | some tyVarId => pure (some ⟨tyVarId.kind, .var tyVarId⟩)
      | none =>
        let kind := kindEnv.getD name.value .star
        let id ← LowerM.freshUniqueId
        let tyVarId : TyVarId := { name := name.value, id := id, kind := kind }
        pure (some ⟨kind, .var tyVarId⟩)
    | .con name =>
      -- Type constructor - might have any kind
      resolveTypeConAny name.value name.span
    | .app fn arg span =>
      let fnTy? ← resolveTypeAnyWithEnv kindEnv tyVarEnv fn
      let argTy? ← resolveTypeWithEnv kindEnv tyVarEnv arg
      match fnTy?, argTy? with
      | some ⟨.arrow k1 k2, fnTy⟩, some argTy =>
        -- We need to check that k1 = .star since argTy : MonoTy = Ty .star
        match k1 with
        | .star =>
          pure (some ⟨k2, .app fnTy argTy⟩)
        | _ =>
          LowerM.reportError (.kindMismatch "kind *" s!"kind {k1}" span)
          pure none
      | some ⟨k, _⟩, some _ =>
        LowerM.reportError (.kindMismatch "arrow kind" s!"kind {k}" span)
        pure none
      | _, _ => pure none
    | _ =>
      -- Other types are kind *
      let ty? ← resolveTypeWithEnv kindEnv tyVarEnv ty
      match ty? with
      | some t => pure (some ⟨.star, t⟩)
      | none => pure none

  /-- Resolve a type constructor name to a MonoTy -/
  private partial def resolveTypeCon (name : String) (span : Span) : LowerM (Option MonoTy) := do
    -- First check star primitives
    match StarPrimitive.fromName? name with
    | some prim => pure (some (.starPrim prim))
    | none =>
      -- Check higher primitives (these need arguments)
      match HigherPrimitive.fromName? name with
      | some _ =>
        -- Higher-kinded primitive needs arguments
        LowerM.reportError (.kindMismatch "kind *" "kind * -> *" span)
        pure none
      | none =>
        -- Look up in type environment
        let tyInfo? ← LowerM.lookupType name
        match tyInfo? with
        | some info =>
          match info.kind with
          | .star =>
            match info.tyCon with
            | .user id => pure (some (.con id))
            | .prim p =>
              -- A prim TyCon in the env - check if it's star-kinded
              match p.kind with
              | .star =>
                match StarPrimitive.fromName? p.name with
                | some sp => pure (some (.starPrim sp))
                | none =>
                  -- Create a user type fallback
                  let modName ← LowerM.getModuleName
                  let unique ← LowerM.freshUniqueId
                  pure (some (.con ⟨modName, p.name, unique, .star⟩))
              | _ =>
                LowerM.reportError (.kindMismatch "kind *" s!"kind {p.kind}" span)
                pure none
          | k =>
            LowerM.reportError (.kindMismatch "kind *" s!"kind {k}" span)
            pure none
        | none =>
          LowerM.reportError (.unknownType name span)
          pure none

  /-- Resolve a type constructor to any kind -/
  private partial def resolveTypeConAny (name : String) (span : Span) : LowerM (Option SomeTy) := do
    -- First check star primitives
    match StarPrimitive.fromName? name with
    | some prim => pure (some ⟨.star, .starPrim prim⟩)
    | none =>
      -- Check higher primitives
      match HigherPrimitive.fromName? name with
      | some prim => pure (some ⟨.arrow .star .star, .higherPrim prim⟩)
      | none =>
        -- Look up in type environment
        let tyInfo? ← LowerM.lookupType name
        match tyInfo? with
        | some info =>
          match info.tyCon with
          | .user id => pure (some ⟨info.kind, userTyOfKind id info.kind⟩)
          | .prim p =>
            match p.kind with
            | .star =>
              match StarPrimitive.fromName? p.name with
              | some sp => pure (some ⟨.star, .starPrim sp⟩)
              | none =>
                let modName ← LowerM.getModuleName
                let unique ← LowerM.freshUniqueId
                pure (some ⟨.star, .con ⟨modName, p.name, unique, .star⟩⟩)
            | .arrow .star .star =>
              match HigherPrimitive.fromName? p.name with
              | some hp => pure (some ⟨.arrow .star .star, .higherPrim hp⟩)
              | none =>
                let modName ← LowerM.getModuleName
                let unique ← LowerM.freshUniqueId
                pure (some ⟨.star, .con ⟨modName, p.name, unique, .star⟩⟩)
            | _ =>
              let modName ← LowerM.getModuleName
              let unique ← LowerM.freshUniqueId
              pure (some ⟨.star, .con ⟨modName, p.name, unique, .star⟩⟩)
        | none =>
          LowerM.reportError (.unknownType name span)
          pure none

  /-- Apply a type function to an argument -/
  private partial def applyType (fn : SomeTy) (arg : MonoTy) (span : Span) : LowerM (Option MonoTy) := do
    match fn with
    | ⟨.arrow k1 k2, fnTy⟩ =>
      match k1, k2 with
      | .star, .star => pure (some (.app fnTy arg))
      | .star, _ =>
        -- Result is not star kind
        LowerM.reportError (.kindMismatch "kind *" s!"kind {k2}" span)
        pure none
      | _, _ =>
        -- Argument kind mismatch
        LowerM.reportError (.kindMismatch s!"kind {k1}" "kind *" span)
        pure none
    | ⟨k, _⟩ =>
      LowerM.reportError (.kindMismatch "arrow kind" s!"kind {k}" span)
      pure none
end

/-- Resolve a type expression from syntax to a MonoTy -/
def resolveType (ty : TypeExpr) : LowerM (Option MonoTy) := do
  let kindEnv := inferKinds ty
  resolveTypeWithEnv kindEnv {} ty

/-- Look up a type class by name, checking built-in classes first -/
private def lookupTypeClass (name : String) : LowerM (Option TyCon) := do
  match name with
  | "Eq" => pure (some TypeClassName.eq)
  | "Ord" => pure (some TypeClassName.ord)
  | "Show" => pure (some TypeClassName.show_)
  | "Num" => pure (some TypeClassName.num)
  | "Functor" => pure (some TypeClassName.functor)
  | "Monad" => pure (some TypeClassName.monad)
  | _ =>
    let env ← LowerM.getGlobalEnv
    pure (env.lookupTypeClass name |>.map (·.tyCon))

/-- Resolve a constraint from syntax with a given type variable environment -/
private def resolveConstraintWithEnv (kindEnv : KindEnv) (tyVarEnv : TyVarEnv) (className : Syntax.Name) (args : Array TypeExpr) : LowerM (Option Constraint) := do
  let tycon? ← lookupTypeClass className.value
  match tycon? with
  | none => pure none
  | some tycon =>
    let resolvedArgs ← args.mapM (resolveTypeWithEnv kindEnv tyVarEnv)
    if resolvedArgs.all Option.isSome then
      pure (some { className := tycon, args := resolvedArgs.filterMap id })
    else
      pure none

/-- Resolve a QualifiedType from a Syntax TypeExpr, handling forall and constraints -/
def resolveQualifiedType (ty : TypeExpr) : LowerM (Option QualifiedType) := do
  -- Infer kinds for the entire type expression first
  let kindEnv := inferKinds ty
  -- Collect type variables and constraints while unwrapping the type
  -- Pass kindEnv and build tyVarEnv incrementally as we encounter foralls
  let (explicitVars, constraints, innerTy, tyVarEnv) ← collectQuantifiers kindEnv ty #[] #[] {}

  -- Collect all free type variable names from the inner type
  let allVarNames := innerTy.collectVarNames
  -- Find implicit type variables (those not already bound by explicit forall)
  let explicitNames : Std.HashSet String := explicitVars.foldl (init := {}) fun acc v => acc.insert v.name

  -- Create TyVarIds for implicit type variables and add to environment
  let mut allVars := explicitVars
  let mut finalEnv := tyVarEnv
  for name in allVarNames do
    if !explicitNames.contains name then
      let kind := kindEnv.getD name .star
      let id ← LowerM.freshUniqueId
      let tyVarId : TyVarId := { name := name, id := id, kind := kind }
      allVars := allVars.push tyVarId
      finalEnv := finalEnv.insert name tyVarId

  let bodyTy? ← resolveTypeWithEnv kindEnv finalEnv innerTy
  match bodyTy? with
  | some bodyTy => pure (some { vars := allVars, constraints, body := bodyTy })
  | none => pure none
where
  /-- Recursively collect forall-bound variables and constraints, building TyVarEnv as we go -/
  collectQuantifiers (kindEnv : KindEnv) (ty : TypeExpr) (accVars : Array TyVarId) (accConstrs : Array Constraint) (tyVarEnv : TyVarEnv)
      : LowerM (Array TyVarId × Array Constraint × TypeExpr × TyVarEnv) := do
    match ty with
    | .forall_ binders body _ =>
      -- Create TyVarIds for each bound variable and add to environment
      let mut newVars := accVars
      let mut newEnv := tyVarEnv
      for binder in binders do
        let varName := binder.name.value
        -- Use explicit kind annotation if provided, otherwise fall back to inferred kind
        let kind := match binder.kind with
          | some kindName => Kind.fromString kindName.value
          | none => kindEnv.getD varName .star
        let id ← LowerM.freshUniqueId
        let tyVarId : TyVarId := { name := varName, id := id, kind := kind }
        newVars := newVars.push tyVarId
        newEnv := newEnv.insert varName tyVarId
      collectQuantifiers kindEnv body newVars accConstrs newEnv
    | .constrained syntaxConstrs body _ =>
      -- Resolve each constraint using current tyVarEnv
      let mut newConstrs := accConstrs
      for (className, args, _span) in syntaxConstrs do
        let constr? ← resolveConstraintWithEnv kindEnv tyVarEnv ⟨className.value, className.span⟩ args
        match constr? with
        | some c => newConstrs := newConstrs.push c
        | none => pure ()  -- Skip unresolved constraints (error reported elsewhere)
      collectQuantifiers kindEnv body accVars newConstrs tyVarEnv
    | .parens inner _ =>
      collectQuantifiers kindEnv inner accVars accConstrs tyVarEnv
    | _ =>
      -- Reached the body type
      pure (accVars, accConstrs, ty, tyVarEnv)

end Soma.Metal.Lower
