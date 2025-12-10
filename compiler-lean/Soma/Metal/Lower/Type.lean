import Soma.Metal.Lower.Monad
import Soma.Syntax.Ast

namespace Soma.Metal.Lower

open Soma.Typing
open Soma.Syntax (Span TypeExpr)

/-- Helper to create a Ty from a user TypeId at a given kind.
    TODO: make user kinds not always * -/
private def userTyOfKind (id : TypeId) : (k : Kind) → Ty k
  | .star => .con id
  | k => .var ⟨id.name, id.unique, k⟩  -- Fallback for non-star kinds

mutual
  /-- Resolve a type expression from Syntax to a MonoTy. TODO: Lower it even if it fails -/
  partial def resolveType (ty : TypeExpr) : LowerM (Option MonoTy) := do
    match ty with
    | .var name =>
      -- Type variable - create a TyVarId (default kind is .star)
      let id ← LowerM.freshUniqueId
      let tyVarId : TyVarId := { name := name.value, id := id, kind := .star }
      pure (some (.var tyVarId))

    | .con name =>
      -- Type constructor - look up in environment
      resolveTypeCon name.value name.span

    | .app fn arg span =>
      -- Type application
      let fnTy? ← resolveTypeAny fn
      let argTy? ← resolveType arg
      match fnTy?, argTy? with
      | some fnTy, some argTy =>
        applyType fnTy argTy span
      | _, _ => pure none

    | .arrow from_ to _ =>
      -- Function type
      let fromTy? ← resolveType from_
      let toTy? ← resolveType to
      match fromTy?, toTy? with
      | some fromTy, some toTy => pure (some (.arrow fromTy toTy))
      | _, _ => pure none

    | .tuple elements _ =>
      -- Tuple type
      let elemTys ← elements.mapM resolveType
      if elemTys.all Option.isSome then
        let tys := elemTys.filterMap id
        pure (some (Ty.tuple tys))
      else
        pure none

    | .list elem _ =>
      -- List type (sugar for Array)
      let elemTy? ← resolveType elem
      match elemTy? with
      | some elemTy => pure (some (Ty.array elemTy))
      | none => pure none

    | .forall_ _ body _ =>
      -- For now, just resolve the body (forall is handled at QualifiedType level)
      resolveType body

    | .constrained _ body _ =>
      -- Constraints handled at QualifiedType level
      resolveType body

    | .parens inner _ =>
      resolveType inner

    | .kinded ty _ _ =>
      -- Kind annotations - just resolve the type for now
      resolveType ty

  /-- Resolve a type that might have non-star kind -/
  private partial def resolveTypeAny (ty : TypeExpr) : LowerM (Option SomeTy) := do
    match ty with
    | .con name =>
      -- Type constructor - might have any kind
      resolveTypeConAny name.value name.span
    | .app fn arg span =>
      let fnTy? ← resolveTypeAny fn
      let argTy? ← resolveType arg
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
      let ty? ← resolveType ty
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

/-- Resolve a QualifiedType from a Syntax TypeExpr -/
def resolveQualifiedType (ty : TypeExpr) : LowerM (Option QualifiedType) := do
  -- TODO: handle forall and constraints
  let bodyTy? ← resolveType ty
  match bodyTy? with
  | some bodyTy => pure (some (QualifiedType.mono bodyTy))
  | none => pure none

end Soma.Metal.Lower
