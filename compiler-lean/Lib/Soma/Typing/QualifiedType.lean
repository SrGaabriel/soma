import Soma.Typing.Constraint

namespace Soma.Typing

/-- A polymorphic type with constraints: forall a b. (Show a, Eq b) => a -> b -> String -/
structure QualifiedType where
  vars : Array TyVarId
  constraints : Array Constraint
  body : MonoTy
  deriving BEq

namespace QualifiedType

/-- Create a monomorphic qualified type (no quantification) -/
def mono (ty : MonoTy) : QualifiedType :=
  { vars := #[], constraints := #[], body := ty }

/-- Check if this type is monomorphic (no quantified variables) -/
def isMonomorphic (qt : QualifiedType) : Bool := qt.vars.isEmpty

/-- Check if this type has constraints -/
def hasConstraints (qt : QualifiedType) : Bool := !qt.constraints.isEmpty

/-- Pretty print a qualified type -/
def toString (qt : QualifiedType) : String :=
  let varsStr :=
    if qt.vars.isEmpty then ""
    else s!"forall {qt.vars.toList.map (·.name) |> String.intercalate " "}. "
  let consStr :=
    if qt.constraints.isEmpty then ""
    else s!"({qt.constraints.toList.map Constraint.toString |> String.intercalate ", "}) => "
  s!"{varsStr}{consStr}{qt.body}"

instance : ToString QualifiedType := ⟨QualifiedType.toString⟩

/-- Get all free type variables (those in body but not quantified) -/
def freeVars (qt : QualifiedType) : Array TyVarId :=
  let boundIds := qt.vars.map (·.id)
  qt.body.freeVars.filter fun v => !boundIds.contains v.id

/-- Instantiate quantified variables with concrete types -/
def instantiate (qt : QualifiedType) (types : Array MonoTy) : Option MonoTy :=
  if types.size != qt.vars.size then none
  else
    -- Build substitution map from var id to replacement type
    let pairs := qt.vars.zip types
    let mapping : TySubst := pairs.foldl (fun m (v, t) => m.insert v.id t) {}
    some (qt.body.subst mapping)

end QualifiedType

end Soma.Typing
