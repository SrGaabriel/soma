import Soma.Typing.Ty

namespace Soma.Typing

/-- A type class constraint: Show a, Functor f -/
structure Constraint where
  className : TyCon
  args : Array MonoTy
  deriving BEq

namespace Constraint

/-- Get the class name as a string -/
def classNameStr (c : Constraint) : String := c.className.name

/-- Pretty print a constraint -/
def toString (c : Constraint) : String :=
  if c.args.isEmpty then c.classNameStr
  else s!"{c.classNameStr} {c.args.toList.map Ty.toString |> String.intercalate " "}"

instance : ToString Constraint := ⟨Constraint.toString⟩

/-- Get all type variables mentioned in this constraint -/
def freeVars (c : Constraint) : Array TyVarId :=
  c.args.foldl (fun acc t => acc ++ t.freeVars) #[]

end Constraint

end Soma.Typing
