import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Core.Quantity
import Soma.Syntax.Source

namespace Soma.Dependent

open Soma.Core
open Soma.Syntax (Span)

/-- Maximum recursion depth for type checking operations -/
def maxRecursionDepth : Nat := 1000

/-- Maximum number of parameters to extract from a Pi type -/
def maxPiParams : Nat := 100

/-- Maximum constraint solving iterations -/
def maxConstraintIterations : Nat := 1000

/-- Maximum instance resolution depth -/
def maxInstanceDepth : Nat := 50

/-- Maximum number of implicit arguments to insert -/
def maxImplicitArgs : Nat := 100

/-- Maximum unification depth for deeply nested types -/
def maxUnificationDepth : Nat := 500

/-- Maximum fuel for termination checking call matrix analysis -/
def maxTerminationFuel : Nat := 1000

/-- Maximum number of positivity checking iterations -/
def maxPositivityIterations : Nat := 100

/-- A span that indicates no source location (for internal use) -/
def noSpan : Span := Span.uninhabited

/-- Safe bounded recursion helper -/
def withFuel {α : Type} (fuel : Nat) (default : α) (f : Nat → α) : α :=
  if fuel == 0 then default else f (fuel - 1)

/-- Check if we have fuel remaining -/
def hasFuel (fuel : Nat) : Bool := fuel > 0

/-- Decrement fuel, returning none if exhausted -/
def decrementFuel (fuel : Nat) : Option Nat :=
  if fuel == 0 then none else some (fuel - 1)

end Soma.Dependent
