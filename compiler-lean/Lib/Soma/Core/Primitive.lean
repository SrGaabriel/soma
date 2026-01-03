namespace Soma.Core

/-- Primitive types with no type parameters (base types) -/
inductive StarPrimitive where
  | int
  | long
  | short
  | byte
  | float
  | double
  | bool
  | string
  | unit
  | closurePtr
  | ptr
  deriving Repr, BEq, Hashable, DecidableEq

namespace StarPrimitive

def name : StarPrimitive → String
  | .int => "Int"
  | .long => "Long"
  | .short => "Short"
  | .byte => "Byte"
  | .float => "Float"
  | .double => "Double"
  | .bool => "Bool"
  | .string => "String"
  | .unit => "Unit"
  | .closurePtr => "ClosurePtr"
  | .ptr => "Ptr"

instance : ToString StarPrimitive := ⟨StarPrimitive.name⟩

def fromName? : String → Option StarPrimitive
  | "Int" => some .int
  | "Long" => some .long
  | "Short" => some .short
  | "Byte" => some .byte
  | "Float" => some .float
  | "Double" => some .double
  | "Bool" => some .bool
  | "String" => some .string
  | "Unit" | "()" => some .unit
  | "ClosurePtr" => some .closurePtr
  | "Ptr" => some .ptr
  | _ => none

/-- Check if this is a numeric type -/
def isNumeric : StarPrimitive → Bool
  | .int | .long | .short | .byte | .float | .double => true
  | _ => false

/-- Check if this is an integral type -/
def isIntegral : StarPrimitive → Bool
  | .int | .long | .short | .byte => true
  | _ => false

/-- Check if this is a floating-point type -/
def isFloating : StarPrimitive → Bool
  | .float | .double => true
  | _ => false

end StarPrimitive

/-- Primitive type constructors that take one type argument -/
inductive HigherPrimitive where
  | array
  | list
  | ref
  | io
  deriving Repr, BEq, Hashable, DecidableEq

namespace HigherPrimitive

def name : HigherPrimitive → String
  | .array => "Array"
  | .list => "List"
  | .ref => "Ref"
  | .io => "IO"

instance : ToString HigherPrimitive := ⟨HigherPrimitive.name⟩

def fromName? : String → Option HigherPrimitive
  | "Array" => some .array
  | "List" => some .list
  | "Ref" => some .ref
  | "IO" => some .io
  | _ => none

/-- Deterministic unique ID for each higher primitive -/
def uniqueId : HigherPrimitive → Nat
  | .array => 0
  | .list => 1
  | .ref => 2
  | .io => 3

end HigherPrimitive

end Soma.Core
