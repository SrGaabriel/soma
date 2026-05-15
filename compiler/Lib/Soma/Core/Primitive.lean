import Kenosis

namespace Soma.Core

open Kenosis

/-- Primitive types recognized by the compiler via @[wired_in] attributes -/
inductive PrimType where
  | int
  | float
  | double
  | bool
  | string
  | unit
  | closurePtr
  -- Fixed-width signed integers
  | int8
  | int16
  | int64
  -- Fixed-width unsigned integers
  | word
  | word8
  | word16
  | word64
  | array
  | list
  | ref
  | world
  | ptr
  deriving Repr, BEq, Hashable, DecidableEq, Serialize, Deserialize

namespace PrimType

def name : PrimType → String
  | .int => "Int32"
  | .float => "Float"
  | .double => "Double"
  | .bool => "Bool"
  | .string => "String"
  | .unit => "Unit"
  | .closurePtr => "ClosurePtr"
  | .int8 => "Int8"
  | .int16 => "Int16"
  | .int64 => "Int64"
  | .word => "Word32"
  | .word8 => "Word8"
  | .word16 => "Word16"
  | .word64 => "Word64"
  | .array => "Array"
  | .list => "List"
  | .ref => "Ref"
  | .world => "World"
  | .ptr => "Ptr"

instance : ToString PrimType := ⟨PrimType.name⟩

/-- Check if this is an integral type -/
def isIntegral : PrimType → Bool
  | .int | .int8 | .int16 | .int64 => true
  | .word | .word8 | .word16 | .word64 => true
  | _ => false

/-- Check if this is a floating-point type -/
def isFloating : PrimType → Bool
  | .float | .double => true
  | _ => false

end PrimType

end Soma.Core
