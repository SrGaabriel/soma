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

def fromName? : String → Option PrimType
  | "Int32" => some .int
  | "Float" => some .float
  | "Double" => some .double
  | "Bool" => some .bool
  | "String" => some .string
  | "Unit" | "()" => some .unit
  | "ClosurePtr" => some .closurePtr
  | "Int8" => some .int8
  | "Int16" => some .int16
  | "Int64" => some .int64
  | "Word32" => some .word
  | "Word8" => some .word8
  | "Word16" => some .word16
  | "Word64" => some .word64
  | "Array" => some .array
  | "List" => some .list
  | "Ref" => some .ref
  | "World" => some .world
  | "Ptr" => some .ptr
  | _ => none

/-- Whether this is a nullary type -/
def isNullary : PrimType → Bool
  | .array | .list | .ref | .ptr => false
  | _ => true

/-- Check if this is a numeric type -/
def isNumeric : PrimType → Bool
  | .int | .float | .double => true
  | .int8 | .int16 | .int64 => true
  | .word | .word8 | .word16 | .word64 => true
  | _ => false

/-- Check if this is an integral type -/
def isIntegral : PrimType → Bool
  | .int | .int8 | .int16 | .int64 => true
  | .word | .word8 | .word16 | .word64 => true
  | _ => false

/-- Check if this is a signed integral type -/
def isSigned : PrimType → Bool
  | .int | .int8 | .int16 | .int64 => true
  | _ => false

/-- Check if this is an unsigned integral type -/
def isUnsigned : PrimType → Bool
  | .word | .word8 | .word16 | .word64 => true
  | _ => false

/-- Check if this is a floating-point type -/
def isFloating : PrimType → Bool
  | .float | .double => true
  | _ => false

/-- Get the bit width of an integral type -/
def bitWidth : PrimType → Option Nat
  | .int8 | .word8 => some 8
  | .int16 | .word16 => some 16
  | .int | .word => some 32
  | .int64 | .word64 => some 64
  | _ => none

end PrimType

end Soma.Core
