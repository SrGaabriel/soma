import Soma.Typing.Kind

namespace Soma.Typing

/-- Primitive types built into the language -/
inductive Primitive where
  | int
  | long
  | short
  | byte
  | float
  | double
  | bool
  | string
  | unit
  | array
  | tuple (arity : Nat)
  | closurePtr
  | ptr
  | ref
  | io
  | classEq
  | classOrd
  | classShow
  | classNum
  | classFunctor
  | classMonad
  deriving Repr, BEq, Hashable, DecidableEq

namespace Primitive

/-- Get the name of a primitive type -/
def name : Primitive → String
  | .int => "Int"
  | .long => "Long"
  | .short => "Short"
  | .byte => "Byte"
  | .float => "Float"
  | .double => "Double"
  | .bool => "Bool"
  | .string => "String"
  | .unit => "Unit"
  | .array => "Array"
  | .tuple 0 => "Unit"
  | .tuple n => s!"Tuple{n}"
  | .closurePtr => "ClosurePtr"
  | .ptr => "Ptr"
  | .ref => "Ref"
  | .io => "IO"
  | .classEq => "Eq"
  | .classOrd => "Ord"
  | .classShow => "Show"
  | .classNum => "Num"
  | .classFunctor => "Functor"
  | .classMonad => "Monad"

instance : ToString Primitive := ⟨Primitive.name⟩

/-- Get the kind of a primitive type -/
def kind : Primitive → Kind
  | .int | .long | .short | .byte => .star
  | .float | .double => .star
  | .bool | .string | .unit => .star
  | .closurePtr | .ptr => .star
  | .array | .ref | .io => .arrow .star .star
  | .tuple n => Kind.nary n
  | .classEq | .classOrd | .classShow | .classNum => .arrow .star .star
  | .classFunctor | .classMonad => .arrow (.arrow .star .star) .star

/-- Parse a primitive type from its name -/
def fromName? : String → Option Primitive
  | "Int" => some .int
  | "Long" => some .long
  | "Short" => some .short
  | "Byte" => some .byte
  | "Float" => some .float
  | "Double" => some .double
  | "Bool" => some .bool
  | "String" => some .string
  | "Unit" | "()" => some .unit
  | "Array" => some .array
  | "ClosurePtr" => some .closurePtr
  | "Ptr" => some .ptr
  | "Ref" => some .ref
  | "IO" => some .io
  | "Eq" => some .classEq
  | "Ord" => some .classOrd
  | "Show" => some .classShow
  | "Num" => some .classNum
  | "Functor" => some .classFunctor
  | "Monad" => some .classMonad
  | s =>
    if s.startsWith "Tuple" then
      match s.drop 5 |>.toNat? with
      | some n => some (.tuple n)
      | none => none
    else none

end Primitive

end Soma.Typing
