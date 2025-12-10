import Std.Data.HashMap
import Soma.Typing.Kind
import Soma.Typing.TyCon

namespace Soma.Typing

/-- Star-kinded primitive types (kind *) -/
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

end StarPrimitive

/-- Higher-kinded primitive types (kind * -> *) -/
inductive HigherPrimitive where
  | array
  | ref
  | io
  deriving Repr, BEq, Hashable, DecidableEq

namespace HigherPrimitive

def name : HigherPrimitive → String
  | .array => "Array"
  | .ref => "Ref"
  | .io => "IO"

instance : ToString HigherPrimitive := ⟨HigherPrimitive.name⟩

def fromName? : String → Option HigherPrimitive
  | "Array" => some .array
  | "Ref" => some .ref
  | "IO" => some .io
  | _ => none

end HigherPrimitive

/-- Type variable identifier (kind is tracked by position in Ty, not here) -/
structure TyVarId where
  name : String
  id : Nat
  deriving Repr, BEq, Hashable, DecidableEq

namespace TyVarId

instance : ToString TyVarId := ⟨fun v => v.name⟩

def fresh (name : String) (counter : Nat) : TyVarId × Nat :=
  (⟨name, counter⟩, counter + 1)

end TyVarId


/-- Types indexed by their kind - ill-kinded types are unrepresentable -/
inductive Ty : Kind → Type where
  | var (v : TyVarId) : Ty k
  | starPrim (p : StarPrimitive) : Ty .star
  | higherPrim (p : HigherPrimitive) : Ty (.arrow .star .star)
  | con (id : TypeId) : Ty .star
  | app : Ty (.arrow k1 k2) → Ty k1 → Ty k2
  | arrow : Ty .star → Ty .star → Ty .star
  | tuple2 : Ty .star → Ty .star → Ty .star
  | tuple3 : Ty .star → Ty .star → Ty .star → Ty .star
  | tuple4 : Ty .star → Ty .star → Ty .star → Ty .star → Ty .star
  | tuple5 : Ty .star → Ty .star → Ty .star → Ty .star → Ty .star → Ty .star
  | tuple6 : Ty .star → Ty .star → Ty .star → Ty .star → Ty .star → Ty .star → Ty .star
  | tuple7 : Ty .star → Ty .star → Ty .star → Ty .star → Ty .star → Ty .star → Ty .star → Ty .star
  | tuple8 : Ty .star → Ty .star → Ty .star → Ty .star → Ty .star → Ty .star → Ty .star → Ty .star → Ty .star

/-- Monomorphic types (kind *) are the most common -/
abbrev MonoTy := Ty Kind.star

/-- Existential wrapper for types of any kind -/
structure SomeTy where
  kind : Kind
  ty : Ty kind

/-- A substitution maps type variable IDs to monomorphic types -/
abbrev TySubst := Std.HashMap Nat MonoTy

mutual
  /-- Substitute in a monomorphic type -/
  def Ty.subst (t : MonoTy) (σ : TySubst) : MonoTy :=
    match t with
    | .var v => σ.getD v.id (.var v)
    | .starPrim p => .starPrim p
    | .con id => .con id
    | .app f a => .app (Ty.substFun f σ) (Ty.substArg a σ)
    | .arrow from_ to => .arrow (Ty.subst from_ σ) (Ty.subst to σ)
    | .tuple2 a b => .tuple2 (Ty.subst a σ) (Ty.subst b σ)
    | .tuple3 a b c => .tuple3 (Ty.subst a σ) (Ty.subst b σ) (Ty.subst c σ)
    | .tuple4 a b c d => .tuple4 (Ty.subst a σ) (Ty.subst b σ) (Ty.subst c σ) (Ty.subst d σ)
    | .tuple5 a b c d e => .tuple5 (Ty.subst a σ) (Ty.subst b σ) (Ty.subst c σ) (Ty.subst d σ) (Ty.subst e σ)
    | .tuple6 a b c d e f => .tuple6 (Ty.subst a σ) (Ty.subst b σ) (Ty.subst c σ) (Ty.subst d σ) (Ty.subst e σ) (Ty.subst f σ)
    | .tuple7 a b c d e f g => .tuple7 (Ty.subst a σ) (Ty.subst b σ) (Ty.subst c σ) (Ty.subst d σ) (Ty.subst e σ) (Ty.subst f σ) (Ty.subst g σ)
    | .tuple8 a b c d e f g h => .tuple8 (Ty.subst a σ) (Ty.subst b σ) (Ty.subst c σ) (Ty.subst d σ) (Ty.subst e σ) (Ty.subst f σ) (Ty.subst g σ) (Ty.subst h σ)

  /-- Substitute in a function-kinded type -/
  def Ty.substFun : {k1 k2 : Kind} → Ty (.arrow k1 k2) → TySubst → Ty (.arrow k1 k2)
    | _, _, .var v, _ => .var v  -- Variables of higher kind can't be substituted with MonoTy
    | _, _, .higherPrim p, _ => .higherPrim p
    | _, _, .app f a, σ => .app (Ty.substFun f σ) (Ty.substArg a σ)

  /-- Substitute in a type of any kind -/
  def Ty.substArg : {k : Kind} → Ty k → TySubst → Ty k
    | .star, t, σ => Ty.subst t σ
    | .arrow _ _, t, σ => Ty.substFun t σ
end

namespace Ty

/-- Check if type needs parentheses (is compound) -/
def isAtom : {k : Kind} → Ty k → Bool
  | _, .var _ => true
  | _, .starPrim _ => true
  | _, .higherPrim _ => true
  | _, .con _ => true
  | _, .app _ _ => false
  | _, .arrow _ _ => false
  | _, .tuple2 _ _ => true  -- tuples are in parens anyway
  | _, .tuple3 _ _ _ => true
  | _, .tuple4 _ _ _ _ => true
  | _, .tuple5 _ _ _ _ _ => true
  | _, .tuple6 _ _ _ _ _ _ => true
  | _, .tuple7 _ _ _ _ _ _ _ => true
  | _, .tuple8 _ _ _ _ _ _ _ _ => true

/-- Pretty print a type of any kind -/
def toString : {k : Kind} → Ty k → String
  | _, .var v => v.name
  | _, .starPrim p => p.name
  | _, .higherPrim p => p.name
  | _, .con id => id.name
  | _, .app f a =>
    let as := if isAtom a then toString a else s!"({toString a})"
    s!"{toString f} {as}"
  | _, .arrow from_ to =>
    let fromStr := if isAtom from_ then toString from_ else s!"({toString from_})"
    s!"{fromStr} -> {toString to}"
  | _, .tuple2 a b => s!"({toString a}, {toString b})"
  | _, .tuple3 a b c => s!"({toString a}, {toString b}, {toString c})"
  | _, .tuple4 a b c d => s!"({toString a}, {toString b}, {toString c}, {toString d})"
  | _, .tuple5 a b c d e => s!"({toString a}, {toString b}, {toString c}, {toString d}, {toString e})"
  | _, .tuple6 a b c d e f => s!"({toString a}, {toString b}, {toString c}, {toString d}, {toString e}, {toString f})"
  | _, .tuple7 a b c d e f g => s!"({toString a}, {toString b}, {toString c}, {toString d}, {toString e}, {toString f}, {toString g})"
  | _, .tuple8 a b c d e f g h => s!"({toString a}, {toString b}, {toString c}, {toString d}, {toString e}, {toString f}, {toString g}, {toString h})"

instance : ToString (Ty k) := ⟨Ty.toString⟩

def int : MonoTy := .starPrim .int
def long : MonoTy := .starPrim .long
def short : MonoTy := .starPrim .short
def byte : MonoTy := .starPrim .byte
def float : MonoTy := .starPrim .float
def double : MonoTy := .starPrim .double
def bool : MonoTy := .starPrim .bool
def string : MonoTy := .starPrim .string
def unit : MonoTy := .starPrim .unit
def closurePtr : MonoTy := .starPrim .closurePtr
def ptr : MonoTy := .starPrim .ptr

/-- Array type constructor (kind * -> *) -/
def arrayCon : Ty (.arrow .star .star) := .higherPrim .array

/-- Construct Array a -/
def array (elem : MonoTy) : MonoTy := .app arrayCon elem

/-- Ref type constructor (kind * -> *) -/
def refCon : Ty (.arrow .star .star) := .higherPrim .ref

/-- Construct Ref a -/
def ref (elem : MonoTy) : MonoTy := .app refCon elem

/-- IO type constructor (kind * -> *) -/
def ioCon : Ty (.arrow .star .star) := .higherPrim .io

/-- Construct IO a -/
def io (elem : MonoTy) : MonoTy := .app ioCon elem

/-- Construct a tuple type from an array of element types -/
def tuple (elements : Array MonoTy) : MonoTy :=
  match h : elements.size with
  | 0 => unit
  | 1 => elements[0]'(by omega)
  | 2 => .tuple2 (elements[0]'(by omega)) (elements[1]'(by omega))
  | 3 => .tuple3 (elements[0]'(by omega)) (elements[1]'(by omega)) (elements[2]'(by omega))
  | 4 => .tuple4 (elements[0]'(by omega)) (elements[1]'(by omega)) (elements[2]'(by omega)) (elements[3]'(by omega))
  | 5 => .tuple5 (elements[0]'(by omega)) (elements[1]'(by omega)) (elements[2]'(by omega)) (elements[3]'(by omega)) (elements[4]'(by omega))
  | 6 => .tuple6 (elements[0]'(by omega)) (elements[1]'(by omega)) (elements[2]'(by omega)) (elements[3]'(by omega)) (elements[4]'(by omega)) (elements[5]'(by omega))
  | 7 => .tuple7 (elements[0]'(by omega)) (elements[1]'(by omega)) (elements[2]'(by omega)) (elements[3]'(by omega)) (elements[4]'(by omega)) (elements[5]'(by omega)) (elements[6]'(by omega))
  | 8 => .tuple8 (elements[0]'(by omega)) (elements[1]'(by omega)) (elements[2]'(by omega)) (elements[3]'(by omega)) (elements[4]'(by omega)) (elements[5]'(by omega)) (elements[6]'(by omega)) (elements[7]'(by omega))
  | _ + 9 =>
    -- For tuples larger than 8, nest: (first8..., rest...)
    let t8 := tuple8
      (elements[0]'(by omega)) (elements[1]'(by omega)) (elements[2]'(by omega)) (elements[3]'(by omega))
      (elements[4]'(by omega)) (elements[5]'(by omega)) (elements[6]'(by omega)) (elements[7]'(by omega))
    let rest := elements.extract 8 elements.size
    have : rest.size < elements.size := by
      rw [Array.size_extract]
      omega
    .tuple2 t8 (tuple rest)
termination_by elements.size

/-- Is this a function type? -/
def isArrow : MonoTy → Bool
  | .arrow _ _ => true
  | _ => false

/-- Is this an array type? -/
def isArray : MonoTy → Bool
  | .app (.higherPrim .array) _ => true
  | _ => false

/-- Extract element type from Array a -/
def arrayElem? : MonoTy → Option MonoTy
  | .app (.higherPrim .array) elem => some elem
  | _ => none

/-- Is this a ref type? -/
def isRef : MonoTy → Bool
  | .app (.higherPrim .ref) _ => true
  | _ => false

/-- Is this an IO type? -/
def isIO : MonoTy → Bool
  | .app (.higherPrim .io) _ => true
  | _ => false

/-- Is this a tuple type? -/
def isTuple : MonoTy → Bool
  | .tuple2 _ _ => true
  | .tuple3 _ _ _ => true
  | .tuple4 _ _ _ _ => true
  | .tuple5 _ _ _ _ _ => true
  | .tuple6 _ _ _ _ _ _ => true
  | .tuple7 _ _ _ _ _ _ _ => true
  | .tuple8 _ _ _ _ _ _ _ _ => true
  | _ => false

/-- Get tuple arity (0 if not a tuple) -/
def tupleArity : MonoTy → Nat
  | .tuple2 _ _ => 2
  | .tuple3 _ _ _ => 3
  | .tuple4 _ _ _ _ => 4
  | .tuple5 _ _ _ _ _ => 5
  | .tuple6 _ _ _ _ _ _ => 6
  | .tuple7 _ _ _ _ _ _ _ => 7
  | .tuple8 _ _ _ _ _ _ _ _ => 8
  | _ => 0

/-- Extract tuple elements (empty if not a tuple) -/
def tupleElems : MonoTy → Array MonoTy
  | .tuple2 a b => #[a, b]
  | .tuple3 a b c => #[a, b, c]
  | .tuple4 a b c d => #[a, b, c, d]
  | .tuple5 a b c d e => #[a, b, c, d, e]
  | .tuple6 a b c d e f => #[a, b, c, d, e, f]
  | .tuple7 a b c d e f g => #[a, b, c, d, e, f, g]
  | .tuple8 a b c d e f g h => #[a, b, c, d, e, f, g, h]
  | _ => #[]

/-- Is this a numeric type? -/
def isNumeric : MonoTy → Bool
  | .starPrim .int => true
  | .starPrim .long => true
  | .starPrim .short => true
  | .starPrim .byte => true
  | .starPrim .float => true
  | .starPrim .double => true
  | _ => false

/-- Is this an integer type? -/
def isIntegral : MonoTy → Bool
  | .starPrim .int => true
  | .starPrim .long => true
  | .starPrim .short => true
  | .starPrim .byte => true
  | _ => false

/-- Is this a floating-point type? -/
def isFloating : MonoTy → Bool
  | .starPrim .float => true
  | .starPrim .double => true
  | _ => false

/-- Split a function type into (arg types, return type) -/
def splitArrow : MonoTy → Array MonoTy × MonoTy
  | .arrow arg rest =>
    let (args, ret) := splitArrow rest
    (#[arg] ++ args, ret)
  | t => (#[], t)

/-- Count the arity of a function type -/
def arrowArity : MonoTy → Nat
  | .arrow _ rest => 1 + arrowArity rest
  | _ => 0

/-- Build a function type from argument types and return type -/
def mkArrow (args : Array MonoTy) (ret : MonoTy) : MonoTy :=
  args.foldr (init := ret) fun arg acc => .arrow arg acc

/-- Get the return type of a function (the type itself if not a function) -/
def returnType : MonoTy → MonoTy
  | .arrow _ rest => returnType rest
  | t => t

/-- Get all type variables in a type of any kind -/
def freeVars : {k : Kind} → Ty k → Array TyVarId
  | _, .var v => #[v]
  | _, .starPrim _ => #[]
  | _, .higherPrim _ => #[]
  | _, .con _ => #[]
  | _, .app f a => freeVars f ++ freeVars a
  | _, .arrow from_ to => freeVars from_ ++ freeVars to
  | _, .tuple2 a b => freeVars a ++ freeVars b
  | _, .tuple3 a b c => freeVars a ++ freeVars b ++ freeVars c
  | _, .tuple4 a b c d => freeVars a ++ freeVars b ++ freeVars c ++ freeVars d
  | _, .tuple5 a b c d e => freeVars a ++ freeVars b ++ freeVars c ++ freeVars d ++ freeVars e
  | _, .tuple6 a b c d e f => freeVars a ++ freeVars b ++ freeVars c ++ freeVars d ++ freeVars e ++ freeVars f
  | _, .tuple7 a b c d e f g => freeVars a ++ freeVars b ++ freeVars c ++ freeVars d ++ freeVars e ++ freeVars f ++ freeVars g
  | _, .tuple8 a b c d e f g h => freeVars a ++ freeVars b ++ freeVars c ++ freeVars d ++ freeVars e ++ freeVars f ++ freeVars g ++ freeVars h

/-- Check if a type has any type variables -/
def hasVars (t : Ty k) : Bool := !t.freeVars.isEmpty

/-- Get unique type variables (by id) -/
def freeVarsUnique (t : Ty k) : Array TyVarId :=
  let vars := t.freeVars
  vars.foldl (init := #[]) fun acc v =>
    if acc.any (·.id == v.id) then acc else acc.push v

/-- Apply a single substitution -/
def substSingle (t : MonoTy) (varId : Nat) (replacement : MonoTy) : MonoTy :=
  t.subst (({} : TySubst).insert varId replacement)

/-- Heterogeneous equality for types (returns false if kinds differ) -/
def heq : {k1 k2 : Kind} → Ty k1 → Ty k2 → Bool
  | _, _, .var v1, .var v2 => v1 == v2
  | _, _, .starPrim p1, .starPrim p2 => p1 == p2
  | _, _, .higherPrim p1, .higherPrim p2 => p1 == p2
  | _, _, .con id1, .con id2 => id1 == id2
  | _, _, .app f1 a1, .app f2 a2 => heq f1 f2 && heq a1 a2
  | _, _, .arrow from1 to1, .arrow from2 to2 => heq from1 from2 && heq to1 to2
  | _, _, .tuple2 a1 b1, .tuple2 a2 b2 => heq a1 a2 && heq b1 b2
  | _, _, .tuple3 a1 b1 c1, .tuple3 a2 b2 c2 => heq a1 a2 && heq b1 b2 && heq c1 c2
  | _, _, .tuple4 a1 b1 c1 d1, .tuple4 a2 b2 c2 d2 => heq a1 a2 && heq b1 b2 && heq c1 c2 && heq d1 d2
  | _, _, .tuple5 a1 b1 c1 d1 e1, .tuple5 a2 b2 c2 d2 e2 => heq a1 a2 && heq b1 b2 && heq c1 c2 && heq d1 d2 && heq e1 e2
  | _, _, .tuple6 a1 b1 c1 d1 e1 f1, .tuple6 a2 b2 c2 d2 e2 f2 => heq a1 a2 && heq b1 b2 && heq c1 c2 && heq d1 d2 && heq e1 e2 && heq f1 f2
  | _, _, .tuple7 a1 b1 c1 d1 e1 f1 g1, .tuple7 a2 b2 c2 d2 e2 f2 g2 => heq a1 a2 && heq b1 b2 && heq c1 c2 && heq d1 d2 && heq e1 e2 && heq f1 f2 && heq g1 g2
  | _, _, .tuple8 a1 b1 c1 d1 e1 f1 g1 h1, .tuple8 a2 b2 c2 d2 e2 f2 g2 h2 => heq a1 a2 && heq b1 b2 && heq c1 c2 && heq d1 d2 && heq e1 e2 && heq f1 f2 && heq g1 g2 && heq h1 h2
  | _, _, _, _ => false

/-- Check equality of types at the same kind -/
def beq (t1 t2 : Ty k) : Bool := heq t1 t2

instance : BEq (Ty k) := ⟨Ty.beq⟩

end Ty

end Soma.Typing
