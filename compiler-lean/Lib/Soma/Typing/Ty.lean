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

/-- Type variable identifier with kind information.

    Type variables now track their kind explicitly, ensuring that
    we can always query a variable's kind without needing context.
-/
structure TyVarId where
  name : String
  id : Nat
  kind : Kind := .star
  deriving Repr

namespace TyVarId

/-- Equality based on id only, name and kind are metadata -/
instance : BEq TyVarId where
  beq v1 v2 := v1.id == v2.id

instance : Hashable TyVarId where
  hash v := hash v.id

instance : DecidableEq TyVarId := fun v1 v2 =>
  match decEq v1.name v2.name, decEq v1.id v2.id, decEq v1.kind v2.kind with
  | isTrue h1, isTrue h2, isTrue h3 =>
    isTrue (by cases v1; cases v2; simp_all)
  | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
  | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
  | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

instance : ToString TyVarId := ⟨fun v => v.name⟩

/-- Generate a fresh type variable -/
def fresh (name : String) (counter : Nat) (kind : Kind := .star) : TyVarId × Nat :=
  (⟨name, counter, kind⟩, counter + 1)

/-- Create a star-kinded type variable -/
def star (name : String) (id : Nat) : TyVarId := ⟨name, id, .star⟩

/-- Check if this is a star-kinded variable -/
def isStar (v : TyVarId) : Bool := v.kind == .star

/-- Check if this is a higher-kinded variable -/
def isHigherKinded (v : TyVarId) : Bool := v.kind != .star

end TyVarId

/-- Types indexed by their kind -/
inductive Ty : Kind → Type where
  | var (v : TyVarId) : Ty k
  | starPrim (p : StarPrimitive) : Ty .star
  | higherPrim (p : HigherPrimitive) : Ty (.arrow .star .star)
  | userCon (k : Kind) (id : TypeId) : Ty k
  | app : Ty (.arrow k1 k2) → Ty k1 → Ty k2
  | arrow : Ty .star → Ty .star → Ty .star
  | tuple (fst snd : Ty .star) (rest : List (Ty .star)) : Ty .star
  | labelLit (name : String) : Ty .label
  | rowEmpty : Ty .row
  | rowExtend (label : Ty .label) (fieldTy : Ty .star) (tail : Ty .row) : Ty .row
  | record (row : Ty .row) : Ty .star
  | variant (row : Ty .row) : Ty .star

/-- Monomorphic types (kind *) are the most common -/
abbrev MonoTy := Ty Kind.star

/-- Row-kinded types for record polymorphism -/
abbrev RowTy := Ty Kind.row

/-- Label-kinded types for field names -/
abbrev LabelTy := Ty Kind.label

/-- Default inhabited instance for MonoTy, uses unit type -/
instance : Inhabited MonoTy := ⟨.starPrim .unit⟩

/-- Existential wrapper for types of any kind -/
structure SomeTy where
  kind : Kind
  ty : Ty kind

/-- A substitution maps type variable IDs to monomorphic types (legacy) -/
abbrev TySubst := Std.HashMap Nat MonoTy

/-- A kind-polymorphic substitution maps type variable IDs to types of any kind -/
abbrev KindSubst := Std.HashMap Nat SomeTy

/-- Try to cast a SomeTy to a specific kind. Returns none if kinds don't match. -/
def SomeTy.cast? (sty : SomeTy) (k : Kind) : Option (Ty k) :=
  if h : sty.kind = k then some (h ▸ sty.ty) else none

/-- Substitute in a label type using kind-polymorphic substitution -/
def Ty.substLabelK (t : LabelTy) (σ : KindSubst) : LabelTy :=
  match t with
  | .labelLit name => .labelLit name
  | .var v =>
    match σ.get? v.id with
    | some sty =>
      match sty.cast? .label with
      | some ty => ty
      | none => .var v -- Kind mismatch, keep variable
    | none => .var v
  | .app _ _ => t
  | .userCon _ _ => t

mutual
  /-- Substitute in a monomorphic type using kind-polymorphic substitution -/
  def Ty.substK (t : MonoTy) (σ : KindSubst) : MonoTy :=
    match t with
    | .var v =>
      match σ.get? v.id with
      | some sty =>
        match sty.cast? .star with
        | some ty => ty
        | none => .var v -- Kind mismatch, keep variable
      | none => .var v
    | .starPrim p => .starPrim p
    | .userCon _ id => .userCon .star id
    | .app f a => .app (Ty.substFunK f σ) (Ty.substArgK a σ)
    | .arrow from_ to => .arrow (Ty.substK from_ σ) (Ty.substK to σ)
    | .tuple fst snd rest =>
      .tuple (Ty.substK fst σ) (Ty.substK snd σ) (Ty.substListK rest σ)
    | .record row => .record (Ty.substRowK row σ)
    | .variant row => .variant (Ty.substRowK row σ)

  /-- Substitute in a list of types -/
  def Ty.substListK (ts : List MonoTy) (σ : KindSubst) : List MonoTy :=
    match ts with
    | [] => []
    | t :: rest => Ty.substK t σ :: Ty.substListK rest σ

  /-- Substitute in a function-kinded type using kind-polymorphic substitution -/
  def Ty.substFunK : {k1 k2 : Kind} → Ty (.arrow k1 k2) → KindSubst → Ty (.arrow k1 k2)
    | k1, k2, .var v, σ =>
      match σ.get? v.id with
      | some sty =>
        match sty.cast? (.arrow k1 k2) with
        | some ty => ty
        | none => .var v -- Kind mismatch, keep variable
      | none => .var v
    | _, _, .higherPrim p, _ => .higherPrim p
    | _, _, .userCon _ id, _ => .userCon _ id
    | _, _, .app f a, σ => .app (Ty.substFunK f σ) (Ty.substArgK a σ)

  /-- Substitute in a row type using kind-polymorphic substitution -/
  def Ty.substRowK (t : RowTy) (σ : KindSubst) : RowTy :=
    match t with
    | .rowEmpty => .rowEmpty
    | .rowExtend label ty tail =>
      .rowExtend (Ty.substLabelK label σ) (Ty.substK ty σ) (Ty.substRowK tail σ)
    | .var v =>
      match σ.get? v.id with
      | some sty =>
        match sty.cast? .row with
        | some ty => ty
        | none => .var v -- Kind mismatch, keep variable
      | none => .var v
    | .app _ _ => t
    | .userCon _ _ => t

  /-- Substitute in a type of any kind using kind-polymorphic substitution -/
  def Ty.substArgK : {k : Kind} → Ty k → KindSubst → Ty k
    | .star, t, σ => Ty.substK t σ
    | .arrow _ _, t, σ => Ty.substFunK t σ
    | .row, t, σ => Ty.substRowK t σ
    | .label, t, σ => Ty.substLabelK t σ
end

/-- Substitute in a label type (todo: remove since labels don't contain star-kinded vars) -/
def Ty.substLabel (t : LabelTy) (_σ : TySubst) : LabelTy :=
  match t with
  | .labelLit name => .labelLit name
  | .var v => .var v -- Label variables can't be substituted with MonoTy
  | .app _ _ => t
  | .userCon _ _ => t

mutual
  /-- Substitute in a monomorphic type (legacy, monomorphic-only substitution) -/
  def Ty.subst (t : MonoTy) (σ : TySubst) : MonoTy :=
    match t with
    | .var v => σ.getD v.id (.var v)
    | .starPrim p => .starPrim p
    | .userCon _ id => .userCon .star id
    | .app f a => .app (Ty.substFun f σ) (Ty.substArg a σ)
    | .arrow from_ to => .arrow (Ty.subst from_ σ) (Ty.subst to σ)
    | .tuple fst snd rest =>
      .tuple (Ty.subst fst σ) (Ty.subst snd σ) (Ty.substList rest σ)
    | .record row => .record (Ty.substRow row σ)
    | .variant row => .variant (Ty.substRow row σ)

  /-- Substitute in a list of types (legacy) -/
  def Ty.substList (ts : List MonoTy) (σ : TySubst) : List MonoTy :=
    match ts with
    | [] => []
    | t :: rest => Ty.subst t σ :: Ty.substList rest σ

  /-- Substitute in a function-kinded type -/
  def Ty.substFun : {k1 k2 : Kind} → Ty (.arrow k1 k2) → TySubst → Ty (.arrow k1 k2)
    | _, _, .var v, _ => .var v  -- Variables of higher kind can't be substituted with MonoTy
    | _, _, .higherPrim p, _ => .higherPrim p
    | _, _, .userCon _ id, _ => .userCon _ id
    | _, _, .app f a, σ => .app (Ty.substFun f σ) (Ty.substArg a σ)

  /-- Substitute in a row type (todo: remove legacy) -/
  def Ty.substRow (t : RowTy) (σ : TySubst) : RowTy :=
    match t with
    | .rowEmpty => .rowEmpty
    | .rowExtend label ty tail =>
      .rowExtend (Ty.substLabel label σ) (Ty.subst ty σ) (Ty.substRow tail σ)
    | .var v => .var v  -- Row variables can't be substituted with MonoTy
    | .app _ _ => t
    | .userCon _ _ => t

  /-- Substitute in a type of any kind (legacy) -/
  def Ty.substArg : {k : Kind} → Ty k → TySubst → Ty k
    | .star, t, σ => Ty.subst t σ
    | .arrow _ _, t, σ => Ty.substFun t σ
    | .row, t, σ => Ty.substRow t σ
    | .label, t, σ => Ty.substLabel t σ
end

namespace Ty

/-- Check if type needs parentheses (is compound) -/
def isAtom : {k : Kind} → Ty k → Bool
  | _, .var _ => true
  | _, .starPrim _ => true
  | _, .higherPrim _ => true
  | _, .userCon _ _ => true
  | _, .app _ _ => false
  | _, .arrow _ _ => false
  | _, .tuple _ _ _ => true  -- tuples are in parens anyway
  | _, .labelLit _ => true
  | _, .rowEmpty => true
  | _, .rowExtend _ _ _ => false
  | _, .record _ => true
  | _, .variant _ => true

/-- Helper to get label string -/
def labelToString (t : LabelTy) : String :=
  match t with
  | .labelLit name => name
  | .var v => v.name
  | .app _ _ => "<impossible>"
  | .userCon _ _ => "<impossible>"

mutual
/-- Pretty print a row type as comma-separated fields (for records) -/
partial def rowToStringAux (row : RowTy) : String :=
  match row with
  | .rowEmpty => ""
  | .var v => "| " ++ v.name
  | .rowExtend label ty tail =>
    let labelStr := labelToString label
    let fieldStr := labelStr ++ " :: " ++ toStringAux ty
    match tail with
    | .rowEmpty => fieldStr
    | .var v => fieldStr ++ " | " ++ v.name
    | .rowExtend _ _ _ => fieldStr ++ ", " ++ rowToStringAux tail
    | .app _ _ => fieldStr
    | .userCon _ _ => fieldStr
  | .app _ _ => "<impossible>"
  | .userCon _ _ => "<impossible>"

/-- Pretty print a row type as pipe-separated cases (for variants) -/
partial def variantRowToStringAux (row : RowTy) : String :=
  match row with
  | .rowEmpty => ""
  | .var v => "| " ++ v.name
  | .rowExtend label ty tail =>
    let labelStr := labelToString label
    let caseStr := labelStr ++ " :: " ++ toStringAux ty
    match tail with
    | .rowEmpty => caseStr
    | .var v => caseStr ++ " | " ++ v.name
    | .rowExtend _ _ _ => caseStr ++ " | " ++ variantRowToStringAux tail
    | .app _ _ => caseStr
    | .userCon _ _ => caseStr
  | .app _ _ => "<impossible>"
  | .userCon _ _ => "<impossible>"

/-- Pretty print a type of any kind -/
partial def toStringAux : {k : Kind} → Ty k → String
  | _, .var v => v.name
  | _, .starPrim p => p.name
  | _, .higherPrim p => p.name
  | _, .userCon _ id => id.name
  | _, .app f a =>
    let as := if isAtom a then toStringAux a else "(" ++ toStringAux a ++ ")"
    toStringAux f ++ " " ++ as
  | _, .arrow from_ to =>
    let fromStr := if isAtom from_ then toStringAux from_ else "(" ++ toStringAux from_ ++ ")"
    fromStr ++ " -> " ++ toStringAux to
  | _, .tuple fst snd rest =>
    let elemStrs := [toStringAux fst, toStringAux snd] ++ rest.map toStringAux
    "(" ++ ", ".intercalate elemStrs ++ ")"
  | _, .labelLit name => "'" ++ name
  | _, .rowEmpty => "{}"
  | _, .rowExtend (label : LabelTy) (ty : MonoTy) (tail : RowTy) =>
    let rowStr := rowToStringAux (Ty.rowExtend label ty tail)
    "{ " ++ rowStr ++ " }"
  | _, .record (row : RowTy) =>
    let rowStr := rowToStringAux row
    "{ " ++ rowStr ++ " }"
  | _, .variant (row : RowTy) =>
    match row with
    | .rowEmpty => "< >"
    | _ => "< " ++ variantRowToStringAux row ++ " >"
end

def toString : {k : Kind} → Ty k → String := toStringAux

instance : ToString (Ty k) := ⟨Ty.toString⟩

/-- Convenience constructor for star-kinded user types. -/
def con (id : TypeId) : MonoTy := .userCon .star id

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
def mkTuple (elements : Array MonoTy) : MonoTy :=
  match elements.toList with
  | [] => unit
  | [x] => x
  | fst :: snd :: rest => .tuple fst snd rest

/-- Create a 2-tuple type -/
def tuple2 (a b : MonoTy) : MonoTy := .tuple a b []

/-- Create a 3-tuple type -/
def tuple3 (a b c : MonoTy) : MonoTy := .tuple a b [c]

/-- Create a 4-tuple type -/
def tuple4 (a b c d : MonoTy) : MonoTy := .tuple a b [c, d]

/-- Create a 5-tuple type -/
def tuple5 (a b c d e : MonoTy) : MonoTy := .tuple a b [c, d, e]

/-- Create a 6-tuple type -/
def tuple6 (a b c d e f : MonoTy) : MonoTy := .tuple a b [c, d, e, f]

/-- Create a 7-tuple type -/
def tuple7 (a b c d e f g : MonoTy) : MonoTy := .tuple a b [c, d, e, f, g]

/-- Create a 8-tuple type -/
def tuple8 (a b c d e f g h : MonoTy) : MonoTy := .tuple a b [c, d, e, f, g, h]

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
  | .tuple _ _ _ => true
  | _ => false

/-- Get tuple arity (0 if not a tuple) -/
def tupleArity : MonoTy → Nat
  | .tuple _ _ rest => 2 + rest.length
  | _ => 0

/-- Extract tuple elements (empty if not a tuple) -/
def tupleElems : MonoTy → Array MonoTy
  | .tuple fst snd rest => #[fst, snd] ++ rest.toArray
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

/-- Extract return type from a function type by stripping exactly n arrows -/
def stripArrows (ty : MonoTy) (n : Nat) : MonoTy :=
  match n, ty with
  | 0, _ => ty
  | n+1, .arrow _ to => stripArrows to n
  | _, _ => ty

/-- Get all type variables in a type of any kind -/
def freeVars : {k : Kind} → Ty k → Array TyVarId
  | _, .var v => #[v]
  | _, .starPrim _ => #[]
  | _, .higherPrim _ => #[]
  | _, .userCon _ _ => #[]
  | _, .app f a => freeVars f ++ freeVars a
  | _, .arrow from_ to => freeVars from_ ++ freeVars to
  | _, .tuple fst snd rest =>
    freeVars fst ++ freeVars snd ++ rest.foldl (init := #[]) fun acc t => acc ++ freeVars t
  | _, .labelLit _ => #[]
  | _, .rowEmpty => #[]
  | _, .rowExtend label ty tail => freeVars label ++ freeVars ty ++ freeVars tail
  | _, .record row => freeVars row
  | _, .variant row => freeVars row

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

mutual
/-- Compare two lists of monomorphic types for equality -/
def heqList : List MonoTy → List MonoTy → Bool
  | [], [] => true
  | t1 :: rest1, t2 :: rest2 => heq t1 t2 && heqList rest1 rest2
  | _, _ => false

/-- Heterogeneous equality for types (returns false if kinds differ) -/
def heq : {k1 k2 : Kind} → Ty k1 → Ty k2 → Bool
  | _, _, .var v1, .var v2 => v1 == v2
  | _, _, .starPrim p1, .starPrim p2 => p1 == p2
  | _, _, .higherPrim p1, .higherPrim p2 => p1 == p2
  | _, _, .userCon _ id1, .userCon _ id2 => id1 == id2
  | _, _, .app f1 a1, .app f2 a2 => heq f1 f2 && heq a1 a2
  | _, _, .arrow from1 to1, .arrow from2 to2 => heq from1 from2 && heq to1 to2
  | _, _, .tuple fst1 snd1 rest1, .tuple fst2 snd2 rest2 =>
    heq fst1 fst2 && heq snd1 snd2 && heqList rest1 rest2
  | _, _, .labelLit n1, .labelLit n2 => n1 == n2
  | _, _, .rowEmpty, .rowEmpty => true
  | _, _, .rowExtend l1 t1 r1, .rowExtend l2 t2 r2 =>
    heq l1 l2 && heq t1 t2 && heq r1 r2
  | _, _, .record r1, .record r2 => heq r1 r2
  | _, _, .variant r1, .variant r2 => heq r1 r2
  | _, _, _, _ => false
end

/-- Check equality of types at the same kind -/
def beq (t1 t2 : Ty k) : Bool := heq t1 t2

instance : BEq (Ty k) := ⟨Ty.beq⟩

/-- Hash a type (for use in hash maps) -/
def hash : {k : Kind} → Ty k → UInt64
  | _, .var v => mixHash 0 (Hashable.hash v)
  | _, .starPrim p => mixHash 1 (Hashable.hash p)
  | _, .higherPrim p => mixHash 2 (Hashable.hash p)
  | _, .userCon _ id => mixHash 3 (Hashable.hash id)
  | _, .app f a => mixHash 4 (mixHash (hash f) (hash a))
  | _, .arrow from_ to => mixHash 5 (mixHash (hash from_) (hash to))
  | _, .tuple fst snd rest =>
    let base := mixHash 6 (mixHash (hash fst) (hash snd))
    rest.foldl (init := base) fun acc t => mixHash acc (hash t)
  | _, .labelLit name => mixHash 7 (Hashable.hash name)
  | _, .rowEmpty => 8
  | _, .rowExtend label ty tail => mixHash 9 (mixHash (hash label) (mixHash (hash ty) (hash tail)))
  | _, .record row => mixHash 10 (hash row)
  | _, .variant row => mixHash 11 (hash row)

instance : Hashable (Ty k) := ⟨Ty.hash⟩

/-- Create a label literal -/
def label (name : String) : LabelTy := .labelLit name

/-- Build a closed record type from field list -/
def mkRecord (fields : List (String × MonoTy)) : MonoTy :=
  let row := fields.foldr (init := Ty.rowEmpty) fun (name, ty) acc =>
    Ty.rowExtend (Ty.labelLit name) ty acc
  Ty.record row

/-- Build an open record type (with row variable tail) -/
def mkOpenRecord (fields : List (String × MonoTy)) (tail : RowTy) : MonoTy :=
  let row := fields.foldr (init := tail) fun (name, ty) acc =>
    Ty.rowExtend (Ty.labelLit name) ty acc
  Ty.record row

/-- Check if a type is a record type -/
def isRecord : MonoTy → Bool
  | .record _ => true
  | _ => false

/-- Extract row from record type -/
def recordRow? : MonoTy → Option RowTy
  | .record row => some row
  | _ => none

/-- Build a closed variant type from case list -/
def mkVariant (cases : List (String × MonoTy)) : MonoTy :=
  let row := cases.foldr (init := Ty.rowEmpty) fun (name, ty) acc =>
    Ty.rowExtend (Ty.labelLit name) ty acc
  Ty.variant row

/-- Build an open variant type (with row variable tail) -/
def mkOpenVariant (cases : List (String × MonoTy)) (tail : RowTy) : MonoTy :=
  let row := cases.foldr (init := tail) fun (name, ty) acc =>
    Ty.rowExtend (Ty.labelLit name) ty acc
  Ty.variant row

/-- Check if a type is a variant type -/
def isVariant : MonoTy → Bool
  | .variant _ => true
  | _ => false

/-- Extract row from variant type -/
def variantRow? : MonoTy → Option RowTy
  | .variant row => some row
  | _ => none

/-- Extract label name from a label type -/
def labelName? (t : LabelTy) : Option String :=
  match t with
  | .labelLit name => some name
  | .var _ => none
  | .app _ _ => none
  | .userCon _ _ => none

/-- Collect all concrete labels from a row -/
def rowLabels (row : RowTy) : List String :=
  match row with
  | .rowEmpty => []
  | .rowExtend label _ tail =>
    match labelName? label with
    | some name => name :: rowLabels tail
    | none => rowLabels tail  -- Skip label variables
  | .var _ => [] -- Unknown tail
  | .app _ _ => [] -- Impossible for RowTy
  | .userCon _ _ => [] -- Impossible for RowTy

/-- Look up a field by concrete label in a row, returns (fieldType, remainingRow) if found -/
def rowLookup (name : String) (row : RowTy) : Option (MonoTy × RowTy) :=
  match row with
  | .rowEmpty => none
  | .rowExtend label ty tail =>
    match labelName? label with
    | some n =>
      if n == name then some (ty, tail)
      else do
        let (fieldTy, rest) ← rowLookup name tail
        some (fieldTy, .rowExtend label ty rest)
    | none => none
  | .var _ => none
  | .app _ _ => none
  | .userCon _ _ => none

/-- Look up a field name in a type variable environment and return the appropriate label -/
def lookupOrLiteralLabel (fieldName : String) (tyVars : Std.HashMap String TyVarId) : LabelTy :=
  match tyVars.get? fieldName with
  | some tyVarId =>
    if tyVarId.kind == Kind.label then
      .var ⟨tyVarId.name, tyVarId.id, Kind.label⟩
    else .labelLit fieldName
  | none => .labelLit fieldName

/-- Check if a row is closed (ends in rowEmpty, not a variable) -/
def isClosedRow (row : RowTy) : Bool :=
  match row with
  | .rowEmpty => true
  | .rowExtend _ _ tail => isClosedRow tail
  | .var _ => false
  | .app _ _ => false
  | .userCon _ _ => false

/-- Count the number of fields in a row (only counts concrete extensions) -/
def rowFieldCount (row : RowTy) : Nat :=
  match row with
  | .rowEmpty => 0
  | .rowExtend _ _ tail => 1 + rowFieldCount tail
  | .var _ => 0
  | .app _ _ => 0
  | .userCon _ _ => 0

end Ty

end Soma.Typing
