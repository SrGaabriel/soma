import Std.Data.HashMap
import Kenosis

open Kenosis

namespace Somac.Alloy

/-- A local value in SSA form (assigned exactly once) -/
structure LocalId where
  id : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace LocalId

instance : ToString LocalId where
  toString v := s!"%{v.id}"

end LocalId

/-- A basic block identifier -/
structure BlockId where
  id : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace BlockId

def entry : BlockId := ⟨0⟩

instance : ToString BlockId where
  toString b := s!"bb{b.id}"

end BlockId

/-- A function identifier (index into the module's function table) -/
structure FuncId where
  id : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace FuncId

instance : ToString FuncId where
  toString f := s!"@fn{f.id}"

end FuncId

/-- A global constant identifier -/
structure GlobalId where
  id : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace GlobalId

instance : ToString GlobalId where
  toString g := s!"@g{g.id}"

end GlobalId

/-- Primitive types at the Alloy level -/
inductive PrimTy where
  | i8 | i16 | i32 | i64
  | u8 | u16 | u32 | u64
  | f32 | f64
  | bool
  | unit
  | world
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace PrimTy

def bitWidth : PrimTy → Nat
  | .i8 | .u8 => 8
  | .i16 | .u16 => 16
  | .i32 | .u32 | .f32 => 32
  | .i64 | .u64 | .f64 => 64
  | .bool => 1
  | .unit | .world => 0

def isSigned : PrimTy → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | _ => false

/-- True iff this primitive has zero runtime representation -/
def isZeroWidth : PrimTy → Bool
  | .world => true
  | .unit => true
  | _ => false

instance : ToString PrimTy where
  toString
    | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
    | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
    | .f32 => "f32" | .f64 => "f64"
    | .bool => "bool"
    | .unit => "unit"
    | .world => "world"

end PrimTy

/-- Alloy types -/
inductive Ty : Nat → Type where
  /-- Primitive types -/
  | prim : PrimTy → Ty n
  /-- Pointer to a value of type t -/
  | ptr : Ty n → Ty n
  /-- Raw pointer (void*) -/
  | rawPtr : Ty n
  /-- Function pointer: (args) -> ret -/
  | funcPtr : Array (Ty n) → Ty n → Ty n
  /-- Struct type (product) with named fields -/
  | struct : Array (String × Ty n) → Ty n
  /-- Array type with static size -/
  | array : Ty n → Nat → Ty n
  /-- Tagged union (for ADTs): tag type + variant payloads -/
  | tagged : Ty n → Array (Nat × Array (Ty n)) → Ty n
  /-- Closure type: function pointer + environment pointer -/
  | closure : Array (Ty n) → Ty n → Ty n
  /-- Type variable (de Bruijn index into enclosing quantifiers) -/
  | var : Fin n → Ty n
  deriving Repr, Serialize, Deserialize

/-- Ty is always inhabited (by rawPtr) -/
instance : Inhabited (Ty n) where
  default := .rawPtr

/-- A closed (monomorphic) type has no free type variables -/
abbrev ClosedTy := Ty 0

/-- Type environment: maps each of n type variables to a closed type -/
abbrev TyEnv (n : Nat) := Fin n → ClosedTy

/-- Instantiate a type by substituting all type variables -/
partial def instantiate (ty : Ty n) (env : TyEnv n) : ClosedTy :=
  match ty with
  | .prim p => .prim p
  | .ptr t => .ptr (instantiate t env)
  | .rawPtr => .rawPtr
  | .funcPtr args ret =>
      .funcPtr (args.map (instantiate · env)) (instantiate ret env)
  | .struct fields =>
      .struct (fields.map fun (name, t) => (name, instantiate t env))
  | .array elem sz => .array (instantiate elem env) sz
  | .tagged tag variants =>
      .tagged (instantiate tag env)
              (variants.map fun (idx, fields) => (idx, fields.map (instantiate · env)))
  | .closure args ret =>
      .closure (args.map (instantiate · env)) (instantiate ret env)
  | .var i => env i

/-- Weaken a type by allowing more type variables (shift all indices) -/
partial def Ty.weaken (ty : Ty n) (extra : Nat) : Ty (n + extra) :=
  match ty with
  | .prim p => .prim p
  | .ptr t => .ptr (t.weaken extra)
  | .rawPtr => .rawPtr
  | .funcPtr args ret => .funcPtr (args.map (·.weaken extra)) (ret.weaken extra)
  | .struct fields => .struct (fields.map fun (name, t) => (name, t.weaken extra))
  | .array elem sz => .array (elem.weaken extra) sz
  | .tagged tag variants =>
      .tagged (tag.weaken extra)
              (variants.map fun (idx, fields) => (idx, fields.map (·.weaken extra)))
  | .closure args ret => .closure (args.map (·.weaken extra)) (ret.weaken extra)
  | .var i => .var ⟨i.val, Nat.lt_add_right extra i.isLt⟩

/-- Embed a closed type into any context (trivially safe) -/
partial def ClosedTy.embed (ty : ClosedTy) : Ty n :=
  match ty with
  | .prim p => .prim p
  | .ptr t => .ptr (embed t)
  | .rawPtr => .rawPtr
  | .funcPtr args ret => .funcPtr (args.map embed) (embed ret)
  | .struct fields => .struct (fields.map fun (name, t) => (name, embed t))
  | .array elem sz => .array (embed elem) sz
  | .tagged tag variants =>
      .tagged (embed tag) (variants.map fun (idx, fields) => (idx, fields.map embed))
  | .closure args ret => .closure (args.map embed) (embed ret)
  | .var i => nomatch i -- impossible

instance : Coe ClosedTy (Ty n) := ⟨ClosedTy.embed⟩

/-- Close a polymorphic type by substituting all type variables with rawPtr -/
def Ty.close (ty : Ty n) : ClosedTy :=
  instantiate ty (fun _ => .rawPtr)

namespace Ty

def bool : Ty n := .prim .bool

/-- Array-backed list: { data: ptr, len: u32, offset: u32 } -/
def somaList : Ty n := .struct #[("data", .rawPtr), ("len", .prim .u32), ("offset", .prim .u32)]

/-- True iff this type has zero runtime representation -/
partial def isZeroWidth (ty : Ty n) : Bool :=
  match ty with
  | .prim p => p.isZeroWidth
  | .struct fields => fields.all fun (_, t) => isZeroWidth t
  | .array elem _ => isZeroWidth elem
  | _ => false

/-- Whether this type supports LLVM arithmetic instructions -/
def isArithmetic (ty : Ty n) : Bool :=
  match ty with
  | .prim _ => true
  | _ => false

/-- Drop zero-width fields from a struct, collapsing it to its non-zero-width elements -/
partial def collapseZeroWidth (ty : Ty n) : Ty n :=
  match ty with
  | .struct fields =>
    let kept := fields.filter fun (_, t) => !isZeroWidth t
    let kept := kept.map fun (name, t) => (name, collapseZeroWidth t)
    if kept.size == 0 then .prim .unit  -- empty struct is unit
    else if kept.size == 1 then kept[0]!.2  -- single field collapses to its type
    else .struct kept
  | .ptr inner => .ptr (collapseZeroWidth inner)
  | .array elem n => .array (collapseZeroWidth elem) n
  | _ => ty

/-- Alignment in bytes -/
partial def alignment (ty : Ty n) (ptrBytes : Nat) : Nat :=
  match ty with
  | .prim p => min ptrBytes ((p.bitWidth + 7) / 8)
  | .ptr _ | .rawPtr | .funcPtr _ _ => ptrBytes
  | .struct fields => fields.foldl (fun acc (_, t) => max acc (t.alignment ptrBytes)) 1
  | .array elem _ => elem.alignment ptrBytes
  | .tagged _ _ =>
      ptrBytes
  | .closure _ _ => ptrBytes
  | .var _ => ptrBytes

mutual
/-- Aligned size of fields laid out as a packed struct (sorted by alignment desc) -/
partial def alignedFieldsSize (fields : Array (Ty n)) (ptrBytes : Nat) : Nat :=
  if fields.isEmpty then 0
  else
    let sorted := fields.qsort fun a b =>
      if a.alignment ptrBytes != b.alignment ptrBytes then a.alignment ptrBytes > b.alignment ptrBytes
      else sizeBytes a ptrBytes > sizeBytes b ptrBytes
    let rawSize := sorted.foldl (fun acc f =>
      let a := max 1 (alignment f ptrBytes)
      ((acc + a - 1) / a) * a + sizeBytes f ptrBytes) 0
    let maxAlign := fields.foldl (fun acc f => max acc (alignment f ptrBytes)) 1
    ((rawSize + maxAlign - 1) / maxAlign) * maxAlign

/-- Size in bytes -/
partial def sizeBytes (ty : Ty n) (ptrBytes : Nat) : Nat :=
  match ty with
  | .prim p => (p.bitWidth + 7) / 8
  | .ptr _ | .rawPtr => ptrBytes
  | .funcPtr _ _ => ptrBytes
  | .struct fields => alignedFieldsSize (fields.map fun (_, t) => t) ptrBytes
  | .array elem size => sizeBytes elem ptrBytes * size
  | .tagged _ _ =>
      alignedFieldsSize (n := n) #[Ty.prim .u32, Ty.rawPtr] ptrBytes
  | .closure _ _ => ptrBytes * 2
  | .var _ => ptrBytes
end

/-- Pretty-print a type -/
partial def toString (ty : Ty n) : String :=
  match ty with
  | .prim p => ToString.toString p
  | .ptr t => s!"*{toString t}"
  | .rawPtr => "rawptr"
  | .funcPtr args ret =>
      let argsStr := String.intercalate ", " (args.toList.map toString)
      s!"fn({argsStr}) -> {toString ret}"
  | .struct fields =>
      let fieldsStr := String.intercalate ", " (fields.toList.map fun (name, t) => s!"{name}: {toString t}")
      s!"\{{fieldsStr}}"
  | .array elem size => s!"[{toString elem}; {size}]"
  | .tagged tag variants =>
      let varStr := String.intercalate " | " (variants.toList.map fun (i, ts) =>
        s!"{i}({String.intercalate ", " (ts.toList.map toString)})")
      s!"tagged<{toString tag}>[{varStr}]"
  | .closure args ret =>
      let argsStr := String.intercalate ", " (args.toList.map toString)
      s!"closure({argsStr}) -> {toString ret}"
  | .var i => s!"α{i.val}"

instance : ToString (Ty n) where
  toString := Ty.toString

/-- Check structural equality -/
partial def beq (a : Ty n) (b : Ty m) : Bool :=
  match a, b with
  | .prim p₁, .prim p₂ => p₁ == p₂
  | .ptr t₁, .ptr t₂ => beq t₁ t₂
  | .rawPtr, .rawPtr => true
  | .funcPtr args₁ ret₁, .funcPtr args₂ ret₂ =>
      args₁.size == args₂.size &&
      (List.zip args₁.toList args₂.toList).all (fun (x, y) => beq x y) &&
      beq ret₁ ret₂
  | .struct fields₁, .struct fields₂ =>
      fields₁.size == fields₂.size &&
      (List.zip fields₁.toList fields₂.toList).all fun ((n₁, t₁), (n₂, t₂)) =>
        n₁ == n₂ && beq t₁ t₂
  | .array elem₁ sz₁, .array elem₂ sz₂ => sz₁ == sz₂ && beq elem₁ elem₂
  | .tagged tag₁ vs₁, .tagged tag₂ vs₂ =>
      beq tag₁ tag₂ && vs₁.size == vs₂.size &&
      (List.zip vs₁.toList vs₂.toList).all fun ((i₁, fs₁), (i₂, fs₂)) =>
        i₁ == i₂ && fs₁.size == fs₂.size &&
        (List.zip fs₁.toList fs₂.toList).all fun (x, y) => beq x y
  | .closure args₁ ret₁, .closure args₂ ret₂ =>
      args₁.size == args₂.size &&
      (List.zip args₁.toList args₂.toList).all (fun (x, y) => beq x y) &&
      beq ret₁ ret₂
  | .var i₁, .var i₂ => i₁.val == i₂.val
  | _, _ => false

instance : BEq (Ty n) where
  beq a b := Ty.beq a b

/-- Check if a type is the array-backed list struct -/
def isSomaList (ty : Ty n) : Bool := ty == somaList

/-- Duplication tier determines how a value is cloned and erased at runtime.

    - **flat**: Register-width values. DUP is a register copy, ERA is a no-op.
      Zero heap interaction, identical to Rust `Copy`.

    - **heap**: Everything else. DUP dispatches based on compile-time type knowledge:
      structs with all-flat fields get inline field-by-field copy; selected heap
      types may use runtime SUP (`supportsLazySup`), and other heap types use
      dedicated type-directed clone paths. -/
inductive DupTier where
  | flat
  | heap
  deriving Repr, BEq, Inhabited

/-- Classify a type into its duplication tier -/
def dupTier : Ty n → DupTier
  | .prim _ => .flat
  | .funcPtr _ _ => .flat
  | _ => .heap

/-- Whether the DUP for this type can be fully inlined at compile time-/
partial def canInlineDup : Ty n → Bool
  | .prim _ => true
  | .funcPtr _ _ => true
  | .struct fields => fields.all fun (_, t) => canInlineDup t
  | .array elem _ => canInlineDup elem
  | .closure _ _ => false -- env is opaque heap pointer
  | .tagged _ _ => false -- potentially recursive ADTs
  | .ptr _ => false -- opaque
  | .rawPtr => false -- opaque
  | .var _ => false -- polymorphic

/-- Whether erasing a value of this type requires cleanup (freeing heap memory) -/
partial def needsErase : Ty n → Bool
  | .prim _ => false
  | .funcPtr _ _ => false
  | .struct fields => fields.any fun (_, t) => needsErase t
  | .array elem _ => needsErase elem
  | .closure _ _ => true -- env_ptr owns heap memory
  | .tagged _ _ => true -- payload is heap-allocated
  | .ptr _ => true
  | .rawPtr => true
  | .var _ => true

/-- Whether this type supports runtime lazy SUP duplication soundly -/
partial def supportsLazySup : Ty n → Bool
  | .closure _ _ => true
  | .var _ => true
  | ty => ty.isSomaList

/-- Number of ptr-sized slots an env of this type occupies inside a closure body -/
def closureEnvSlotCount : Ty n → Nat
  | ty =>
    if ty.isZeroWidth then 0
    else match ty with
      | .struct fields => if fields.size > 1 then fields.size else 1
      | _ => 1

/-- Total ptr-sized slot count for a closure whose env has type `envTy` -/
def closureTotalSlotCount (envTy : Ty n) : Nat :=
  closureEnvSlotCount envTy + 2

/-- Whether a `.clone` of this type can be soundly rewritten to .stackClone` -/
def isStackCloneable : Ty n → Bool
  | .closure _ _ => true
  | _ => false

end Ty

/-- Compile-time constants -/
inductive Const where
  /-- Integer literal -/
  | int (val : Int) (ty : PrimTy)
  /-- Floating point literal -/
  | float (val : Float) (ty : PrimTy)
  /-- Boolean literal -/
  | bool (val : Bool)
  /-- Unit value -/
  | unit
  /-- Null pointer -/
  | null (ty : ClosedTy)
  /-- String literal (index into string table) -/
  | string (idx : Nat) (len : Nat)
  /-- Undefined value (for unitialized memory) -/
  | undef (ty : ClosedTy)
  deriving BEq, Inhabited, Serialize, Deserialize

instance : Repr Const where
  reprPrec c _ := match c with
    | .int v t => s!"Const.int {repr v} {repr t}"
    | .float v t => s!"Const.float {repr v} {repr t}"
    | .bool b => s!"Const.bool {repr b}"
    | .unit => "Const.unit"
    | .null _ => "Const.null _"
    | .string idx len => s!"Const.string {idx} {len}"
    | .undef _ => "Const.undef _"

namespace Const

/-- Type of a constant, when it can be determined without context -/
def ty? : Const → Option ClosedTy
  | .int _ t => some (.prim t)
  | .float _ t => some (.prim t)
  | .bool _ => some (.prim .bool)
  | .unit => some (.prim .unit)
  | .null t => some (.ptr t)
  | .string _ _ => none
  | .undef t => some t

instance : ToString Const where
  toString
    | .int v t => s!"{v}_{t}"
    | .float v t => s!"{v}_{t}"
    | .bool b => if b then "true" else "false"
    | .unit => "()"
    | .null _ => "null"
    | .string idx len => s!"str#{idx}[{len}]"
    | .undef t => s!"undef:{t}"

end Const

/-- An operand is either a local value or a constant -/
inductive Operand where
  | local (id : LocalId)
  | const (c : Const)
  | global (id : GlobalId)
  | func (id : FuncId)
  deriving Repr, BEq, Inhabited, Serialize, Deserialize

namespace Operand

instance : ToString Operand where
  toString
    | .local id => ToString.toString id
    | .const c => ToString.toString c
    | .global id => ToString.toString id
    | .func id => ToString.toString id

end Operand

/-- Binary operations -/
inductive BinOp where
  -- Arithmetic
  | add | sub | mul | div | rem
  -- Bitwise
  | and | or | xor | shl | shr
  -- Comparison (returns bool)
  | eq | ne | lt | le | gt | ge
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace BinOp

def isComparison : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

instance : ToString BinOp where
  toString
    | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .rem => "rem"
    | .and => "and" | .or => "or" | .xor => "xor" | .shl => "shl" | .shr => "shr"
    | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"

end BinOp

/-- Unary operations -/
inductive UnOp (n : Nat) where
  | neg
  | not
  | trunc (to : PrimTy)
  | zext (to : PrimTy)
  | sext (to : PrimTy)
  | itof (to : PrimTy)
  | ftoi (to : PrimTy)
  | bitcast (to : Ty n)
  | ptrtoint (to : PrimTy)
  | inttoptr
  deriving BEq, Inhabited, Serialize, Deserialize

instance : Repr (UnOp n) where
  reprPrec op _ := match op with
    | .neg => "UnOp.neg"
    | .not => "UnOp.not"
    | .trunc t => s!"UnOp.trunc {repr t}"
    | .zext t => s!"UnOp.zext {repr t}"
    | .sext t => s!"UnOp.sext {repr t}"
    | .itof t => s!"UnOp.itof {repr t}"
    | .ftoi t => s!"UnOp.ftoi {repr t}"
    | .bitcast t => s!"UnOp.bitcast {t}"
    | .ptrtoint t => s!"UnOp.ptrtoint {repr t}"
    | .inttoptr => "UnOp.inttoptr"

namespace UnOp

def instantiate (op : UnOp n) (env : TyEnv n) : UnOp 0 :=
  match op with
  | .neg => .neg
  | .not => .not
  | .trunc t => .trunc t
  | .zext t => .zext t
  | .sext t => .sext t
  | .itof t => .itof t
  | .ftoi t => .ftoi t
  | .bitcast t => .bitcast (Somac.Alloy.instantiate t env)
  | .ptrtoint t => .ptrtoint t
  | .inttoptr => .inttoptr

instance : ToString (UnOp n) where
  toString
    | .neg => "neg"
    | .not => "not"
    | .trunc t => s!"trunc.{t}"
    | .zext t => s!"zext.{t}"
    | .sext t => s!"sext.{t}"
    | .itof t => s!"itof.{t}"
    | .ftoi t => s!"ftoi.{t}"
    | .bitcast t => s!"bitcast.{t}"
    | .ptrtoint t => s!"ptrtoint.{t}"
    | .inttoptr => "inttoptr"

end UnOp

/-- FFI/intrinsic operations -/
inductive IntrinsicOp where
  | ptrNull | ptrAdd | ptrDiff | ptrRead | ptrWrite | ptrCast
  | toCString | fromCString | cstringLen
  | strcat | intToString
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace IntrinsicOp

def name : IntrinsicOp → String
  | .ptrNull => "ptr_null" | .ptrAdd => "ptr_add" | .ptrDiff => "ptr_diff"
  | .ptrRead => "ptr_read" | .ptrWrite => "ptr_write" | .ptrCast => "ptr_cast"
  | .toCString => "to_cstring" | .fromCString => "from_cstring" | .cstringLen => "cstring_len"
  | .strcat => "strcat" | .intToString => "int_to_string"

instance : ToString IntrinsicOp where
  toString := IntrinsicOp.name

def hasResult : IntrinsicOp → Bool
  | .ptrWrite => false
  | _ => true

/-- Return type of an intrinsic when known statically -/
def fixedRetTy : IntrinsicOp → Option ClosedTy
  | .ptrNull => some .rawPtr
  | .ptrAdd => some .rawPtr
  | .ptrDiff => some (.prim .i64)
  | .ptrRead => none
  | .ptrWrite => some (.prim .unit)
  | .ptrCast => some .rawPtr
  | .toCString => some .rawPtr
  | .fromCString => none
  | .cstringLen => some (.prim .u64)
  | .strcat => none
  | .intToString => none

/-- True for intrinsics whose return type is the wired-in string layout -/
def returnsString : IntrinsicOp → Bool
  | .fromCString | .strcat | .intToString => true
  | _ => false

end IntrinsicOp

/-- Primitive operations -/
inductive PrimOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  | and | or | not | neg
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace PrimOp

def name : PrimOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod"
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .and => "and" | .or => "or" | .not => "not" | .neg => "neg"

def isBinary : PrimOp → Bool
  | .not | .neg => false
  | _ => true

def isComparison : PrimOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

instance : ToString PrimOp where
  toString := PrimOp.name

end PrimOp

/-- A function reference that may be resolved later -/
inductive FuncRef where
  /-- A resolved local function with known FuncId -/
  | local (id : FuncId)
  /-- Cross-module function reference -/
  | external (qualifiedName : String)
  /-- Intrinsic -/
  | intrinsic (op : IntrinsicOp)
  /-- PrimOp intrinsic -/
  | primOp (op : PrimOp)
  /-- External C function used as a value -/
  | externC (name : String)
  deriving Repr, BEq, Hashable, Inhabited, Serialize, Deserialize

namespace FuncRef

/-- Get the FuncId if this is a resolved local reference -/
def toFuncId? : FuncRef → Option FuncId
  | .local id => some id
  | _ => none

instance : ToString FuncRef where
  toString
    | .local id => ToString.toString id
    | .external name => s!"@extern\"{name}\""
    | .intrinsic op => s!"@intrinsic.{op}"
    | .primOp op => s!"@primop.{op}"
    | .externC name => s!"@externc\"{name}\""

end FuncRef

/-- Mix two hash values -/
def mixHash (a b : UInt64) : UInt64 :=
  a ^^^ (b * 0x9e3779b97f4a7c15 + (a <<< (6 : UInt64)) + (a >>> (2 : UInt64)))

/-- Hash a closed type -/
partial def hashClosedTy (ty : ClosedTy) : UInt64 :=
  match ty with
  | .prim p => mixHash 1 (hash p)
  | .ptr t => mixHash 2 (hashClosedTy t)
  | .rawPtr => 3
  | .funcPtr args ret =>
      let argsHash := args.foldl (init := (0 : UInt64)) fun acc t => mixHash acc (hashClosedTy t)
      mixHash 4 (mixHash argsHash (hashClosedTy ret))
  | .struct fields =>
      let fieldsHash := fields.foldl (init := (0 : UInt64)) fun acc (n, t) =>
        mixHash acc (mixHash (hash n) (hashClosedTy t))
      mixHash 5 fieldsHash
  | .array elem size => mixHash 6 (mixHash (hashClosedTy elem) (hash size))
  | .tagged tag variants =>
      let variantsHash := variants.foldl (init := (0 : UInt64)) fun acc (i, fields) =>
        let fieldsH := fields.foldl (init := hash i) fun a t => mixHash a (hashClosedTy t)
        mixHash acc fieldsH
      mixHash 7 (mixHash (hashClosedTy tag) variantsHash)
  | .closure args ret =>
      let argsHash := args.foldl (init := (0 : UInt64)) fun acc t => mixHash acc (hashClosedTy t)
      mixHash 8 (mixHash argsHash (hashClosedTy ret))
  | .var i => nomatch i

instance : Hashable ClosedTy where
  hash := hashClosedTy

/-- Hash an array of closed types -/
def hashClosedTyArray (tys : Array ClosedTy) : UInt64 :=
  tys.foldl (init := (0 : UInt64)) fun acc ty => mixHash acc (hashClosedTy ty)

/-- Wired-in function roles at the Alloy IR level -/
inductive WiredFunc where
  | listMap
  | listFilter
  | listFoldl
  | listFoldr
  | listSum
  | listProduct
  | listLength
  | listAny
  | listAll
  | listReverse
  | pureIO
  | bindIO
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

end Somac.Alloy
