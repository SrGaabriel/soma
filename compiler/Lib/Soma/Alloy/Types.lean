/-
  Alloy IR: Mid-level Intermediate Representation for Soma

  Alloy is an imperative, SSA-based IR positioned between Circuit IR (interaction nets)
  and LLVM IR. It serves as the target for Circuit IR lowering and the source for
  native code generation.

  Key design principles:
  1. SSA form: Every value is defined exactly once
  2. Explicit control flow: Basic blocks with terminators
  3. Explicit memory: Allocations, loads, stores
  4. Explicit closures: Environment capture and function pointers
  5. No interaction net concepts: DUP/SUP lowered to explicit copies/allocations

  The name "Alloy" reflects its role as a refined, hardened form of the higher-level
  Circuit IR - just as an alloy is a refined mixture of metals.
-/

import Std.Data.HashMap

namespace Soma.Alloy

/-! ## Value Identifiers -/

/-- A local value in SSA form (assigned exactly once) -/
structure LocalId where
  id : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace LocalId

def zero : LocalId := ⟨0⟩

instance : ToString LocalId where
  toString v := s!"%{v.id}"

end LocalId

/-- A basic block identifier -/
structure BlockId where
  id : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace BlockId

def entry : BlockId := ⟨0⟩

instance : ToString BlockId where
  toString b := s!"bb{b.id}"

end BlockId

/-- A function identifier (index into the module's function table) -/
structure FuncId where
  id : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace FuncId

instance : ToString FuncId where
  toString f := s!"@fn{f.id}"

end FuncId

/-- A global constant identifier -/
structure GlobalId where
  id : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace GlobalId

instance : ToString GlobalId where
  toString g := s!"@g{g.id}"

end GlobalId

/-! ## Types -/

/-- Primitive types at the Alloy level -/
inductive PrimTy where
  | i8 | i16 | i32 | i64
  | u8 | u16 | u32 | u64
  | f32 | f64
  | bool
  | unit
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace PrimTy

def bitWidth : PrimTy → Nat
  | .i8 | .u8 => 8
  | .i16 | .u16 => 16
  | .i32 | .u32 | .f32 => 32
  | .i64 | .u64 | .f64 => 64
  | .bool => 1
  | .unit => 0

def isSigned : PrimTy → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | _ => false

def isFloat : PrimTy → Bool
  | .f32 | .f64 => true
  | _ => false

instance : ToString PrimTy where
  toString
    | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
    | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
    | .f32 => "f32" | .f64 => "f64"
    | .bool => "bool"
    | .unit => "unit"

end PrimTy

/-- Alloy types -/
inductive Ty where
  /-- Primitive types -/
  | prim (p : PrimTy)
  /-- Pointer to a value of type t -/
  | ptr (t : Ty)
  /-- Raw pointer (void*) -/
  | rawPtr
  /-- Function pointer: (args) -> ret -/
  | funcPtr (args : Array Ty) (ret : Ty)
  /-- Struct type (product) with named fields -/
  | struct (fields : Array (String × Ty))
  /-- Array type with static size -/
  | array (elem : Ty) (size : Nat)
  /-- Tagged union (for ADTs) -/
  | tagged (tag : Ty) (variants : Array (Nat × Array Ty))
  /-- Closure type: function pointer + environment pointer -/
  | closure (args : Array Ty) (ret : Ty)
  deriving Repr, BEq, Inhabited

namespace Ty

/-- Common type aliases -/
def i64 : Ty := .prim .i64
def i32 : Ty := .prim .i32
def u64 : Ty := .prim .u64
def u32 : Ty := .prim .u32
def bool : Ty := .prim .bool
def unit : Ty := .prim .unit

/-- Size in bytes (for allocation) -/
partial def sizeBytes : Ty → Nat
  | .prim p => (p.bitWidth + 7) / 8
  | .ptr _ | .rawPtr => 8
  | .funcPtr _ _ => 8
  | .struct fields => fields.foldl (fun acc (_, t) => acc + t.sizeBytes) 0
  | .array elem size => elem.sizeBytes * size
  | .tagged tag variants =>
    let maxPayload := variants.foldl (fun acc (_, fields) =>
      max acc (fields.foldl (fun a t => a + t.sizeBytes) 0)) 0
    tag.sizeBytes + maxPayload
  | .closure _ _ => 16  -- fn ptr + env ptr

/-- Alignment in bytes -/
partial def alignment : Ty → Nat
  | .prim p => min 8 ((p.bitWidth + 7) / 8)
  | .ptr _ | .rawPtr | .funcPtr _ _ => 8
  | .struct fields => fields.foldl (fun acc (_, t) => max acc t.alignment) 1
  | .array elem _ => elem.alignment
  | .tagged tag variants =>
    let maxAlign := variants.foldl (fun acc (_, fields) =>
      max acc (fields.foldl (fun a t => max a t.alignment) 1)) 1
    max tag.alignment maxAlign
  | .closure _ _ => 8

partial def toStringAux : Ty → String
  | .prim p => ToString.toString p
  | .ptr t => s!"*{toStringAux t}"
  | .rawPtr => "rawptr"
  | .funcPtr args ret =>
    let argsStr := String.intercalate ", " (args.toList.map toStringAux)
    s!"fn({argsStr}) -> {toStringAux ret}"
  | .struct fields =>
    let fieldsStr := String.intercalate ", " (fields.toList.map fun (n, t) => s!"{n}: {toStringAux t}")
    s!"\{{fieldsStr}}"
  | .array elem size => s!"[{toStringAux elem}; {size}]"
  | .tagged tag variants =>
    let varStr := String.intercalate " | " (variants.toList.map fun (i, ts) =>
      s!"{i}({String.intercalate ", " (ts.toList.map toStringAux)})")
    s!"tagged<{toStringAux tag}>[{varStr}]"
  | .closure args ret =>
    let argsStr := String.intercalate ", " (args.toList.map toStringAux)
    s!"closure({argsStr}) -> {toStringAux ret}"

instance : ToString Ty where
  toString := toStringAux

end Ty

/-! ## Constants -/

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
  | null (ty : Ty)
  /-- String literal (index into string table) -/
  | string (idx : Nat) (len : Nat)
  /-- Undefined value (for uninitialized memory) -/
  | undef (ty : Ty)
  deriving Repr, BEq, Inhabited

namespace Const

def ty : Const → Ty
  | .int _ t => .prim t
  | .float _ t => .prim t
  | .bool _ => .prim .bool
  | .unit => .prim .unit
  | .null t => .ptr t
  | .string _ _ => .rawPtr
  | .undef t => t

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

/-! ## Operands -/

/-- An operand is either a local value or a constant -/
inductive Operand where
  | local (id : LocalId)
  | const (c : Const)
  | global (id : GlobalId)
  | func (id : FuncId)
  deriving Repr, BEq, Inhabited

namespace Operand

instance : ToString Operand where
  toString
    | .local id => ToString.toString id
    | .const c => ToString.toString c
    | .global id => ToString.toString id
    | .func id => ToString.toString id

end Operand

/-! ## Binary and Unary Operations -/

/-- Binary operations -/
inductive BinOp where
  -- Arithmetic
  | add | sub | mul | div | rem
  -- Bitwise
  | and | or | xor | shl | shr
  -- Comparison (returns bool)
  | eq | ne | lt | le | gt | ge
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

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
inductive UnOp where
  | neg   -- Arithmetic negation
  | not   -- Bitwise/logical not
  | trunc (to : PrimTy)   -- Truncate to smaller type
  | zext (to : PrimTy)    -- Zero-extend to larger type
  | sext (to : PrimTy)    -- Sign-extend to larger type
  | itof (to : PrimTy)    -- Int to float
  | ftoi (to : PrimTy)    -- Float to int
  | bitcast (to : Ty)     -- Reinterpret bits
  deriving Repr, BEq, Inhabited

namespace UnOp

instance : ToString UnOp where
  toString
    | .neg => "neg"
    | .not => "not"
    | .trunc t => s!"trunc.{t}"
    | .zext t => s!"zext.{t}"
    | .sext t => s!"sext.{t}"
    | .itof t => s!"itof.{t}"
    | .ftoi t => s!"ftoi.{t}"
    | .bitcast t => s!"bitcast.{t}"

end UnOp

end Soma.Alloy
