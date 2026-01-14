/-
  Alloy IR Instructions

  Instructions are the atomic operations in Alloy. Each instruction produces
  at most one value (SSA form). Instructions are organized into categories:

  1. Value operations: arithmetic, logic, conversions
  2. Memory operations: alloc, load, store, memcpy
  3. Aggregate operations: struct/array construction and access
  4. Control flow: handled by terminators (separate type)
  5. Function operations: call, closure creation
-/

import Somac.Alloy.Types

namespace Somac.Alloy

/-- An instruction that produces a value -/
inductive Inst where
  /-- Binary operation: result = op lhs rhs -/
  | binOp (op : BinOp) (lhs : Operand) (rhs : Operand) (ty : Ty)

  /-- Unary operation: result = op operand -/
  | unOp (op : UnOp) (operand : Operand)

  /-- Copy an operand (identity, useful for phi nodes and moves) -/
  | copy (src : Operand)

  /-- Stack allocation: result = alloca ty
      Allocates sizeof(ty) bytes on the stack, returns pointer -/
  | alloca (ty : Ty)

  /-- Heap allocation: result = malloc size
      Allocates size bytes on the heap, returns raw pointer -/
  | malloc (size : Operand)

  /-- Free heap memory: free ptr -/
  | free (ptr : Operand)

  /-- Load from pointer: result = *ptr -/
  | load (ptr : Operand) (ty : Ty)

  /-- Store to pointer: *ptr = val (no result) -/
  | store (ptr : Operand) (val : Operand)

  /-- Get pointer to struct field: result = &base->field -/
  | getFieldPtr (base : Operand) (fieldIdx : Nat) (structTy : Ty)

  /-- Get pointer to array element: result = &base[idx] -/
  | getElemPtr (base : Operand) (idx : Operand) (elemTy : Ty)

  /-- Extract value from struct: result = val.field -/
  | extractField (val : Operand) (fieldIdx : Nat)

  /-- Insert value into struct: result = { val | field = newVal } -/
  | insertField (val : Operand) (fieldIdx : Nat) (newVal : Operand)

  /-- Extract element from array: result = val[idx] -/
  | extractElem (val : Operand) (idx : Operand)

  /-- Insert element into array: result = val[idx := newVal] -/
  | insertElem (val : Operand) (idx : Operand) (newVal : Operand)

  /-- Construct a struct from fields: result = { f0, f1, ... } -/
  | structLit (fields : Array Operand) (ty : Ty)

  /-- Construct an array from elements: result = [e0, e1, ...] -/
  | arrayLit (elems : Array Operand) (elemTy : Ty)

  /-- Get tag from tagged union: result = val.tag -/
  | getTag (val : Operand)

  /-- Get payload from tagged union (unsafe, must check tag first) -/
  | getPayload (val : Operand) (variantIdx : Nat) (fieldIdx : Nat)

  /-- Construct tagged union: result = Tag(payload...) -/
  | taggedLit (tag : Nat) (payload : Array Operand) (ty : Ty)

  /-- Direct function call: result = func(args...) -/
  | call (func : FuncId) (args : Array Operand) (retTy : Ty)

  /-- Call a polymorphic function with type arguments: result = func<T1, T2, ...>(args...) -/
  | callPoly (func : FuncId) (typeArgs : Array Ty) (args : Array Operand) (retTy : Ty)

  /-- Indirect call through function pointer: result = ptr(args...) -/
  | callIndirect (ptr : Operand) (args : Array Operand) (retTy : Ty)

  /-- Closure call: result = closure(args...)
      Unpacks closure into (fn, env), calls fn(env, args...) -/
  | callClosure (closure : Operand) (args : Array Operand) (retTy : Ty)

  /-- Create closure from polymorphic function: result = { fn<T1, T2, ...>, env } -/
  | makeClosurePoly (func : FuncId) (typeArgs : Array Ty) (env : Operand)

  /-- Create closure: result = { fn, env }
      Captures environment pointer with function pointer -/
  | makeClosure (func : FuncId) (env : Operand)

  /-- Get function pointer from closure -/
  | closureFunc (closure : Operand)

  /-- Get environment pointer from closure -/
  | closureEnv (closure : Operand)

  /-- Phi node: result = phi [val1, block1], [val2, block2], ...
      Value depends on which predecessor block we came from -/
  | phi (incoming : Array (Operand × BlockId)) (ty : Ty)

  /-- Select: result = cond ? thenVal : elseVal -/
  | select (cond : Operand) (thenVal : Operand) (elseVal : Operand)

  /-- Memory copy: memcpy dst src size -/
  | memcpy (dst : Operand) (src : Operand) (size : Operand)

  /-- Memory set: memset dst val size -/
  | memset (dst : Operand) (val : Operand) (size : Operand)

  /-- Clone a value (deep copy for runtime) -/
  | clone (src : Operand) (ty : Ty)

  /-- Erase/free a value (recursive deallocation) -/
  | erase (val : Operand) (ty : Ty)

  /-- Panic with message (aborts execution) -/
  | panic (msgIdx : Nat) (line : Nat)

  /-- Runtime intrinsic call -/
  | intrinsic (name : String) (args : Array Operand) (retTy : Ty)

  deriving Repr, Inhabited

namespace Inst

/-- Does this instruction have a result value? -/
def hasResult : Inst → Bool
  | .store _ _ => false
  | .free _ => false
  | .memcpy _ _ _ => false
  | .memset _ _ _ => false
  | .erase _ _ => false
  | .panic _ _ => false
  | _ => true

/-- Get the result type of an instruction (if it has one) -/
def resultTy : Inst → Option Ty
  | .binOp op _ _ ty =>
    if op.isComparison then some Ty.bool else some ty
  | .unOp op _ =>
    match op with
    | .neg | .not => none  -- Same as input type
    | .trunc t | .zext t | .sext t | .itof t | .ftoi t => some (.prim t)
    | .bitcast t => some t
  | .copy _ => none  -- Same as input
  | .alloca ty => some (.ptr ty)
  | .malloc _ => some .rawPtr
  | .free _ => none
  | .load _ ty => some ty
  | .store _ _ => none
  | .getFieldPtr _ fieldIdx structTy =>
    match structTy with
    | .struct fields => fields[fieldIdx]?.map (fun (_, t) => .ptr t)
    | _ => none
  | .getElemPtr _ _ elemTy => some (.ptr elemTy)
  | .extractField _ _ => none  -- Depends on struct type
  | .insertField _ _ _ => none  -- Same as input struct
  | .extractElem _ _ => none  -- Depends on array type
  | .insertElem _ _ _ => none  -- Same as input array
  | .structLit _ ty => some ty
  | .arrayLit elems elemTy => some (.array elemTy elems.size)
  | .getTag _ => some (.prim .u32)
  | .getPayload _ _ _ => none  -- Depends on variant
  | .taggedLit _ _ ty => some ty
  | .call _ _ retTy => some retTy
  | .callPoly _ _ _ retTy => some retTy
  | .callIndirect _ _ retTy => some retTy
  | .callClosure _ _ retTy => some retTy
  | .makeClosurePoly _ _ _ => none -- Closure type depends on function
  | .makeClosure _ _ => none  -- Closure type depends on function
  | .closureFunc _ => none  -- Function pointer type
  | .closureEnv _ => some .rawPtr
  | .phi _ ty => some ty
  | .select _ _ _ => none  -- Same as branch types
  | .memcpy _ _ _ => none
  | .memset _ _ _ => none
  | .clone _ ty => some ty
  | .erase _ _ => none
  | .panic _ _ => none
  | .intrinsic _ _ retTy => some retTy

instance : ToString Inst where
  toString inst :=
    match inst with
    | .binOp op lhs rhs _ => s!"{op} {lhs}, {rhs}"
    | .unOp op operand => s!"{op} {operand}"
    | .copy src => s!"copy {src}"
    | .alloca ty => s!"alloca {ty}"
    | .malloc size => s!"malloc {size}"
    | .free ptr => s!"free {ptr}"
    | .load ptr ty => s!"load {ty} {ptr}"
    | .store ptr val => s!"store {ptr}, {val}"
    | .getFieldPtr base idx _ => s!"getfieldptr {base}, {idx}"
    | .getElemPtr base idx _ => s!"getelemptr {base}, {idx}"
    | .extractField val idx => s!"extractfield {val}, {idx}"
    | .insertField val idx newVal => s!"insertfield {val}, {idx}, {newVal}"
    | .extractElem val idx => s!"extractelem {val}, {idx}"
    | .insertElem val idx newVal => s!"insertelem {val}, {idx}, {newVal}"
    | .structLit fields _ =>
      let fs := String.intercalate ", " (fields.toList.map ToString.toString)
      s!"struct \{{fs}}"
    | .arrayLit elems _ =>
      let es := String.intercalate ", " (elems.toList.map ToString.toString)
      s!"array [{es}]"
    | .getTag val => s!"gettag {val}"
    | .getPayload val variant field => s!"getpayload {val}, {variant}, {field}"
    | .taggedLit tag payload _ =>
      let ps := String.intercalate ", " (payload.toList.map ToString.toString)
      s!"tagged {tag}({ps})"
    | .call func args _ =>
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call {func}({as})"
    | .callPoly func typeArgs args _ =>
      let ts := String.intercalate ", " (typeArgs.toList.map ToString.toString)
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call.poly {func}<{ts}>({as})"
    | .callIndirect ptr args _ =>
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call.indirect {ptr}({as})"
    | .callClosure closure args _ =>
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call.closure {closure}({as})"
    | .makeClosurePoly func typeArgs env =>
      let ts := String.intercalate ", " (typeArgs.toList.map ToString.toString)
      s!"makeclosure.poly {func}<{ts}>, {env}"
    | .makeClosure func env => s!"makeclosure {func}, {env}"
    | .closureFunc closure => s!"closure.func {closure}"
    | .closureEnv closure => s!"closure.env {closure}"
    | .phi incoming _ =>
      let is := String.intercalate ", " (incoming.toList.map fun (v, b) => s!"[{v}, {b}]")
      s!"phi {is}"
    | .select cond t e => s!"select {cond}, {t}, {e}"
    | .memcpy dst src size => s!"memcpy {dst}, {src}, {size}"
    | .memset dst val size => s!"memset {dst}, {val}, {size}"
    | .clone src ty => s!"clone {src} : {ty}"
    | .erase val ty => s!"erase {val} : {ty}"
    | .panic msgIdx line => s!"panic #{msgIdx} @ line {line}"
    | .intrinsic name args _ =>
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"intrinsic {name}({as})"

end Inst

/-! ## Block Terminators -/

/-- A terminator ends a basic block with control flow -/
inductive Terminator where
  /-- Unconditional jump to a block -/
  | jump (target : BlockId)

  /-- Conditional branch: br cond ? then : else -/
  | branch (cond : Operand) (thenBlock : BlockId) (elseBlock : BlockId)

  /-- Multi-way branch on integer value (switch) -/
  | switch (val : Operand) (cases : Array (Int × BlockId)) (default : BlockId)

  /-- Return from function with value -/
  | ret (val : Operand)

  /-- Return unit (void) -/
  | retUnit

  /-- Unreachable (undefined behavior if reached) -/
  | unreachable

  deriving Repr, Inhabited

namespace Terminator

/-- Get all successor blocks -/
def successors : Terminator → Array BlockId
  | .jump target => #[target]
  | .branch _ thenB elseB => #[thenB, elseB]
  | .switch _ cases default => cases.map (·.2) |>.push default
  | .ret _ | .retUnit | .unreachable => #[]

instance : ToString Terminator where
  toString
    | .jump target => s!"jump {target}"
    | .branch cond thenB elseB => s!"br {cond}, {thenB}, {elseB}"
    | .switch val cases default =>
      let cs := String.intercalate ", " (cases.toList.map fun (v, b) => s!"{v} => {b}")
      s!"switch {val} [{cs}] default {default}"
    | .ret val => s!"ret {val}"
    | .retUnit => "ret"
    | .unreachable => "unreachable"

end Terminator

end Somac.Alloy
