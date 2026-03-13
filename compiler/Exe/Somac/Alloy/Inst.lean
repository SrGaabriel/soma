import Somac.Alloy.Types
import Kenosis

namespace Somac.Alloy

/-- An instruction that produces a value -/
inductive Inst : Nat → Type where
  /-- Binary operation: result = op lhs rhs -/
  | binOp : BinOp → Operand → Operand → Ty n → Inst n

  /-- Unary operation: result = op operand -/
  | unOp : UnOp n → Operand → Inst n

  /-- Copy an operand -/
  | copy : Operand → Inst n

  /-- Stack allocation: result = alloca ty -/
  | alloca : Ty n → Inst n

  /-- Heap allocation: result = malloc size -/
  | malloc : Operand → Inst n

  /-- Free heap memory -/
  | free : Operand → Inst n

  /-- Load from pointer: result = *ptr -/
  | load : Operand → Ty n → Inst n

  /-- Store to pointer: *ptr = val -/
  | store : Operand → Operand → Inst n

  /-- Get pointer to struct field: result = &base->field -/
  | getFieldPtr : Operand → Nat → Ty n → Inst n

  /-- Get pointer to array element: result = &base[idx] -/
  | getElemPtr : Operand → Operand → Ty n → Inst n

  /-- Extract value from struct -/
  | extractField : Operand → Nat → Inst n

  /-- Insert value into struct -/
  | insertField : Operand → Nat → Operand → Inst n

  /-- Extract element from array -/
  | extractElem : Operand → Operand → Inst n

  /-- Insert element into array -/
  | insertElem : Operand → Operand → Operand → Inst n

  /-- Construct a struct from fields -/
  | structLit : Array Operand → Ty n → Inst n

  /-- Construct an array from elements -/
  | arrayLit : Array Operand → Ty n → Inst n

  /-- Get tag from tagged union -/
  | getTag : Operand → Inst n

  /-- Get payload from tagged union -/
  | getPayload : Operand → Nat → Nat → Ty n → Inst n

  /-- Construct tagged union -/
  | taggedLit : Nat → Array Operand → Ty n → Inst n

  /-- Construct tagged union by reusing an existing payload allocation in-place -/
  | reuseTaggedLit : Nat → Array Operand → Operand → Ty n → Inst n

  /-- Direct function call (monomorphic) -/
  | call : FuncId → Array Operand → Ty n → Inst n

  /-- Polymorphic function call with type arguments -/
  | callPoly : FuncId → Array (Ty n) → Array Operand → Ty n → Inst n

  /-- Indirect call through function pointer -/
  | callIndirect : Operand → Array Operand → Ty n → Inst n

  /-- Closure call -/
  | callClosure : Operand → Array Operand → Ty n → Inst n

  /-- Create closure from polymorphic function -/
  | makeClosurePoly : FuncRef → Array (Ty n) → Operand → Inst n

  /-- Create closure (monomorphic) -/
  | makeClosure : FuncRef → Operand → Inst n

  /-- Create closure from a dynamically-resolved function (itself a closure) -/
  | makeClosureDyn : Operand → Operand → Ty n → Inst n

  /-- Get function pointer from closure -/
  | closureFunc : Operand → Inst n

  /-- Get environment pointer from closure -/
  | closureEnv : Operand → Inst n

  /-- Phi node -/
  | phi : Array (Operand × BlockId) → Ty n → Inst n

  /-- Select: cond ? thenVal : elseVal -/
  | select : Operand → Operand → Operand → Inst n

  /-- Memory copy -/
  | memcpy : Operand → Operand → Operand → Inst n

  /-- Memory set -/
  | memset : Operand → Operand → Operand → Inst n

  /-- Create a SUP node for lazy duplication -/
  | lazySup : UInt32 → Operand → Ty n → Inst n

  /-- Project the first copy from a SUP node -/
  | supProj0 : Operand → Ty n → Inst n

  /-- Project the second copy from a SUP node -/
  | supProj1 : Operand → Ty n → Inst n

  /-- Erase a value -/
  | erase : Operand → Ty n → Inst n

  /-- Panic with message -/
  | panic : Nat → Nat → Inst n

  /-- FFI intrinsic operation -/
  | callIntrinsic : IntrinsicOp → Array Operand → Ty n → Inst n

  /-- External function call -/
  | callExtern : String → Array Operand → Ty n → Inst n

/-- Monomorphic instruction -/
abbrev ClosedInst := Inst 0

namespace Inst

/-- Does this instruction have a result value? -/
def hasResult : Inst n → Bool
  | .store _ _ => false
  | .free _ => false
  | .memcpy _ _ _ => false
  | .memset _ _ _ => false
  | .erase _ _ => false
  | .panic _ _ => false
  | .callIntrinsic op _ _ => op.hasResult
  | _ => true

/-- Instantiate all types in an instruction -/
def instantiate : Inst n → TyEnv n → ClosedInst
  | .binOp op lhs rhs ty, env => .binOp op lhs rhs (Somac.Alloy.instantiate ty env)
  | .unOp op operand, env => .unOp (op.instantiate env) operand
  | .copy src, _ => .copy src
  | .alloca ty, env => .alloca (Somac.Alloy.instantiate ty env)
  | .malloc size, _ => .malloc size
  | .free ptr, _ => .free ptr
  | .load ptr ty, env => .load ptr (Somac.Alloy.instantiate ty env)
  | .store ptr val, _ => .store ptr val
  | .getFieldPtr base idx structTy, env => .getFieldPtr base idx (Somac.Alloy.instantiate structTy env)
  | .getElemPtr base idx elemTy, env => .getElemPtr base idx (Somac.Alloy.instantiate elemTy env)
  | .extractField val idx, _ => .extractField val idx
  | .insertField val idx newVal, _ => .insertField val idx newVal
  | .extractElem val idx, _ => .extractElem val idx
  | .insertElem val idx newVal, _ => .insertElem val idx newVal
  | .structLit fields ty, env => .structLit fields (Somac.Alloy.instantiate ty env)
  | .arrayLit elems ty, env => .arrayLit elems (Somac.Alloy.instantiate ty env)
  | .getTag val, _ => .getTag val
  | .getPayload val variant field ty, env => .getPayload val variant field (Somac.Alloy.instantiate ty env)
  | .taggedLit tag payload ty, env => .taggedLit tag payload (Somac.Alloy.instantiate ty env)
  | .reuseTaggedLit tag payload reuse ty, env =>
      .reuseTaggedLit tag payload reuse (Somac.Alloy.instantiate ty env)
  | .call func args retTy, env => .call func args (Somac.Alloy.instantiate retTy env)
  | .callPoly func tyArgs args retTy, env =>
      .callPoly func (tyArgs.map (Somac.Alloy.instantiate · env)) args (Somac.Alloy.instantiate retTy env)
  | .callIndirect ptr args retTy, env => .callIndirect ptr args (Somac.Alloy.instantiate retTy env)
  | .callClosure closure args retTy, env => .callClosure closure args (Somac.Alloy.instantiate retTy env)
  | .makeClosurePoly func tyArgs envOp, env =>
      .makeClosurePoly func (tyArgs.map (Somac.Alloy.instantiate · env)) envOp
  | .makeClosure func envOp, _ => .makeClosure func envOp
  | .makeClosureDyn fnClosure envOp ty, env => .makeClosureDyn fnClosure envOp (Somac.Alloy.instantiate ty env)
  | .closureFunc closure, _ => .closureFunc closure
  | .closureEnv closure, _ => .closureEnv closure
  | .phi incoming ty, env => .phi incoming (Somac.Alloy.instantiate ty env)
  | .select cond t e, _ => .select cond t e
  | .memcpy dst src size, _ => .memcpy dst src size
  | .memset dst val size, _ => .memset dst val size
  | .lazySup label src ty, env => .lazySup label src (Somac.Alloy.instantiate ty env)
  | .supProj0 src ty, env => .supProj0 src (Somac.Alloy.instantiate ty env)
  | .supProj1 src ty, env => .supProj1 src (Somac.Alloy.instantiate ty env)
  | .erase val ty, env => .erase val (Somac.Alloy.instantiate ty env)
  | .panic msgIdx line, _ => .panic msgIdx line
  | .callIntrinsic op args retTy, env => .callIntrinsic op args (Somac.Alloy.instantiate retTy env)
  | .callExtern name args retTy, env => .callExtern name args (Somac.Alloy.instantiate retTy env)

/-- Get the result type of a closed instruction -/
def resultTy : ClosedInst → Option ClosedTy
  | .binOp op _ _ ty => if op.isComparison then some Ty.bool else some ty
  | .unOp op _ =>
      match op with
      | .neg | .not => none
      | .trunc t | .zext t | .sext t | .itof t | .ftoi t | .ptrtoint t => some (.prim t)
      | .bitcast t => some t
      | .inttoptr => some .rawPtr
  | .copy _ => none
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
  | .extractField _ _ => none
  | .insertField _ _ _ => none
  | .extractElem _ _ => none
  | .insertElem _ _ _ => none
  | .structLit _ ty => some ty
  | .arrayLit elems elemTy => some (.array elemTy elems.size)
  | .getTag _ => some (.prim .u32)
  | .getPayload _ _ _ ty => some ty
  | .taggedLit _ _ ty => some ty
  | .reuseTaggedLit _ _ _ ty => some ty
  | .call _ _ retTy => some retTy
  | .callPoly _ _ _ retTy => some retTy
  | .callIndirect _ _ retTy => some retTy
  | .callClosure _ _ retTy => some retTy
  | .makeClosurePoly _ _ _ => none
  | .makeClosure _ _ => none
  | .makeClosureDyn _ _ ty => some ty
  | .closureFunc _ => none
  | .closureEnv _ => some .rawPtr
  | .phi _ ty => some ty
  | .select _ _ _ => none
  | .memcpy _ _ _ => none
  | .memset _ _ _ => none
  | .lazySup _ _ ty => some ty
  | .supProj0 _ ty => some ty
  | .supProj1 _ ty => some ty
  | .erase _ _ => none
  | .panic _ _ => none
  | .callIntrinsic op _ retTy => if op.hasResult then some retTy else none
  | .callExtern _ _ retTy => some retTy

private def toStringAux : Inst n → String
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
  | .getPayload val variant field ty => s!"getpayload {val}, {variant}, {field} : {ty}"
  | .taggedLit tag payload _ =>
      let ps := String.intercalate ", " (payload.toList.map ToString.toString)
      s!"tagged {tag}({ps})"
  | .reuseTaggedLit tag payload reuse _ =>
      let ps := String.intercalate ", " (payload.toList.map ToString.toString)
      s!"reuse_tagged {tag}({ps}) reusing {reuse}"
  | .call func args _ =>
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call {func}({as})"
  | .callPoly func typeArgs args _ =>
      let ts := String.intercalate ", " (typeArgs.toList.map Ty.toString)
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call.poly {func}<{ts}>({as})"
  | .callIndirect ptr args _ =>
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call.indirect {ptr}({as})"
  | .callClosure closure args _ =>
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call.closure {closure}({as})"
  | .makeClosurePoly funcRef typeArgs env =>
      let ts := String.intercalate ", " (typeArgs.toList.map Ty.toString)
      s!"makeclosure.poly {funcRef}<{ts}>, {env}"
  | .makeClosure funcRef env => s!"makeclosure {funcRef}, {env}"
  | .makeClosureDyn fnClosure env ty => s!"makeclosure.dyn {fnClosure}, {env} : {ty}"
  | .closureFunc closure => s!"closure.func {closure}"
  | .closureEnv closure => s!"closure.env {closure}"
  | .phi incoming _ =>
      let is := String.intercalate ", " (incoming.toList.map fun (v, b) => s!"[{v}, {b}]")
      s!"phi {is}"
  | .select cond t e => s!"select {cond}, {t}, {e}"
  | .memcpy dst src size => s!"memcpy {dst}, {src}, {size}"
  | .memset dst val size => s!"memset {dst}, {val}, {size}"
  | .lazySup label src ty => s!"lazy_sup &{label} {src} : {ty}"
  | .supProj0 src ty => s!"sup_proj0 {src} : {ty}"
  | .supProj1 src ty => s!"sup_proj1 {src} : {ty}"
  | .erase val ty => s!"erase {val} : {ty}"
  | .panic msgIdx line => s!"panic #{msgIdx} @ line {line}"
  | .callIntrinsic op args _ =>
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call.intrinsic {op}({as})"
  | .callExtern name args _ =>
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call.extern {name}({as})"

instance : ToString (Inst n) where
  toString := toStringAux

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

  deriving Repr, Inhabited, Serialize, Deserialize

namespace Terminator

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
