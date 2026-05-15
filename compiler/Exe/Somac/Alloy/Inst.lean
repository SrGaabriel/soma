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

  /-- Create a stack-allocated closure (monomorphic) -/
  | stackClosure : FuncRef → Operand → Inst n

  /-- Stack-allocated polymorphic closure counterpart to makeClosurePoly -/
  | stackClosurePoly : FuncRef → Array (Ty n) → Operand → Inst n

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

  /-- Produces a type-specialized deep copy of a value -/
  | clone : Operand → Ty n → UInt32 → Inst n

  /-- Stack-allocated counterpart to `clone` -/
  | stackClone : Operand → Ty n → Nat → Inst n

  /-- Panic with message -/
  | panic : Nat → Nat → Inst n

  /-- FFI intrinsic operation -/
  | callIntrinsic : IntrinsicOp → Array Operand → Ty n → Inst n

  /-- External function call -/
  | callExtern : String → Array Operand → Ty n → Inst n

  /-- Polymorphic external function call -/
  | callExternPoly : String → Array (Ty n) → Array Operand → Ty n → Inst n

/-- Monomorphic instruction -/
abbrev ClosedInst := Inst 0

namespace Inst

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
  | .stackClosure func envOp, _ => .stackClosure func envOp
  | .stackClosurePoly func tyArgs envOp, env =>
      .stackClosurePoly func (tyArgs.map (Somac.Alloy.instantiate · env)) envOp
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
  | .clone val ty label, env => .clone val (Somac.Alloy.instantiate ty env) label
  | .stackClone val ty slots, env => .stackClone val (Somac.Alloy.instantiate ty env) slots
  | .panic msgIdx line, _ => .panic msgIdx line
  | .callIntrinsic op args retTy, env => .callIntrinsic op args (Somac.Alloy.instantiate retTy env)
  | .callExtern name args retTy, env => .callExtern name args (Somac.Alloy.instantiate retTy env)
  | .callExternPoly name tyArgs args retTy, env =>
      .callExternPoly name (tyArgs.map (Somac.Alloy.instantiate · env)) args (Somac.Alloy.instantiate retTy env)

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
  | .stackClosure _ _ => none
  | .stackClosurePoly _ _ _ => none
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
  | .clone _ ty _ => some ty
  | .stackClone _ ty _ => some ty
  | .panic _ _ => none
  | .callIntrinsic op _ retTy => if op.hasResult then some retTy else none
  | .callExtern _ _ retTy => some retTy
  | .callExternPoly _ _ _ retTy => some retTy

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
  | .stackClosure funcRef env => s!"stackclosure {funcRef}, {env}"
  | .stackClosurePoly funcRef typeArgs env =>
      let ts := String.intercalate ", " (typeArgs.toList.map Ty.toString)
      s!"stackclosure.poly {funcRef}<{ts}>, {env}"
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
  | .clone val ty label => s!"clone {val} : {ty} &{label}"
  | .stackClone val ty slots => s!"stackclone {val} : {ty} @{slots}slots"
  | .panic msgIdx line => s!"panic #{msgIdx} @ line {line}"
  | .callIntrinsic op args _ =>
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call.intrinsic {op}({as})"
  | .callExtern name args _ =>
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call.extern {name}({as})"
  | .callExternPoly name typeArgs args _ =>
      let ts := String.intercalate ", " (typeArgs.toList.map Ty.toString)
      let as := String.intercalate ", " (args.toList.map ToString.toString)
      s!"call.extern.poly {name}<{ts}>({as})"

instance : ToString (Inst n) where
  toString := toStringAux

/-- Extract all operands referenced by an instruction -/
def operands : Inst n → Array (Operand)
  | .binOp _ l r _ => #[l, r]
  | .unOp _ o => #[o]
  | .copy o => #[o]
  | .load o _ => #[o]
  | .store v p => #[v, p]
  | .getFieldPtr o _ _ => #[o]
  | .getElemPtr o i _ => #[o, i]
  | .extractField o _ => #[o]
  | .insertField o _ v => #[o, v]
  | .extractElem o i => #[o, i]
  | .insertElem o i v => #[o, i, v]
  | .call _ args _ => args
  | .callPoly _ _ args _ => args
  | .callIndirect f args _ => #[f] ++ args
  | .callClosure f args _ => #[f] ++ args
  | .callExtern _ args _ => args
  | .callExternPoly _ _ args _ => args
  | .callIntrinsic _ args _ => args
  | .makeClosure _ env => #[env]
  | .makeClosurePoly _ _ env => #[env]
  | .makeClosureDyn f env _ => #[f, env]
  | .stackClosure _ env => #[env]
  | .stackClosurePoly _ _ env => #[env]
  | .taggedLit _ fields _ => fields
  | .reuseTaggedLit _ fields r _ => fields ++ #[r]
  | .structLit fields _ => fields
  | .arrayLit elems _ => elems
  | .getTag o => #[o]
  | .getPayload o _ _ _ => #[o]
  | .erase o _ => #[o]
  | .clone o _ _ => #[o]
  | .stackClone o _ _ => #[o]
  | .closureFunc o => #[o]
  | .closureEnv o => #[o]
  | .phi incoming _ => incoming.map Prod.fst
  | .select c t e => #[c, t, e]
  | .memcpy d s sz => #[d, s, sz]
  | .memset d v sz => #[d, v, sz]
  | .lazySup _ o _ => #[o]
  | .supProj0 o _ => #[o]
  | .supProj1 o _ => #[o]
  | .malloc sz => #[sz]
  | .free p => #[p]
  | .alloca _ => #[]
  | .panic _ _ => #[]

/-- Extract all local variable references from an instruction's operands -/
def localUses (inst : Inst n) : Array LocalId :=
  inst.operands.filterMap fun
    | .local id => some id
    | _ => none

/-- Apply a function to every operand in an instruction, producing a new instruction -/
def mapOperands (inst : Inst 0) (f : Operand → Operand) : Inst 0 :=
  match inst with
  | .binOp op l r ty => .binOp op (f l) (f r) ty
  | .unOp op o => .unOp op (f o)
  | .copy o => .copy (f o)
  | .alloca ty => .alloca ty
  | .malloc sz => .malloc (f sz)
  | .free p => .free (f p)
  | .load o ty => .load (f o) ty
  | .store v p => .store (f v) (f p)
  | .getFieldPtr o idx ty => .getFieldPtr (f o) idx ty
  | .getElemPtr o i ty => .getElemPtr (f o) (f i) ty
  | .extractField o idx => .extractField (f o) idx
  | .insertField o idx v => .insertField (f o) idx (f v)
  | .extractElem o idx => .extractElem (f o) (f idx)
  | .insertElem o idx v => .insertElem (f o) (f idx) (f v)
  | .structLit fields ty => .structLit (fields.map f) ty
  | .arrayLit elems ty => .arrayLit (elems.map f) ty
  | .getTag o => .getTag (f o)
  | .getPayload o vi fi ty => .getPayload (f o) vi fi ty
  | .taggedLit tag fields ty => .taggedLit tag (fields.map f) ty
  | .reuseTaggedLit tag fields r ty => .reuseTaggedLit tag (fields.map f) (f r) ty
  | .call fid args ty => .call fid (args.map f) ty
  | .callPoly fid tys args ty => .callPoly fid tys (args.map f) ty
  | .callIndirect fn args ty => .callIndirect (f fn) (args.map f) ty
  | .callClosure clo args ty => .callClosure (f clo) (args.map f) ty
  | .callExtern name args ty => .callExtern name (args.map f) ty
  | .callExternPoly name tys args ty => .callExternPoly name tys (args.map f) ty
  | .callIntrinsic op args ty => .callIntrinsic op (args.map f) ty
  | .makeClosure ref env => .makeClosure ref (f env)
  | .makeClosurePoly ref tys env => .makeClosurePoly ref tys (f env)
  | .makeClosureDyn fn env ty => .makeClosureDyn (f fn) (f env) ty
  | .stackClosure ref env => .stackClosure ref (f env)
  | .stackClosurePoly ref tys env => .stackClosurePoly ref tys (f env)
  | .closureFunc o => .closureFunc (f o)
  | .closureEnv o => .closureEnv (f o)
  | .phi incoming ty => .phi (incoming.map fun (op, bid) => (f op, bid)) ty
  | .select c t e => .select (f c) (f t) (f e)
  | .memcpy d s sz => .memcpy (f d) (f s) (f sz)
  | .memset d v sz => .memset (f d) (f v) (f sz)
  | .lazySup lbl o ty => .lazySup lbl (f o) ty
  | .supProj0 o ty => .supProj0 (f o) ty
  | .supProj1 o ty => .supProj1 (f o) ty
  | .erase o ty => .erase (f o) ty
  | .clone o ty label => .clone (f o) ty label
  | .stackClone o ty slots => .stackClone (f o) ty slots
  | .panic idx line => .panic idx line

end Inst

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

/-- Extract all local variable references from a terminator -/
def localUses : Terminator → Array LocalId
  | .ret val => match val with
    | .local id => #[id]
    | _ => #[]
  | .branch cond _ _ => match cond with
    | .local id => #[id]
    | _ => #[]
  | .switch val _ _ => match val with
    | .local id => #[id]
    | _ => #[]
  | .jump _ | .retUnit | .unreachable => #[]

/-- Apply a function to every operand in a terminator -/
def mapOperands : Terminator → (Operand → Operand) → Terminator
  | .ret val, f => .ret (f val)
  | .branch cond t e, f => .branch (f cond) t e
  | .switch val cases d, f => .switch (f val) cases d
  | .jump t, _ => .jump t
  | .retUnit, _ => .retUnit
  | .unreachable, _ => .unreachable

end Terminator

end Somac.Alloy
