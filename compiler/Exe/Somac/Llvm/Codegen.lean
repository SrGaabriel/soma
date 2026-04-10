import Somac.Alloy.Func
import Somac.Alloy.Monomorphize
import Somac.Llvm.Builder
import Soma.Driver.Target
import Std.Data.HashMap

namespace Somac.Llvm.Codegen

open Somac.Alloy
open Somac.Llvm
open Somac.Llvm.Builder
open Soma.Driver

/-- Convert Alloy primitive type to LLVM type -/
def convertPrimTy : PrimTy → LLVMType
  | .i8 => .i8
  | .i16 => .i16
  | .i32 => .i32
  | .i64 => .i64
  | .u8 => .i8
  | .u16 => .i16
  | .u32 => .i32
  | .u64 => .i64
  | .f32 => .float
  | .f64 => .double
  | .bool => .i1
  | .unit => .i8 -- here unit is i8 so it can be used as a value but wherever it's important it's void

/-- Check if a primitive type is a floating point type -/
def primTyIsFloat : PrimTy → Bool
  | .f32 | .f64 => true
  | _ => false

/-- Convert Alloy closed type to LLVM type -/
partial def convertTy : ClosedTy → LLVMType
  | .prim p => convertPrimTy p
  | .ptr _ => .ptr
  | .rawPtr => .ptr
  | .funcPtr args ret =>
    .func (convertTy ret) (args.map convertTy) false
  | .struct fields =>
    .struct false (fields.map fun (_, t) => convertTy t)
  | .array elem size =>
    .array size (convertTy elem)
  | .tagged _ _ =>
    .struct false #[.i32, .ptr]
  | .closure _ _ =>
    .ptr
  | .var i => nomatch i -- impossible

/-- Check if an Alloy type is unit -/
def isUnitTy : ClosedTy → Bool
  | .prim .unit => true
  | _ => false

/-- Convert Alloy type to LLVM type for function return types -/
partial def convertRetTy : ClosedTy → LLVMType
  | .prim .unit => .void
  | other => convertTy other

/-- Runtime closure object pointer type -/
def closureTy : LLVMType := .ptr

/-- Headerless closure struct -/
def closureHeaderTy : LLVMType := .struct false #[.i8, .array 7 .i8, .ptr]

/-- NODE_CLOSURE sentinel -/
def nodeClosureTag : Int := 1

/-- The tagged union struct type -/
def taggedTy : LLVMType := .struct false #[.i32, .ptr]

/-- Packed layout for a variant's payload: fields sorted by alignment (desc) -/
structure PackedLayout where
  /-- LLVM struct type with fields in physical (sorted) order -/
  llvmTy : LLVMType
  /-- Total byte size including alignment padding -/
  byteSize : Nat
  /-- Maps physical struct index → logical field index -/
  physToLog : Array Nat
  /-- Maps logical field index → physical struct index -/
  logToPhys : Array Nat

/-- Invert a permutation: if perm[physIdx] = logIdx, result[logIdx] = physIdx -/
def invertPerm (perm : Array Nat) : Array Nat :=
  let init := (List.replicate perm.size 0).toArray
  perm.foldl (fun (acc, phys) logIdx =>
    (acc.set! logIdx phys, phys + 1))
    (init, 0) |>.1

/-- Compute optimal packed layout for a variant's payload fields -/
partial def computePackedLayout (fields : Array ClosedTy) (ptrBytes : Nat) : PackedLayout :=
  if fields.isEmpty then
    { llvmTy := .struct false #[], byteSize := 0, physToLog := #[], logToPhys := #[] }
  else if fields.size == 1 then
    { llvmTy := .struct false #[convertTy fields[0]!]
      byteSize := fields[0]!.sizeBytes ptrBytes
      physToLog := #[0]
      logToPhys := #[0] }
  else
    let indexed := fields.mapIdx fun i f => (i, f)
    let sorted := indexed.qsort fun (_, a) (_, b) =>
      if a.alignment ptrBytes != b.alignment ptrBytes then a.alignment ptrBytes > b.alignment ptrBytes
      else a.sizeBytes ptrBytes > b.sizeBytes ptrBytes
    let physToLog := sorted.map fun (i, _) => i
    let logToPhys := invertPerm physToLog
    let physFields := sorted.map fun (_, t) => convertTy t
    let rawSize := sorted.foldl (fun acc (_, t) =>
      let align := max 1 (t.alignment ptrBytes)
      ((acc + align - 1) / align) * align + t.sizeBytes ptrBytes) 0
    let maxAlign := fields.foldl (fun acc t => max acc (t.alignment ptrBytes)) 1
    let byteSize := ((rawSize + maxAlign - 1) / maxAlign) * maxAlign
    { llvmTy := .struct false physFields, byteSize, physToLog, logToPhys }

/-- Maximum packed payload size across all variants of a tagged union -/
partial def maxPackedPayloadSize (variants : Array (Nat × Array ClosedTy)) (ptrBytes : Nat) : Nat :=
  variants.foldl (fun acc (_, fields) => max acc (computePackedLayout fields ptrBytes).byteSize) 0

/-- Natural alignment for a type -/
def naturalAlign (ty : LLVMType) (ptrBytes : Nat) : Option Nat :=
  let a := ty.alignment ptrBytes
  if a > 0 then some a else none

/-- Get the type of an Alloy operand -/
def getOperandTy (op : Operand) (localTypes : Std.HashMap Nat ClosedTy) : ClosedTy :=
  match op with
  | .local id => localTypes.get? id.id |>.getD (.prim .i64)
  | .const c => c.ty
  | .global _ => .rawPtr
  | .func _ => .rawPtr

/-- Get field type from a struct type -/
def getStructFieldTy (structTy : ClosedTy) (fieldIdx : Nat) : ClosedTy :=
  match structTy with
  | .struct fields =>
    if h : fieldIdx < fields.size then fields[fieldIdx].2
    else .prim .i64
  | _ => .prim .i64

/-- Get element type from an array type -/
def getArrayElemTy : ClosedTy → ClosedTy
  | .array elem _ => elem
  | _ => .prim .i64

/-- Check whether a closed type is the runtime String object type -/
def isStringObjTy (ty : ClosedTy) : Bool :=
  ty == (.struct #[("data", .rawPtr), ("len", .prim .i64)] : ClosedTy)

/-- Check whether a closed type is the runtime List object type -/
def isListObjTy (ty : ClosedTy) : Bool := ty.isSomaList

/-- Get payload field types from a tagged union -/
def getTaggedPayloadTy (taggedTy : ClosedTy) (variantIdx : Nat) (fieldIdx : Nat) : ClosedTy :=
  match taggedTy with
  | .tagged _ variants =>
    if h : variantIdx < variants.size then
      let (_, fields) := variants[variantIdx]
      if h2 : fieldIdx < fields.size then fields[fieldIdx]
      else .prim .i64
    else .prim .i64
  | _ => .prim .i64

/-- State for code generation -/
structure CodegenState where
  /-- Module builder state -/
  moduleState : ModuleBuilderState
  /-- Alloy FuncId to LLVM function name mapping -/
  funcNames : Std.HashMap Nat String := {}
  /-- Alloy FuncId to function signature mapping -/
  funcSigs : Std.HashMap Nat ClosedSignature := {}
  /-- Alloy LocalId to LLVM LocalRef mapping (per function) -/
  localMap : Std.HashMap Nat LocalRef := {}
  /-- Alloy LocalId to Alloy Type mapping (per function) -/
  localTypes : Std.HashMap Nat ClosedTy := {}
  /-- Alloy BlockId to LLVM Label mapping (per function) -/
  blockMap : Std.HashMap Nat Label := {}
  /-- Function builder state -/
  funcState : FuncBuilderState := {}
  /-- Current function being lowered -/
  currentFunc : Option ClosedFunc := none
  /-- Set of extern function names that have been declared -/
  declaredExterns : Std.HashSet String := {}
  /-- Cache of generated trampoline functions, keyed by signature string -/
  trampolineCache : Std.HashMap String String := {}
  /-- Blocks that were terminated early due to noreturn instructions -/
  deadBlocks : Std.HashSet Nat := {}
  /-- Set during instruction lowering when a noreturn call is emitted -/
  noreturnEmitted : Bool := false
  /-- Tracks Alloy locals that hold string constants (localId → string table index) -/
  stringConstLocals : Std.HashMap Nat Nat := {}
  /-- String table name for the panic message -/
  panicStrName : String := ".str.0"
  /-- String table contents -/
  stringTable : Array String := #[]
  /-- Per-function borrow info: FuncId.id → Array Bool (indexed by param) -/
  borrowInfo : Std.HashMap Nat (Array Bool) := {}
  /-- Cache of generated type-specialized eraser functions -/
  eraserCache : Std.HashMap String String := {}
  /-- Cache of generated type-specialized cloner functions -/
  clonerCache : Std.HashMap String String := {}
  /-- Cache of generated TypeDesc globals -/
  typeDescCache : Std.HashMap String String := {}
  /-- Target operating system for ABI and platform decisions -/
  targetOs : TargetOS := .linux
  /-- Pointer width in bytes -/
  ptrSize : Nat := 8
  /-- Set to true when the current instruction should be emitted as a tail call -/
  emitAsTailCall : Bool := false

instance : Inhabited CodegenState where
  default := { moduleState := default, funcState := default, ptrSize := 8 }

/-- Codegen monad -/
abbrev CodegenM := StateM CodegenState

namespace CodegenM

/-- Initialize codegen state -/
def init (name : String) (triple : Option String := none) (dataLayout : Option String := none)
    (ptrSize : Nat) (targetOs : TargetOS) : CodegenState :=
  { moduleState := ModuleBuilder.init name triple dataLayout, ptrSize, targetOs }

/-- Is the target OS Windows? (Uses the Windows x64 calling convention) -/
def isWindows : CodegenM Bool := do return (← get).targetOs.isWindowsABI

/-- Get pointer size in bytes -/
def getPointerSize : CodegenM Nat := do return (← get).ptrSize

/-- Run a FuncBuilder operation -/
def withFuncBuilder (m : FuncBuilder α) : CodegenM α := do
  let s ← get
  let (result, funcState') := Id.run (StateT.run m s.funcState)
  set { s with funcState := funcState' }
  pure result

/-- Run a ModuleBuilder operation -/
def withModuleBuilder (m : ModuleBuilder α) : CodegenM α := do
  let s ← get
  let (result, moduleState') := Id.run (StateT.run m s.moduleState)
  set { s with moduleState := moduleState' }
  pure result

/-- Map an Alloy local to LLVM local with its type -/
def mapLocal (alloyId : Nat) (llvmRef : LocalRef) (ty : ClosedTy) : CodegenM Unit := do
  modify fun s => { s with
    localMap := s.localMap.insert alloyId llvmRef
    localTypes := s.localTypes.insert alloyId ty
  }

/-- Get LLVM local for Alloy local -/
def getLocal (alloyId : Nat) : CodegenM (Option LocalRef) := do
  let s ← get
  pure (s.localMap.get? alloyId)

/-- Get type of an Alloy local -/
def getLocalTy (alloyId : Nat) : CodegenM ClosedTy := do
  let s ← get
  pure (s.localTypes.get? alloyId |>.getD (.prim .i64))

/-- Get Alloy type from codegen state, returning none if not mapped -/
def getLocalTy? (alloyId : Nat) : CodegenM (Option ClosedTy) := do
  let s ← get
  pure (s.localTypes.get? alloyId)

/-- Get LLVM local, creating if needed (with default type) -/
def getOrCreateLocal (alloyId : Nat) (defaultTy : ClosedTy := .prim .i64) : CodegenM LocalRef := do
  match ← getLocal alloyId with
  | some ref => pure ref
  | none =>
    let ref ← withFuncBuilder FuncBuilder.freshLocal
    mapLocal alloyId ref defaultTy
    pure ref

/-- Map an Alloy block to LLVM label -/
def mapBlock (alloyId : Nat) (label : Label) : CodegenM Unit := do
  modify fun s => { s with blockMap := s.blockMap.insert alloyId label }

/-- Get LLVM label for Alloy block -/
def getBlock (alloyId : Nat) : CodegenM (Option Label) := do
  let s ← get
  pure (s.blockMap.get? alloyId)

/-- Get or create LLVM label for Alloy block -/
def getOrCreateBlock (alloyId : Nat) : CodegenM Label := do
  match ← getBlock alloyId with
  | some label => pure label
  | none =>
    let label ← withFuncBuilder (FuncBuilder.freshLabel "bb")
    mapBlock alloyId label
    pure label

/-- Register a function -/
def registerFunc (alloyId : Nat) (name : String) (sig : ClosedSignature) : CodegenM Unit := do
  modify fun s => { s with
    funcNames := s.funcNames.insert alloyId name
    funcSigs := s.funcSigs.insert alloyId sig
  }

/-- Get function name -/
def getFuncName (alloyId : Nat) : CodegenM String := do
  let s ← get
  pure (s.funcNames.get? alloyId |>.getD s!"fn{alloyId}")

/-- Get function signature -/
def getFuncSig (alloyId : Nat) : CodegenM (Option ClosedSignature) := do
  let s ← get
  pure (s.funcSigs.get? alloyId)

/-- Clear per-function state -/
def markBlockDead (alloyBlockId : Nat) : CodegenM Unit := do
  modify fun s => { s with deadBlocks := s.deadBlocks.insert alloyBlockId }

/-- Signal that a noreturn call was emitted during instruction lowering -/
def signalNoReturn : CodegenM Unit := do
  modify fun s => { s with noreturnEmitted := true }

/-- Check and clear the noreturn flag -/
def consumeNoReturn : CodegenM Bool := do
  let s ← get
  if s.noreturnEmitted then
    modify fun s => { s with noreturnEmitted := false }
    pure true
  else
    pure false

def isBlockDead (alloyBlockId : Nat) : CodegenM Bool := do
  let s ← get
  pure (s.deadBlocks.contains alloyBlockId)

def clearFuncState : CodegenM Unit := do
  modify fun s => { s with
    localMap := {}
    localTypes := {}
    blockMap := {}
    deadBlocks := {}
    noreturnEmitted := false
    stringConstLocals := {}
    funcState := {}
    currentFunc := none
  }

/-- Set current function -/
def setCurrentFunc (func : ClosedFunc) : CodegenM Unit := do
  modify fun s => { s with currentFunc := some func }

/-- Get current function -/
def getCurrentFunc : CodegenM (Option ClosedFunc) := do
  let s ← get
  pure s.currentFunc

/-- Get local types map -/
def getLocalTypes : CodegenM (Std.HashMap Nat ClosedTy) := do
  let s ← get
  pure s.localTypes

/-- Check if an extern function has been declared -/
def isExternDeclared (name : String) : CodegenM Bool := do
  let s ← get
  pure (s.declaredExterns.contains name)

/-- Mark an extern function as declared -/
def markExternDeclared (name : String) : CodegenM Unit := do
  modify fun s => { s with declaredExterns := s.declaredExterns.insert name }

end CodegenM

/-- Get the Alloy type of an operand -/
def operandTy (op : Operand) : CodegenM ClosedTy := do
  match op with
  | .local id =>
    let codegenTy ← CodegenM.getLocalTy? id.id
    match codegenTy with
    | some ty => pure ty
    | none =>
      -- Fall back to Alloy Func's localTypes
      let func? ← CodegenM.getCurrentFunc
      match func?.bind (·.getLocalType id) with
      | some ty => pure ty
      | none => pure .rawPtr
  | .const c => pure c.ty
  | .global _ => pure .rawPtr
  | .func _ => pure .rawPtr

/-- Unbox a ptr result from soma_apply to the expected LLVM type -/
def unboxApplyResult (ref : LocalRef) (retTy : ClosedTy) : CodegenM LocalRef := do
  let expectedLLVMTy := convertTy retTy
  if expectedLLVMTy == .ptr then pure ref
  else if expectedLLVMTy.isInt then
    CodegenM.withFuncBuilder (FuncBuilder.ptrtoint expectedLLVMTy (.local ref))
  else
    CodegenM.withFuncBuilder (FuncBuilder.load expectedLLVMTy (.local ref))

/-- Coerce an LLVM value from one type to another, handling all valid conversions -/
def coerceValue (srcTy dstTy : LLVMType) (val : LLVMValue) : CodegenM LLVMValue := do
  if srcTy == dstTy then pure val
  else
    let ref ← CodegenM.withFuncBuilder do
      -- Integer ↔ ptr conversions
      if dstTy == .ptr && srcTy.isInt then
        FuncBuilder.inttoptr srcTy val
      else if dstTy.isInt && srcTy == .ptr then
        FuncBuilder.ptrtoint dstTy val
      -- Pointer to pointer (identity with opaque pointers)
      else if dstTy == .ptr && srcTy == .ptr then
        FuncBuilder.bitcast .ptr .ptr val
      -- Integer to integer (different sizes)
      else if dstTy.isInt && srcTy.isInt then
        let srcBits := srcTy.intBits.getD 64
        let dstBits := dstTy.intBits.getD 64
        if srcBits < dstBits then FuncBuilder.zext srcTy dstTy val
        else if srcBits > dstBits then FuncBuilder.trunc srcTy dstTy val
        else FuncBuilder.asLocalRef dstTy val
      -- Tagged union struct { i32, ptr } → extract tag (i32)
      else if srcTy == taggedTy && dstTy == .i32 then
        FuncBuilder.extractvalue srcTy val #[0]
      -- ptr → aggregate: load from pointer
      else if srcTy == .ptr && !(dstTy.isInt) && !(dstTy == .ptr) then
        FuncBuilder.load dstTy val
      -- Aggregate → ptr: box via malloc
      else if dstTy == .ptr && !srcTy.isInt then do
        let sizePtr ← FuncBuilder.gepi32 srcTy (.const .null) #[1]
        let sizeI64 ← FuncBuilder.ptrtoint .i64 (.local sizePtr)
        let boxPtr ← FuncBuilder.callNamed .ptr "malloc" #[(.i64, .local sizeI64)]
        FuncBuilder.store srcTy val (.local boxPtr)
        pure boxPtr
      else
        panic! s!"CODEGEN BUG: coerceValue cannot convert {srcTy.toLLVM} to {dstTy.toLLVM}"
    pure (.local ref)

/-- Convert Alloy operand to LLVM value -/
def convertOperand (op : Operand) : CodegenM LLVMValue := do
  match op with
  | .local id =>
    match ← CodegenM.getLocal id.id with
    | some ref => pure (.local ref)
    | none =>
      let s ← get
      let fname := match s.currentFunc with
        | some f => f.sig.name
        | none => "unknown"
      panic! s!"CODEGEN BUG: local %{id.id} not found in {fname}"
  | .const c =>
    match c with
    | .int val t =>
      let bits := match t with
        | .i8 | .u8 => 8 | .i16 | .u16 => 16 | .i32 | .u32 => 32 | _ => 64
      pure (.const (.int val bits))
    | .float val t =>
      match t with
      | .f32 => pure (.const (.float32 val))
      | _ => pure (.const (.float64 val))
    | .bool b => pure (.const (.bool b))
    | .unit => pure (.const (.int 0 8))
    | .null _ => pure (.const .null)
    | .string idx len =>
      let staticBit : Int := Int.ofNat (1 <<< 63)
      let staticLen : Int := (Int.ofNat len) + staticBit
      pure (.const (.struct false #[
        (.ptr, .globalRef s!".str.{idx}"),
        (.i64, .int staticLen 64)
      ]))
    | .undef t => pure (.const (.undef (convertTy t)))
  | .global id => pure (.global ⟨s!"global{id.id}"⟩)
  | .func id =>
    let name ← CodegenM.getFuncName id.id
    pure (.global ⟨name⟩)

/-- Look up the LLVM ground-truth type -/
def operandLLVMTy (op : Operand) : CodegenM (Option LLVMType) := do
  match op with
  | .local id =>
    match ← CodegenM.getLocal id.id with
    | some llvmRef => CodegenM.withFuncBuilder (FuncBuilder.getLocalType llvmRef)
    | none => pure none
  | _ => pure none

/-- Convert operand with its LLVM type preferring ground-truth LLVM type over Alloy-derived type -/
def convertOperandWithTy (op : Operand) : CodegenM (LLVMType × LLVMValue) := do
  let val ← convertOperand op
  match ← operandLLVMTy op with
  | some llvmTy => pure (llvmTy, val)
  | none =>
    let ty ← operandTy op
    pure (convertTy ty, val)

/-- Ensure a value is a pointer, converting if necessary -/
def ensurePtr (ty : LLVMType) (val : LLVMValue) : CodegenM LLVMValue :=
  coerceValue ty .ptr val

/-- Convert a value to i64, handling both pointers and other integer types -/
def toI64 (ty : LLVMType) (val : LLVMValue) : CodegenM LocalRef := do
  if ty == .ptr then
    CodegenM.withFuncBuilder (FuncBuilder.ptrtoint .i64 val)
  else if ty == .i64 then
    -- Already i64
    CodegenM.withFuncBuilder (FuncBuilder.asLocalRef .i64 val)
  else if ty.isInt then
    -- Other integer type, extend or truncate to i64
    let bits := ty.intBits.getD 64
    if bits < 64 then
      CodegenM.withFuncBuilder (FuncBuilder.zext ty .i64 val)
    else
      CodegenM.withFuncBuilder (FuncBuilder.trunc ty .i64 val)
  else
    -- Aggregate type: box via malloc, return ptr as i64
    let sizePtr ← CodegenM.withFuncBuilder
      (FuncBuilder.gepi32 ty (.const .null) #[1])
    let sizeI64 ← CodegenM.withFuncBuilder
      (FuncBuilder.ptrtoint .i64 (.local sizePtr))
    let boxPtr ← CodegenM.withFuncBuilder do
      FuncBuilder.callNamed .ptr "malloc" #[(.i64, .local sizeI64)]
    CodegenM.withFuncBuilder do
      FuncBuilder.store ty val (.local boxPtr)
    CodegenM.withFuncBuilder (FuncBuilder.ptrtoint .i64 (.local boxPtr))

/-- Convert an i64 value back to the target LLVM type -/
def fromI64 (targetTy : LLVMType) (val : LLVMValue) : CodegenM LocalRef := do
  if targetTy == .ptr then
    CodegenM.withFuncBuilder (FuncBuilder.inttoptr .i64 val)
  else if targetTy == .i64 then
    CodegenM.withFuncBuilder (FuncBuilder.asLocalRef .i64 val)
  else if targetTy.isInt then
    let bits := targetTy.intBits.getD 64
    if bits < 64 then
      CodegenM.withFuncBuilder (FuncBuilder.trunc .i64 targetTy val)
    else
      CodegenM.withFuncBuilder (FuncBuilder.zext targetTy .i64 val)
  else
    -- Aggregate type: unbox from heap pointer
    let boxPtr ← CodegenM.withFuncBuilder (FuncBuilder.inttoptr .i64 val)
    CodegenM.withFuncBuilder (FuncBuilder.load targetTy (.local boxPtr))

/-- The LLVM type used for the SomaString fat pointer -/
def somaStringLLVMTy : LLVMType := .struct false #[.ptr, .i64]

/-- The LLVM type used for the SomaList struct { data, len, offset } -/
def somaListLLVMTy : LLVMType := .struct false #[.ptr, .i32, .i32]

/-- Check if a type is the SomaString struct -/
def isSomaStringLLVMTy (ty : LLVMType) : Bool :=
  ty == somaStringLLVMTy

/-- Compute the SysV x86-64 coerced type for a struct -/
def sysVCoercedType (ty : LLVMType) : LLVMType :=
  match ty with
  | .struct _ fields =>
    let totalBytes := fields.foldl (fun acc f =>
      match f with
      | .ptr => acc + 8
      | .i64 | .double => acc + 8
      | .i32 | .float => acc + 4
      | .i16 => acc + 2
      | .i8 | .i1 => acc + 1
      | _ => acc + 8) 0
    let numEightbytes := (totalBytes + 7) / 8
    if numEightbytes == 1 then .i64
    else .struct false ((List.replicate numEightbytes LLVMType.i64).toArray)
  | _ => ty

/-- Coerce a struct value to its SysV ABI type via alloca-store-load -/
def coerceStructToSysV (origTy coercedTy : LLVMType) (val : LLVMValue)
    : CodegenM LocalRef := do
  let alloca ← CodegenM.withFuncBuilder (FuncBuilder.alloca origTy)
  CodegenM.withFuncBuilder (FuncBuilder.store origTy val (.local alloca))
  CodegenM.withFuncBuilder (FuncBuilder.load coercedTy (.local alloca))

/-- Coerce a SysV ABI return value back to the original struct type -/
def coerceSysVToStruct (origTy coercedTy : LLVMType) (val : LLVMValue)
    : CodegenM LocalRef := do
  let alloca ← CodegenM.withFuncBuilder (FuncBuilder.alloca coercedTy)
  CodegenM.withFuncBuilder (FuncBuilder.store coercedTy val (.local alloca))
  CodegenM.withFuncBuilder (FuncBuilder.load origTy (.local alloca))

/-- Call a named C function with correct ABI for struct-by-value args/returns -/
def callCFuncStructABI (retTy : LLVMType) (name : String)
    (args : Array (LLVMType × LLVMValue)) : CodegenM LocalRef := do
  let winABI ← CodegenM.isWindows
  let hasStructRet := retTy.isStruct && winABI
  let mut abiArgs : Array (LLVMType × LLVMValue) := #[]
  let mut argAttrs : Array (Option String) := #[]
  let sretAlloca? ← if hasStructRet then do
      let alloca ← CodegenM.withFuncBuilder (FuncBuilder.alloca retTy)
      abiArgs := abiArgs.push (.ptr, .local alloca)
      argAttrs := argAttrs.push (some s!"sret({retTy.toLLVM})")
      pure (some alloca)
    else pure none
  for (ty, val) in args do
    if ty.isStruct && winABI then
      let alloca ← CodegenM.withFuncBuilder (FuncBuilder.alloca ty)
      CodegenM.withFuncBuilder (FuncBuilder.store ty val (.local alloca))
      abiArgs := abiArgs.push (.ptr, .local alloca)
      argAttrs := argAttrs.push (some s!"byval({ty.toLLVM})")
    else if ty.isStruct && !winABI then
      let coerced := sysVCoercedType ty
      let ref ← coerceStructToSysV ty coerced val
      abiArgs := abiArgs.push (coerced, .local ref)
      argAttrs := argAttrs.push none
    else
      abiArgs := abiArgs.push (ty, val)
      argAttrs := argAttrs.push none
  let callRetTy := if hasStructRet then LLVMType.void
    else if retTy.isStruct && !winABI then sysVCoercedType retTy
    else retTy
  let needsSysVCoerce := retTy.isStruct && !winABI
  let rawRef ← CodegenM.withFuncBuilder do
    let inst : LLVMInst := .call false none callRetTy (.global ⟨name⟩) abiArgs argAttrs
    if hasStructRet then
      FuncBuilder.emitVoid inst
      FuncBuilder.load retTy (.local sretAlloca?.get!)
    else
      FuncBuilder.emit inst
  if needsSysVCoerce then
    coerceSysVToStruct retTy callRetTy (.local rawRef)
  else
    pure rawRef

/-- Call a named void C function with correct ABI for struct-by-value args -/
def callCFuncStructABIVoid (name : String) (args : Array (LLVMType × LLVMValue))
    : CodegenM Unit := do
  let winABI ← CodegenM.isWindows
  let mut abiArgs : Array (LLVMType × LLVMValue) := #[]
  let mut argAttrs : Array (Option String) := #[]
  for (ty, val) in args do
    if ty.isStruct && winABI then
      let alloca ← CodegenM.withFuncBuilder (FuncBuilder.alloca ty)
      CodegenM.withFuncBuilder (FuncBuilder.store ty val (.local alloca))
      abiArgs := abiArgs.push (.ptr, .local alloca)
      argAttrs := argAttrs.push (some s!"byval({ty.toLLVM})")
    else if ty.isStruct && !winABI then
      let coerced := sysVCoercedType ty
      let ref ← coerceStructToSysV ty coerced val
      abiArgs := abiArgs.push (coerced, .local ref)
      argAttrs := argAttrs.push none
    else
      abiArgs := abiArgs.push (ty, val)
      argAttrs := argAttrs.push none
  CodegenM.withFuncBuilder do
    FuncBuilder.emitVoid (.call false none .void (.global ⟨name⟩) abiArgs argAttrs)

/-- Convert Alloy binary operation to LLVM -/
def convertBinOp (op : BinOp) (ty : ClosedTy) (lhs rhs : LLVMValue) : CodegenM LocalRef := do
  let llvmTy := convertTy ty
  let isFloat := match ty with
    | .prim p => primTyIsFloat p
    | _ => false
  let isSigned := match ty with
    | .prim p => p.isSigned
    | _ => true

  CodegenM.withFuncBuilder do
    match op with
    | .add => if isFloat then FuncBuilder.fadd llvmTy lhs rhs
              else FuncBuilder.add llvmTy lhs rhs
    | .sub => if isFloat then FuncBuilder.fsub llvmTy lhs rhs
              else FuncBuilder.sub llvmTy lhs rhs
    | .mul => if isFloat then FuncBuilder.fmul llvmTy lhs rhs
              else FuncBuilder.mul llvmTy lhs rhs
    | .div =>
      if isFloat then FuncBuilder.fdiv llvmTy lhs rhs
      else if isSigned then FuncBuilder.sdiv llvmTy lhs rhs
      else FuncBuilder.udiv llvmTy lhs rhs
    | .rem =>
      if isFloat then FuncBuilder.frem llvmTy lhs rhs
      else if isSigned then FuncBuilder.srem llvmTy lhs rhs
      else FuncBuilder.urem llvmTy lhs rhs
    | .and => FuncBuilder.and_ llvmTy lhs rhs
    | .or => FuncBuilder.or_ llvmTy lhs rhs
    | .xor => FuncBuilder.xor_ llvmTy lhs rhs
    | .shl => FuncBuilder.shl llvmTy lhs rhs
    | .shr => if isSigned then FuncBuilder.ashr llvmTy lhs rhs
              else FuncBuilder.lshr llvmTy lhs rhs
    | .eq =>
      if isFloat then FuncBuilder.fcmp .oeq llvmTy lhs rhs
      else FuncBuilder.icmp .eq llvmTy lhs rhs
    | .ne =>
      if isFloat then FuncBuilder.fcmp .one llvmTy lhs rhs
      else FuncBuilder.icmp .ne llvmTy lhs rhs
    | .lt =>
      if isFloat then FuncBuilder.fcmp .olt llvmTy lhs rhs
      else if isSigned then FuncBuilder.icmp .slt llvmTy lhs rhs
      else FuncBuilder.icmp .ult llvmTy lhs rhs
    | .le =>
      if isFloat then FuncBuilder.fcmp .ole llvmTy lhs rhs
      else if isSigned then FuncBuilder.icmp .sle llvmTy lhs rhs
      else FuncBuilder.icmp .ule llvmTy lhs rhs
    | .gt =>
      if isFloat then FuncBuilder.fcmp .ogt llvmTy lhs rhs
      else if isSigned then FuncBuilder.icmp .sgt llvmTy lhs rhs
      else FuncBuilder.icmp .ugt llvmTy lhs rhs
    | .ge =>
      if isFloat then FuncBuilder.fcmp .oge llvmTy lhs rhs
      else if isSigned then FuncBuilder.icmp .sge llvmTy lhs rhs
      else FuncBuilder.icmp .uge llvmTy lhs rhs

/-- Convert Alloy unary operation to LLVM with proper source type -/
def convertUnOp (op : UnOp 0) (srcTy : ClosedTy) (operand : LLVMValue) : CodegenM LocalRef := do
  let llvmSrcTy := convertTy srcTy
  let isFloat := match srcTy with
    | .prim p => primTyIsFloat p
    | _ => false

  CodegenM.withFuncBuilder do
    match op with
    | .neg =>
      if isFloat then FuncBuilder.fneg llvmSrcTy operand
      else FuncBuilder.sub llvmSrcTy (intVal 0 64) operand
    | .not =>
      -- For booleans, use xor with true; for integers, xor with -1
      match srcTy with
      | .prim .bool => FuncBuilder.xor_ .i1 operand (boolVal true)
      | _ => FuncBuilder.xor_ llvmSrcTy operand (intVal (-1) 64)
    | .trunc t =>
      let toTy := convertPrimTy t
      FuncBuilder.trunc llvmSrcTy toTy operand
    | .zext t =>
      let toTy := convertPrimTy t
      FuncBuilder.zext llvmSrcTy toTy operand
    | .sext t =>
      let toTy := convertPrimTy t
      FuncBuilder.sext llvmSrcTy toTy operand
    | .itof t =>
      let toTy := convertPrimTy t
      let isSigned := match srcTy with
        | .prim p => p.isSigned
        | _ => true
      if isSigned then FuncBuilder.sitofp llvmSrcTy toTy operand
      else FuncBuilder.uitofp llvmSrcTy toTy operand
    | .ftoi t =>
      let toTy := convertPrimTy t
      let isSigned := t.isSigned
      if isSigned then FuncBuilder.fptosi llvmSrcTy toTy operand
      else FuncBuilder.fptoui llvmSrcTy toTy operand
    | .bitcast t =>
      let toTy := convertTy t
      if llvmSrcTy == toTy then
        -- Same type, no-op
        if toTy.isInt || toTy == .ptr then
          FuncBuilder.asLocalRef toTy operand
        else
          -- For structs/other types, use select to produce new SSA value
          FuncBuilder.select toTy (boolVal true) operand operand
      else if llvmSrcTy.isInt && toTy == .ptr then
        FuncBuilder.inttoptr llvmSrcTy operand
      else if llvmSrcTy == .ptr && toTy.isInt then
        FuncBuilder.ptrtoint toTy operand
      else if llvmSrcTy == .ptr && toTy == .ptr then
        FuncBuilder.bitcast .ptr .ptr operand
      else if llvmSrcTy == .ptr && toTy.isStruct then
        FuncBuilder.load toTy operand
      else if llvmSrcTy.isInt && toTy.isInt then
        let srcBits := llvmSrcTy.intBits.getD 64
        let dstBits := toTy.intBits.getD 64
        if srcBits < dstBits then FuncBuilder.zext llvmSrcTy toTy operand
        else if srcBits > dstBits then FuncBuilder.trunc llvmSrcTy toTy operand
        else FuncBuilder.bitcast llvmSrcTy toTy operand
      else
        panic! s!"CODEGEN BUG: bitcast cannot convert {llvmSrcTy.toLLVM} to {toTy.toLLVM}"
    | .ptrtoint t =>
      let toTy := convertPrimTy t
      -- Handle the case where source might already be an integer (from dead code)
      if llvmSrcTy == .ptr then
        FuncBuilder.ptrtoint toTy operand
      else if llvmSrcTy.isInt then
        -- Already an integer, just convert to target size
        let srcBits := llvmSrcTy.intBits.getD 64
        let dstBits := toTy.intBits.getD 64
        if srcBits == dstBits then
          FuncBuilder.asLocalRef llvmSrcTy operand
        else if srcBits < dstBits then
          FuncBuilder.zext llvmSrcTy toTy operand
        else
          FuncBuilder.trunc llvmSrcTy toTy operand
      else
        panic! s!"CODEGEN BUG: ptrtoint cannot convert {llvmSrcTy.toLLVM} to {toTy.toLLVM}"
    | .inttoptr =>
      -- Handle the case where source might already be a pointer (shouldn't happen but be safe)
      if llvmSrcTy == .ptr then
        FuncBuilder.bitcast .ptr .ptr operand
      else
        FuncBuilder.inttoptr llvmSrcTy operand

/-- Mangle a type into a function name suffix -/
private def mangleTyName (ty : ClosedTy) : String :=
  Somac.Alloy.Monomorphize.mangleTy ty

/-- Compute a stable structural key for the eraser/cloner cache from a closed type -/
private def tyKey (ty : ClosedTy) : String := mangleTyName ty

mutual
/-- Emit type-recursive erasure code -/
partial def emitEraseForType (valRef : LLVMValue) (ty : ClosedTy) : CodegenM Unit := do
  match ty with
  | .prim _ | .funcPtr _ _ =>
    pure ()
  | .rawPtr =>
    -- Opaque pointer: delegate to runtime for tag-based dispatch
    CodegenM.withFuncBuilder do
      FuncBuilder.callNamedVoid "soma_era_free" #[(.ptr, valRef)]
  | .ptr _ =>
    CodegenM.withFuncBuilder do
      FuncBuilder.callNamedVoid "soma_era_free" #[(.ptr, valRef)]
  | .tagged _ _ =>
    -- Tagged union: use type-specialized eraser that knows field layout
    let eraserName ← getOrEmitEraser ty
    let valAsPtr ← ensurePtr (convertTy ty) valRef
    CodegenM.withFuncBuilder do
      FuncBuilder.callNamedVoid eraserName #[(.ptr, valAsPtr)]
  | .closure _ _ =>
    -- Closure: use type-specialized eraser
    let eraserName ← getOrEmitEraser ty
    let valAsPtr ← ensurePtr .ptr valRef
    CodegenM.withFuncBuilder do
      FuncBuilder.callNamedVoid eraserName #[(.ptr, valAsPtr)]
  | .struct fields =>
    if isStringObjTy ty then
      -- String fat pointer: call soma_era_string with { ptr, i64 } struct
      let llvmTy := convertTy ty
      callCFuncStructABIVoid "soma_era_string" #[(llvmTy, valRef)]
    else if isListObjTy ty then
      callCFuncStructABIVoid "soma_list_era" #[(somaListLLVMTy, valRef)]
    else
      -- Struct: recurse into each field that may contain pointers
      let llvmTy := convertTy ty
      for i in [:fields.size] do
        if h : i < fields.size then
          let (_, fieldTy) := fields[i]
          if fieldTy.needsErase then
            let fieldRef ← CodegenM.withFuncBuilder do
              FuncBuilder.extractvalue llvmTy valRef #[i]
            emitEraseForType (.local fieldRef) fieldTy
  | .array _ _ =>
    -- Arrays are value types at this level so we recursively erase elements that own memory
    let elemTy := getArrayElemTy ty
    if elemTy.needsErase then
      let llvmArrTy := convertTy ty
      match ty with
      | .array _ size =>
        for i in [:size] do
          let elemRef ← CodegenM.withFuncBuilder do
            FuncBuilder.extractvalue llvmArrTy valRef #[i]
          emitEraseForType (.local elemRef) elemTy
      | _ => pure ()
    else
      pure ()
  | .var _ =>
    -- Should not occur at closed type level (nomatch in convertTy)
    pure ()

/-- Get or emit a type-specialized eraser function -/
partial def getOrEmitEraser (ty : ClosedTy) : CodegenM String := do
  let key := tyKey ty
  let s ← get
  if let some name := s.eraserCache.get? key then
    return name

  let name := s!"soma_erase${mangleTyName ty}"
  modify fun s => { s with eraserCache := s.eraserCache.insert key name }

  let savedFuncState := (← get).funcState

  let eraserFunc ← do
    modify fun s => { s with funcState := {} }

    let paramRef ← CodegenM.withFuncBuilder FuncBuilder.freshLocal

    let entryLabel ← CodegenM.withFuncBuilder (FuncBuilder.freshLabel "entry")
    CodegenM.withFuncBuilder (FuncBuilder.startBlock entryLabel)

    match ty with
    | .tagged _tagTy variants =>
      -- Headerless tagged union: {i32 tag, ptr payload} on stack,
      -- payload is a naturally-typed struct per variant
      let structVal ← CodegenM.withFuncBuilder (FuncBuilder.load taggedTy (.local paramRef))
      let tagVal ← CodegenM.withFuncBuilder do
        FuncBuilder.extractvalue taggedTy (.local structVal) #[0]
      let payloadPtr ← CodegenM.withFuncBuilder do
        FuncBuilder.extractvalue taggedTy (.local structVal) #[1]

      let isNull ← CodegenM.withFuncBuilder do
        FuncBuilder.icmp .eq .ptr (.local payloadPtr) (.const .null)
      let nullLabel ← CodegenM.withFuncBuilder (FuncBuilder.freshLabel "null_payload")
      let eraseLabel ← CodegenM.withFuncBuilder (FuncBuilder.freshLabel "erase")
      CodegenM.withFuncBuilder (FuncBuilder.condBr (.local isNull) nullLabel eraseLabel)

      CodegenM.withFuncBuilder (FuncBuilder.startBlock eraseLabel)

      let hasAnyErasableFields := variants.any fun (_, fields) =>
        fields.any fun ft => ft.needsErase

      let payloadByteSize : Int := Int.ofNat (maxPackedPayloadSize variants (← get).ptrSize)

      if hasAnyErasableFields then
        let freeLabel ← CodegenM.withFuncBuilder (FuncBuilder.freshLabel "free_payload")
        let mut cases : Array (LLVMConst × Label) := #[]
        let mut variantLabels : Array Label := #[]

        for vi in [:variants.size] do
          let lbl ← CodegenM.withFuncBuilder (FuncBuilder.freshLabel s!"variant_{vi}")
          variantLabels := variantLabels.push lbl
          cases := cases.push (.int (Int.ofNat vi) 32, lbl)

        CodegenM.withFuncBuilder (FuncBuilder.switch .i32 (.local tagVal) freeLabel cases)

        for h : vi in [:variants.size] do
          if hv : vi < variants.size then
            let (_, fields) := variants[vi]
            let lbl := variantLabels[vi]!
            CodegenM.withFuncBuilder (FuncBuilder.startBlock lbl)

            let layout := computePackedLayout fields (← get).ptrSize
            for hf : fi in [:fields.size] do
              if h2 : fi < fields.size then
                let logIdx := layout.physToLog.getD fi fi
                let fieldTy := fields.getD logIdx fields[fi]
                if fieldTy.needsErase then
                  let fieldAddr ← CodegenM.withFuncBuilder do
                    FuncBuilder.gepi32 layout.llvmTy (.local payloadPtr) #[0, fi]
                  let fieldLLVMTy := convertTy fieldTy
                  let fieldVal ← CodegenM.withFuncBuilder do
                    FuncBuilder.load fieldLLVMTy (.local fieldAddr)
                  let fieldAsPtr ← ensurePtr fieldLLVMTy (.local fieldVal)
                  let fieldEraserName ← getOrEmitEraser fieldTy
                  CodegenM.withFuncBuilder do
                    FuncBuilder.callNamedVoid fieldEraserName #[(.ptr, fieldAsPtr)]

            CodegenM.withFuncBuilder (FuncBuilder.br freeLabel)

        -- Free block: free headerless payload buffer + boxed struct
        CodegenM.withFuncBuilder (FuncBuilder.startBlock freeLabel)
        CodegenM.withFuncBuilder do
          FuncBuilder.callNamedVoid "soma_pool_free_raw"
            #[(.ptr, .local payloadPtr), (.i64, .const (.int payloadByteSize 64))]
        CodegenM.withFuncBuilder do
          FuncBuilder.callNamedVoid "free" #[(.ptr, .local paramRef)]
        CodegenM.withFuncBuilder FuncBuilder.retVoid
      else
        -- No erasable fields — just free payload and struct
        CodegenM.withFuncBuilder do
          FuncBuilder.callNamedVoid "soma_pool_free_raw"
            #[(.ptr, .local payloadPtr), (.i64, .const (.int payloadByteSize 64))]
        CodegenM.withFuncBuilder do
          FuncBuilder.callNamedVoid "free" #[(.ptr, .local paramRef)]
        CodegenM.withFuncBuilder FuncBuilder.retVoid

      -- Null-payload block: free only the boxed struct
      CodegenM.withFuncBuilder (FuncBuilder.startBlock nullLabel)
      CodegenM.withFuncBuilder do
        FuncBuilder.callNamedVoid "free" #[(.ptr, .local paramRef)]
      CodegenM.withFuncBuilder FuncBuilder.retVoid

    | .closure _ _ =>
      -- Delegate to soma_era_closure which reads env_size from _pad[1..2]
      CodegenM.withFuncBuilder do
        FuncBuilder.callNamedVoid "soma_era_closure" #[(.ptr, .local paramRef)]
      CodegenM.withFuncBuilder FuncBuilder.retVoid

    | .rawPtr =>
      -- rawPtr fallback: generic tag-based dispatch
      CodegenM.withFuncBuilder do
        FuncBuilder.callNamedVoid "soma_era_free" #[(.ptr, .local paramRef)]
      CodegenM.withFuncBuilder FuncBuilder.retVoid

    | .ptr _ =>
      -- Pointer to known type: generic free
      CodegenM.withFuncBuilder do
        FuncBuilder.callNamedVoid "soma_era_free" #[(.ptr, .local paramRef)]
      CodegenM.withFuncBuilder FuncBuilder.retVoid

    | _ =>
      -- Flat types, funcPtrs etc — should not reach here but emit no-op
      CodegenM.withFuncBuilder FuncBuilder.retVoid

    let blocks ← CodegenM.withFuncBuilder FuncBuilder.getBlocks
    pure ({
      name := name
      retTy := .void
      params := #[{ name := "v0", ty := .ptr }]
      attrs := { nounwind := true }
      blocks := blocks
      isDeclaration := false
    } : LLVMFunc)

  -- Add to module
  CodegenM.withModuleBuilder (ModuleBuilder.addFunc eraserFunc)

  -- Restore function builder state
  modify fun s => { s with funcState := savedFuncState }

  return name

/-- Get or emit a type-specialized cloner function -/
partial def getOrEmitCloner (ty : ClosedTy) : CodegenM String := do
  let key := tyKey ty
  let s ← get
  if let some name := s.clonerCache.get? key then
    return name

  let name := s!"soma_clone${mangleTyName ty}"
  modify fun s => { s with clonerCache := s.clonerCache.insert key name }

  let savedFuncState := (← get).funcState

  let clonerFunc ← do
    modify fun s => { s with funcState := {} }

    let valParam ← CodegenM.withFuncBuilder FuncBuilder.freshLocal
    let lblParam ← CodegenM.withFuncBuilder FuncBuilder.freshLocal

    let entryLabel ← CodegenM.withFuncBuilder (FuncBuilder.freshLabel "entry")
    CodegenM.withFuncBuilder (FuncBuilder.startBlock entryLabel)

    match ty with
    | .tagged _tagTy variants =>
      let structVal ← CodegenM.withFuncBuilder (FuncBuilder.load taggedTy (.local valParam))
      let tagVal ← CodegenM.withFuncBuilder (FuncBuilder.extractvalue taggedTy (.local structVal) #[0])
      let payloadPtr ← CodegenM.withFuncBuilder (FuncBuilder.extractvalue taggedTy (.local structVal) #[1])

      let isNull ← CodegenM.withFuncBuilder do
        FuncBuilder.icmp .eq .ptr (.local payloadPtr) (.const .null)
      let cloneLabel ← CodegenM.withFuncBuilder (FuncBuilder.freshLabel "clone")
      let doneLabel ← CodegenM.withFuncBuilder (FuncBuilder.freshLabel "done")
      CodegenM.withFuncBuilder (FuncBuilder.condBr (.local isNull) doneLabel cloneLabel)

      CodegenM.withFuncBuilder (FuncBuilder.startBlock cloneLabel)

      let payloadByteSize : Int := Int.ofNat (maxPackedPayloadSize variants (← get).ptrSize)
      let newPayload ← CodegenM.withFuncBuilder do
        FuncBuilder.callNamed .ptr "soma_pool_alloc_raw"
          #[(.i64, .const (.int payloadByteSize 64))]

      let buildLabel ← CodegenM.withFuncBuilder (FuncBuilder.freshLabel "build")

      -- Check if any variant has fields that need cloning (not just flat copy)
      let hasAnyClonableFields := variants.any fun (_, fields) =>
        fields.any fun ft => ft.needsErase

      if hasAnyClonableFields then
        let mut cases : Array (LLVMConst × Label) := #[]
        let mut variantLabels : Array Label := #[]

        for vi in [:variants.size] do
          let lbl ← CodegenM.withFuncBuilder (FuncBuilder.freshLabel s!"clone_v{vi}")
          variantLabels := variantLabels.push lbl
          cases := cases.push (.int (Int.ofNat vi) 32, lbl)

        CodegenM.withFuncBuilder (FuncBuilder.switch .i32 (.local tagVal) buildLabel cases)

        -- Emit per-variant clone blocks
        for h : vi in [:variants.size] do
          if hv : vi < variants.size then
            let (_, fields) := variants[vi]
            let lbl := variantLabels[vi]!
            CodegenM.withFuncBuilder (FuncBuilder.startBlock lbl)

            let layout := computePackedLayout fields (← get).ptrSize
            for hf : fi in [:fields.size] do
              if h2 : fi < fields.size then
                let logIdx := layout.physToLog.getD fi fi
                let fieldTy := fields.getD logIdx fields[fi]
                let fieldLLVMTy := convertTy fieldTy
                let srcAddr ← CodegenM.withFuncBuilder do
                  FuncBuilder.gepi32 layout.llvmTy (.local payloadPtr) #[0, fi]
                let fieldVal ← CodegenM.withFuncBuilder do
                  FuncBuilder.load fieldLLVMTy (.local srcAddr)
                let dstAddr ← CodegenM.withFuncBuilder do
                  FuncBuilder.gepi32 layout.llvmTy (.local newPayload) #[0, fi]

                if fieldTy.needsErase then
                  let fieldAsPtr ← ensurePtr fieldLLVMTy (.local fieldVal)
                  let fieldClonerName ← getOrEmitCloner fieldTy
                  let clonedPtr ← CodegenM.withFuncBuilder do
                    FuncBuilder.callNamed .ptr fieldClonerName
                      #[(.ptr, fieldAsPtr), (.i32, .local lblParam)]
                  let clonedVal ← coerceValue .ptr fieldLLVMTy (.local clonedPtr)
                  CodegenM.withFuncBuilder do
                    FuncBuilder.store fieldLLVMTy clonedVal (.local dstAddr)
                else
                  CodegenM.withFuncBuilder do
                    FuncBuilder.store fieldLLVMTy (.local fieldVal) (.local dstAddr)

            CodegenM.withFuncBuilder (FuncBuilder.br buildLabel)
      else
        let payloadSizeVal : LLVMValue := .const (.int payloadByteSize 64)
        CodegenM.withFuncBuilder do
          FuncBuilder.memcpy (.local newPayload) (.local payloadPtr) payloadSizeVal
        CodegenM.withFuncBuilder (FuncBuilder.br buildLabel)

      -- Build block: allocate a new boxed {i32, ptr} struct and return as ptr
      CodegenM.withFuncBuilder (FuncBuilder.startBlock buildLabel)
      -- tagged struct = {i32 tag, ptr payload}, aligned to pointer size
      let taggedSize : Int := Int.ofNat ((← get).ptrSize * 2)
      let newStructPtr ← CodegenM.withFuncBuilder do
        FuncBuilder.callNamed .ptr "malloc"
          #[(.i64, .const (.int taggedSize 64))]
      let newTagAddr ← CodegenM.withFuncBuilder do
        FuncBuilder.gepi32 taggedTy (.local newStructPtr) #[0, 0]
      CodegenM.withFuncBuilder (FuncBuilder.store .i32 (.local tagVal) (.local newTagAddr))
      let newPayloadAddr ← CodegenM.withFuncBuilder do
        FuncBuilder.gepi32 taggedTy (.local newStructPtr) #[0, 1]
      CodegenM.withFuncBuilder (FuncBuilder.store .ptr (.local newPayload) (.local newPayloadAddr))
      CodegenM.withFuncBuilder (FuncBuilder.ret .ptr (.local newStructPtr))

      CodegenM.withFuncBuilder (FuncBuilder.startBlock doneLabel)
      CodegenM.withFuncBuilder (FuncBuilder.ret .ptr (.local valParam))

    | .closure _ _ =>
      -- Delegate to soma_clone_closure which reads env_size from _pad[1..2]
      -- and handles PAPs with arbitrary env sizes
      let cloned ← CodegenM.withFuncBuilder do
        FuncBuilder.callNamed .ptr "soma_clone_closure"
          #[(.ptr, .local valParam), (.i32, .local lblParam)]
      CodegenM.withFuncBuilder (FuncBuilder.ret .ptr (.local cloned))

    | .rawPtr =>
      CodegenM.withFuncBuilder (FuncBuilder.ret .ptr (.local valParam))

    | .struct fields =>
      -- Struct clone: allocate new struct, clone each field
      let llvmTy := convertTy ty
      let structVal ← CodegenM.withFuncBuilder (FuncBuilder.load llvmTy (.local valParam))
      let hasClonableFields := fields.any fun (_, ft) => ft.needsErase
      if hasClonableFields then
        let mut result := structVal
        for fi in [:fields.size] do
          let (_, fieldTy) := fields[fi]!
          if fieldTy.needsErase then
            let fieldLLVMTy := convertTy fieldTy
            let fieldVal ← CodegenM.withFuncBuilder do
              FuncBuilder.extractvalue llvmTy (.local result) #[fi]
            let fieldAsPtr ← ensurePtr fieldLLVMTy (.local fieldVal)
            let fieldClonerName ← getOrEmitCloner fieldTy
            let clonedPtr ← CodegenM.withFuncBuilder do
              FuncBuilder.callNamed .ptr fieldClonerName
                #[(.ptr, fieldAsPtr), (.i32, .local lblParam)]
            let clonedVal ← coerceValue .ptr fieldLLVMTy (.local clonedPtr)
            let newResult ← CodegenM.withFuncBuilder do
              FuncBuilder.insertvalue llvmTy (.local result) clonedVal #[fi]
            result := newResult
        -- Store updated struct and return pointer
        let structSizePtr ← CodegenM.withFuncBuilder do
          FuncBuilder.gepi32 llvmTy (.const .null) #[1]
        let structSizeI64 ← CodegenM.withFuncBuilder do
          FuncBuilder.ptrtoint .i64 (.local structSizePtr)
        let newPtr ← CodegenM.withFuncBuilder do
          FuncBuilder.callNamed .ptr "malloc" #[(.i64, .local structSizeI64)]
        CodegenM.withFuncBuilder (FuncBuilder.store llvmTy (.local result) (.local newPtr))
        CodegenM.withFuncBuilder (FuncBuilder.ret .ptr (.local newPtr))
      else
        -- All flat fields: identity clone
        CodegenM.withFuncBuilder (FuncBuilder.ret .ptr (.local valParam))

    | _ =>
      -- Flat types: identity clone
      CodegenM.withFuncBuilder (FuncBuilder.ret .ptr (.local valParam))

    let blocks ← CodegenM.withFuncBuilder FuncBuilder.getBlocks
    pure ({
      name := name
      retTy := .ptr
      params := #[{ name := "v0", ty := .ptr }, { name := "v1", ty := .i32 }]
      attrs := { nounwind := true }
      blocks := blocks
      isDeclaration := false
    } : LLVMFunc)

  CodegenM.withModuleBuilder (ModuleBuilder.addFunc clonerFunc)
  modify fun s => { s with funcState := savedFuncState }
  return name

/-- Get or emit a TypeDesc global for a given type -/
partial def getOrEmitTypeDesc (ty : ClosedTy) : CodegenM String := do
  let key := tyKey ty
  let s ← get
  if let some name := s.typeDescCache.get? key then
    return name

  -- Emit the clone and erase functions first
  let clonerName ← getOrEmitCloner ty
  let eraserName ← getOrEmitEraser ty

  let descName := s!"soma_typedesc${mangleTyName ty}"
  modify fun s => { s with typeDescCache := s.typeDescCache.insert key descName }

  -- Emit a constant global: { ptr @clone_fn, ptr @erase_fn }
  let typeDescTy : LLVMType := .struct false #[.ptr, .ptr]
  let typeDescGlobal : LLVMGlobal := {
    name := descName
    ty := typeDescTy
    init := some (.struct false #[(.ptr, .globalRef clonerName), (.ptr, .globalRef eraserName)])
    linkage := .private_
    isConstant := true
  }
  CodegenM.withModuleBuilder (ModuleBuilder.addGlobal typeDescGlobal)

  return descName

end

/-- Lower a direct function call -/
def lowerDirectCall (funcId : Nat) (args : Array Operand) (retTy : ClosedTy)
    : CodegenM (Option (LocalRef × ClosedTy)) := do
  let funcName ← CodegenM.getFuncName funcId
  let maybeSig ← CodegenM.getFuncSig funcId
  let actualRetTy := match maybeSig with
    | some sig => if retTy == .rawPtr && sig.retTy != .rawPtr then sig.retTy else retTy
    | none => retTy
  let llvmRetTy := convertTy actualRetTy
  let paramCount := match maybeSig with
    | some sig => sig.params.size
    | none => args.size
  -- Split args into direct params (up to function arity) and over-applied extras
  let directArgs := if args.size > paramCount then args.extract 0 paramCount else args
  let extraArgs := if args.size > paramCount then args.extract paramCount args.size else #[]
  let llvmArgs ← directArgs.mapIdxM fun i arg => do
    let argVal ← convertOperand arg
    let actualTy ← operandTy arg
    let actualLLVMTy := convertTy actualTy
    let expectedTy ← match maybeSig with
      | some sig =>
        if h : i < sig.params.size then pure sig.params[i].ty
        else pure actualTy
      | none => pure actualTy
    let expectedLLVMTy := convertTy expectedTy
    let coercedVal ← if actualLLVMTy == expectedLLVMTy then pure argVal
                      else coerceValue actualLLVMTy expectedLLVMTy argVal
    pure (expectedLLVMTy, coercedVal)
  -- Call function with its declared parameters
  let callRetTy := if extraArgs.isEmpty then llvmRetTy else .ptr
  let isTailCall := (← get).emitAsTailCall
  let mut ref ← CodegenM.withFuncBuilder do
    FuncBuilder.callNamed callRetTy funcName llvmArgs
      (tailcall := isTailCall) (callconv := some .fast)
  if isTailCall then modify fun s => { s with emitAsTailCall := false }
  -- Over-application: apply extra args via soma_apply to the returned closure
  for extraArg in extraArgs do
    let (extraArgTy, extraArgVal) ← convertOperandWithTy extraArg
    let argPtr ← if extraArgTy == .ptr then pure extraArgVal
                  else if extraArgTy.isInt then do
                    let converted ← CodegenM.withFuncBuilder (FuncBuilder.inttoptr extraArgTy extraArgVal)
                    pure (.local converted)
                  else pure extraArgVal
    ref ← CodegenM.withFuncBuilder do
      FuncBuilder.callNamed .ptr "soma_apply" #[(.ptr, .local ref), (.ptr, argPtr)]
  if !extraArgs.isEmpty then
    ref ← unboxApplyResult ref retTy
  pure (some (ref, actualRetTy))

/-- The composite env struct type: two i64 slots -/
def compositeEnvTy : LLVMType := .struct false #[.ptr, .ptr]

/-- Get or create a trampoline function for dynamic closures with the given arity -/
def getOrCreateTrampoline (arity : Nat) : CodegenM String := do
  let name := s!"soma_dyn_trampoline_{arity}"
  let s ← get
  if s.trampolineCache.contains name then
    return name
  let mut params : Array LLVMParam := #[{ name := "v0", ty := .ptr }]
  for i in List.range arity do
    params := params.push { name := s!"v{i + 1}", ty := .ptr }
  let trampolineFunc := buildFuncWithEntry name .ptr params {} do
    let compositeEnvRef := LocalRef.mk 0
    let innerSlotAddr ← FuncBuilder.gepi32 compositeEnvTy (.local compositeEnvRef) #[0, 0]
    let innerClosurePtr ← FuncBuilder.load .ptr (.local innerSlotAddr)
    -- Load outer_env from compositeEnv[1]
    let outerEnvSlotAddr ← FuncBuilder.gepi32 compositeEnvTy (.local compositeEnvRef) #[0, 1]
    let outerEnvPtr ← FuncBuilder.load .ptr (.local outerEnvSlotAddr)
    -- Headerless: func_ptr is field 2 of { i8, [7xi8], ptr }
    let fnPtrAddr ← FuncBuilder.gepi32 closureHeaderTy (.local innerClosurePtr) #[0, 2]
    let fnPtr ← FuncBuilder.load .ptr (.local fnPtrAddr)
    -- Headerless: env is at GEP index 1 past header struct
    let innerEnvAddr ← FuncBuilder.gepi32 closureHeaderTy (.local innerClosurePtr) #[1]
    let innerEnvPtr ← FuncBuilder.load .ptr (.local innerEnvAddr)
    let mut callArgs : Array (LLVMType × LLVMValue) :=
      #[(.ptr, .local innerEnvPtr), (.ptr, .local outerEnvPtr)]
    for i in List.range arity do
      callArgs := callArgs.push (.ptr, .local (LocalRef.mk (i + 1)))
    let result ← FuncBuilder.call .ptr (.local fnPtr) callArgs
    FuncBuilder.ret .ptr (.local result)
  -- Add the trampoline to the module
  CodegenM.withModuleBuilder (ModuleBuilder.addFunc trampolineFunc)
  modify fun s => { s with trampolineCache := s.trampolineCache.insert name name }
  return name

/-- Shared closure allocation logic for makeClosure and makeClosurePoly -/
private def emitMakeClosureImpl (funcRef : FuncRef) (env : Operand)
    : CodegenM (Option (LocalRef × ClosedTy)) := do
  let funcId := match funcRef with
    | .local id => id
    | _ => FuncId.mk 0
  let funcName ← CodegenM.getFuncName funcId.id
  let (envLLVMTy, envVal) ← convertOperandWithTy env
  let envAlloTy ← operandTy env
  -- Detect empty env (unit/erased)
  let isEmptyEnv := envAlloTy == .prim .unit
  let envFieldCount : Nat := if isEmptyEnv then 0
    else match envLLVMTy with
      | .struct _ fields => if fields.size > 1 then fields.size else 1
      | _ => 1
  let closureArity : Nat ← do
    match ← CodegenM.getFuncSig funcId.id with
    | some sig =>
      let n := sig.params.size
      pure (if isEmptyEnv then n else if n ≤ envFieldCount then 0 else n - envFieldCount)
    | none => pure 0
  let envSlotCount : Nat := if isEmptyEnv then 0 else envFieldCount
  let ps := (← get).ptrSize
  let closureHeaderSize := ps + ps
  let closureByteSize : Int := Int.ofNat (closureHeaderSize + envSlotCount * ps)
  let closurePtr ← CodegenM.withFuncBuilder do
    FuncBuilder.callNamed .ptr "soma_pool_alloc_raw" #[(.i64, .const (.int closureByteSize 64))]
  -- Store arity (field 0 of closureHeaderTy)
  let arityAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 0])
  CodegenM.withFuncBuilder (FuncBuilder.store .i8 (intVal (Int.ofNat closureArity) 8) (.local arityAddr))
  -- Store _pad[0] = NODE_CLOSURE sentinel for runtime identification
  let pad0Addr ← CodegenM.withFuncBuilder do
    FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 1, 0]
  CodegenM.withFuncBuilder (FuncBuilder.store .i8 (intVal nodeClosureTag 8) (.local pad0Addr))
  -- Store env_size in _pad[1..2] as little-endian u16
  let pad1Addr ← CodegenM.withFuncBuilder do
    FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 1, 1]
  CodegenM.withFuncBuilder (FuncBuilder.store .i8 (intVal (Int.ofNat (envSlotCount % 256)) 8) (.local pad1Addr))
  let pad2Addr ← CodegenM.withFuncBuilder do
    FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 1, 2]
  CodegenM.withFuncBuilder (FuncBuilder.store .i8 (intVal (Int.ofNat (envSlotCount / 256)) 8) (.local pad2Addr))
  -- Store func_ptr (field 2 of closureHeaderTy = the ptr field)
  let funcFieldAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 2])
  CodegenM.withFuncBuilder (FuncBuilder.store .ptr (globalVal funcName) (.local funcFieldAddr))
  -- Store env slots
  if !isEmptyEnv then
    if envFieldCount > 1 then
      -- Multi-field struct env: extract each field and store as separate slots
      match envLLVMTy with
      | .struct _ fields =>
        for fi in [:fields.size] do
          let fieldVal ← CodegenM.withFuncBuilder (FuncBuilder.extractvalue envLLVMTy envVal #[fi])
          let fieldPtrVal ← ensurePtr (fields[fi]!) (.local fieldVal)
          let slotAddr ← CodegenM.withFuncBuilder do
            FuncBuilder.gepi32 (.array envSlotCount .ptr) (.local closurePtr)
              #[if fi == 0 then 1 else (1 : Nat) + fi]
          CodegenM.withFuncBuilder (FuncBuilder.store .ptr fieldPtrVal (.local slotAddr))
      | _ =>
        -- Fallback: single slot
        let envPtrVal ← ensurePtr envLLVMTy envVal
        let envSlotAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[1])
        CodegenM.withFuncBuilder (FuncBuilder.store .ptr envPtrVal (.local envSlotAddr))
    else
      -- Single env slot
      let envPtrVal ← ensurePtr envLLVMTy envVal
      let envSlotAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[1])
      CodegenM.withFuncBuilder (FuncBuilder.store .ptr envPtrVal (.local envSlotAddr))
  let closureTyAlloy ← do
    match ← CodegenM.getFuncSig funcId.id with
    | some sig => pure (.closure (sig.params.map (·.ty)) sig.retTy)
    | none => pure (.closure #[] (.prim .i64))
  pure (some (closurePtr, closureTyAlloy))

/-- Lower an Alloy instruction to LLVM, returning result ref and result type -/
def lowerInst (inst : ClosedInst) : CodegenM (Option (LocalRef × ClosedTy)) := do
  match inst with
  | .binOp op lhs rhs ty =>
    let targetLlvmTy := convertTy ty
    let (lhsTy, lhsVal) ← convertOperandWithTy lhs
    let (rhsTy, rhsVal) ← convertOperandWithTy rhs
    -- Coerce operands to matching types when widths differ
    let lhsCoerced ← if lhsTy == targetLlvmTy then pure lhsVal
                      else coerceValue lhsTy targetLlvmTy lhsVal
    let rhsCoerced ← if rhsTy == targetLlvmTy then pure rhsVal
                      else coerceValue rhsTy targetLlvmTy rhsVal
    let ref ← convertBinOp op ty lhsCoerced rhsCoerced
    let resultTy := if op.isComparison then .prim .bool else ty
    pure (some (ref, resultTy))

  | .unOp op operand =>
    let srcTy ← operandTy operand
    let opVal ← convertOperand operand
    let ref ← convertUnOp op srcTy opVal
    let resultTy := match op with
      | .trunc t | .zext t | .sext t | .itof t | .ftoi t | .ptrtoint t => .prim t
      | .bitcast t => t
      | .inttoptr => .rawPtr
      | .neg | .not => srcTy
    pure (some (ref, resultTy))

  | .copy src =>
    match src with
    | .const (.undef ty) =>
      let llvmTy := convertTy ty
      let ref ← CodegenM.withFuncBuilder do
        if llvmTy == .ptr then
          FuncBuilder.asLocalRef .ptr (.const .null)
        else if llvmTy.isInt then
          FuncBuilder.add llvmTy (intVal 0 (llvmTy.intBits.getD 64)) (intVal 0 (llvmTy.intBits.getD 64))
        else do
          -- Aggregate types (structs, tagged unions): alloca + load to produce undef local
          let allocaRef ← FuncBuilder.emit (.alloca llvmTy none none)
          FuncBuilder.emit (.load llvmTy (.local allocaRef) none)
      pure (some (ref, ty))
    | .const (.string idx len) =>
      -- Fat pointer struct: build via insertvalue from undef
      let somaStrTy : LLVMType := .struct false #[.ptr, .i64]
      let staticBit : Int := Int.ofNat (1 <<< 63)
      let staticLen : Int := (Int.ofNat len) + staticBit
      let r1 ← CodegenM.withFuncBuilder
        (FuncBuilder.insertvalue somaStrTy (.const (.undef somaStrTy))
          (.global ⟨s!".str.{idx}"⟩) #[0])
      let r2 ← CodegenM.withFuncBuilder
        (FuncBuilder.insertvalue somaStrTy (.local r1)
          (.const (.int staticLen 64)) #[1])
      pure (some (r2, Ty.string))
    | _ =>
      let srcTy ← operandTy src
      let srcVal ← convertOperand src
      let llvmTy := convertTy srcTy
      -- For copies, we need to produce an SSA value
      match srcVal with
      | .local ref =>
        pure (some (ref, srcTy))
      | _ =>
        let ref ← CodegenM.withFuncBuilder do
          match srcVal with
          | .const .null =>
            FuncBuilder.asLocalRef .ptr (.const .null)
          | _ =>
            -- Materialize non-local values (constants, globals) as SSA values
            FuncBuilder.asLocalRef llvmTy srcVal
        pure (some (ref, srcTy))

  | .alloca ty =>
    let llvmTy := convertTy ty
    let ref ← CodegenM.withFuncBuilder (FuncBuilder.alloca llvmTy (some (← get).ptrSize))
    pure (some (ref, .ptr ty))

  | .malloc size =>
    let sizeVal ← convertOperand size
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.callNamed .ptr "malloc" #[(.i64, sizeVal)]
    pure (some (ref, .rawPtr))

  | .free ptr =>
    let ptrVal ← convertOperand ptr
    CodegenM.withFuncBuilder do
      FuncBuilder.callNamedVoid "free" #[(.ptr, ptrVal)]
    pure none

  | .load ptr ty =>
    let ptrVal ← convertOperand ptr
    let llvmTy := convertTy ty
    let ref ← CodegenM.withFuncBuilder (FuncBuilder.load llvmTy ptrVal)
    pure (some (ref, ty))

  | .store ptr val =>
    let ptrVal ← convertOperand ptr
    let valTy ← operandTy val
    let valVal ← convertOperand val
    let llvmValTy := convertTy valTy
    CodegenM.withFuncBuilder (FuncBuilder.store llvmValTy valVal ptrVal)
    pure none

  | .getFieldPtr base fieldIdx structTy =>
    let baseVal ← convertOperand base
    let llvmStructTy := convertTy structTy
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 llvmStructTy baseVal #[0, fieldIdx]
    let fieldTy := getStructFieldTy structTy fieldIdx
    pure (some (ref, .ptr fieldTy))

  | .getElemPtr base idx elemTy =>
    let baseVal ← convertOperand base
    let (idxLLVMTy, idxVal) ← convertOperandWithTy idx
    let llvmElemTy := convertTy elemTy
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.gep llvmElemTy baseVal #[(idxLLVMTy, idxVal)]
    pure (some (ref, .ptr elemTy))

  | .extractField val fieldIdx =>
    let valTy ← operandTy val
    let valRef ← convertOperand val
    let llvmValTy := convertTy valTy
    let fieldTy := getStructFieldTy valTy fieldIdx
    let llvmFieldTy := convertTy fieldTy
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.extractvalue llvmValTy valRef #[fieldIdx]
    pure (some (ref, fieldTy))

  | .insertField val fieldIdx newVal =>
    let valTy ← operandTy val
    let valRef ← convertOperand val
    let llvmValTy := convertTy valTy
    let newValRef ← convertOperand newVal
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.insertvalue llvmValTy valRef newValRef #[fieldIdx]
    pure (some (ref, valTy))

  | .extractElem val idx =>
    let valTy ← operandTy val
    let elemTy := getArrayElemTy valTy
    let valRef ← convertOperand val
    let (idxLLVMTy, idxVal) ← convertOperandWithTy idx
    let llvmElemTy := convertTy elemTy
    -- Array element extraction via GEP + load
    let elemPtr ← CodegenM.withFuncBuilder do
      FuncBuilder.gep llvmElemTy valRef #[(idxLLVMTy, idxVal)]
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.load llvmElemTy (.local elemPtr)
    pure (some (ref, elemTy))

  | .insertElem val idx newVal =>
    let valTy ← operandTy val
    let elemTy := getArrayElemTy valTy
    let valRef ← convertOperand val
    let (idxLLVMTy, idxVal) ← convertOperandWithTy idx
    let newValRef ← convertOperand newVal
    let llvmElemTy := convertTy elemTy
    -- Array element insertion via GEP + store
    let elemPtr ← CodegenM.withFuncBuilder do
      FuncBuilder.gep llvmElemTy valRef #[(idxLLVMTy, idxVal)]
    CodegenM.withFuncBuilder do
      FuncBuilder.store llvmElemTy newValRef (.local elemPtr)
    -- Return original array (in-place mutation semantics)
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.bitcast .ptr .ptr valRef
    pure (some (ref, valTy))

  | .structLit fields ty =>
    let llvmTy := convertTy ty
    -- Build struct via insertvalue chain (pure register ops, no memory round-trip)
    let mut agg : LLVMValue := .const (.undef llvmTy)
    for i in [:fields.size] do
      if h : i < fields.size then
        let fieldOp := fields[i]
        let (_, fieldVal) ← convertOperandWithTy fieldOp
        let ref ← CodegenM.withFuncBuilder do
          FuncBuilder.insertvalue llvmTy agg fieldVal #[i]
        agg := .local ref
    let finalRef ← match agg with
      | .local r => pure r
      | _ => CodegenM.withFuncBuilder (FuncBuilder.asLocalRef llvmTy agg)
    pure (some (finalRef, ty))

  | .arrayLit elems elemTy =>
    let llvmElemTy := convertTy elemTy
    let arrayTy := LLVMType.array elems.size llvmElemTy
    let arrayPtr ← CodegenM.withFuncBuilder (FuncBuilder.alloca arrayTy)
    for i in [:elems.size] do
      if h : i < elems.size then
        let elemOp := elems[i]
        let elemVal ← convertOperand elemOp
        let elemPtr ← CodegenM.withFuncBuilder do
          FuncBuilder.gepi32 arrayTy (.local arrayPtr) #[0, i]
        CodegenM.withFuncBuilder do
          FuncBuilder.store llvmElemTy elemVal (.local elemPtr)
    let resultTy := Ty.array elemTy elems.size
    pure (some (arrayPtr, resultTy))

  | .getTag val =>
    let valTy ← operandTy val
    let valRef ← convertOperand val
    let llvmValTy := convertTy valTy
    -- Handle based on Alloy type to determine the proper extraction strategy
    match valTy with
    | .tagged _ _ =>
      -- Tagged union by value: extract the tag (field 0) directly from { i32, ptr }
      let ref ← CodegenM.withFuncBuilder do
        FuncBuilder.extractvalue llvmValTy valRef #[0]
      pure (some (ref, .prim .u32))
    | .rawPtr | .ptr _ =>
      -- Pointer to tagged union in memory: GEP to tag field + load
      let tagPtr ← CodegenM.withFuncBuilder do
        FuncBuilder.gepi32 taggedTy valRef #[0, 0]
      let ref ← CodegenM.withFuncBuilder do
        FuncBuilder.load .i32 (.local tagPtr)
      pure (some (ref, .prim .u32))
    | .struct fields =>
      -- Struct: check if first field is a tagged union
      match fields[0]? with
      | some (_, Ty.tagged _ _) =>
        let innerRef ← CodegenM.withFuncBuilder do
          FuncBuilder.extractvalue llvmValTy valRef #[0]
        let ref ← CodegenM.withFuncBuilder do
          FuncBuilder.extractvalue taggedTy (.local innerRef) #[0]
        pure (some (ref, .prim .u32))
      | _ =>
        panic! s!"CODEGEN BUG: getTag on plain struct {valTy} — single-constructor records should be optimized out at the Alloy level"
    | .prim .bool =>
      -- Bool: zext i1 to i32
      let ref ← CodegenM.withFuncBuilder do
        FuncBuilder.zext .i1 .i32 valRef
      pure (some (ref, .prim .u32))
    | _ =>
      match llvmValTy with
      | .i32 =>
        -- Already i32
        let ref ← CodegenM.withFuncBuilder do
          FuncBuilder.asLocalRef .i32 valRef
        pure (some (ref, .prim .u32))
      | .i1 | .i8 | .i16 =>
        -- Small integer type, zext to i32
        let ref ← CodegenM.withFuncBuilder do
          FuncBuilder.zext llvmValTy .i32 valRef
        pure (some (ref, .prim .u32))
      | .struct _ _ =>
        -- Struct type, extract first field as tag
        let ref ← CodegenM.withFuncBuilder do
          FuncBuilder.extractvalue llvmValTy valRef #[0]
        pure (some (ref, .prim .u32))
      | _ =>
        -- Unknown type, assume tagged union and extract tag
        let ref ← CodegenM.withFuncBuilder do
          FuncBuilder.extractvalue taggedTy valRef #[0]
        pure (some (ref, .prim .u32))

  | .getPayload val variantIdx fieldIdx resultTy =>
    let valTy ← operandTy val
    let valRef ← convertOperand val
    let llvmValTy := convertTy valTy
    let llvmResultTy := convertTy resultTy
    match valTy with
    | .struct _ =>
      panic! s!"CODEGEN BUG: getPayload on struct {valTy} — should use extractField via PROJ optimization"
    | .prim .unit =>
      panic! s!"CODEGEN BUG: getPayload on unit — should be eliminated by single-constructor MAT optimization"
    | _ =>
    -- Tagged union: extract payload pointer first
    let payloadPtr ← match valTy with
        | .rawPtr | .ptr _ =>
          -- Pointer to tagged union: GEP to payload field (index 1) + load
          let payloadSlot ← CodegenM.withFuncBuilder do
            FuncBuilder.gepi32 taggedTy valRef #[0, 1]
          CodegenM.withFuncBuilder do
            FuncBuilder.load .ptr (.local payloadSlot)
        | _ =>
          -- By-value tagged union: extractvalue to get payload pointer
          CodegenM.withFuncBuilder do
            FuncBuilder.extractvalue llvmValTy valRef #[1]
      -- Natural-size payload: GEP into typed struct for this variant
      let variantFieldTypes? := match valTy with
        | .tagged _ variants =>
          match variants.find? (fun (idx, _) => idx == variantIdx) with
          | some (_, fields) => if fields.isEmpty then none else some fields
          | none => none
        | _ => none
      match variantFieldTypes? with
      | some fields =>
        let layout := computePackedLayout fields (← get).ptrSize
        let physIdx := layout.logToPhys.getD fieldIdx fieldIdx
        let fieldPtr ← CodegenM.withFuncBuilder do
          FuncBuilder.gepi32 layout.llvmTy (.local payloadPtr) #[0, physIdx]
        let ref ← CodegenM.withFuncBuilder do
          FuncBuilder.load llvmResultTy (.local fieldPtr)
        pure (some (ref, resultTy))
      | none =>
        panic! s!"CODEGEN BUG: field access on unknown variant {variantIdx} of {valTy}"

  | .taggedLit tag payload ty =>
    let taggedPtr ← CodegenM.withFuncBuilder (FuncBuilder.alloca taggedTy)
    -- Store tag
    let tagPtr ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 taggedTy (.local taggedPtr) #[0, 0]
    CodegenM.withFuncBuilder do
      FuncBuilder.store .i32 (i32Val tag) (.local tagPtr)
    -- Allocate and store payload if non-empty
    if payload.size > 0 then
      let fieldTypes ← payload.mapM fun op => operandTy op
      let layout := computePackedLayout fieldTypes (← get).ptrSize
      let payloadBytes : Int := Int.ofNat layout.byteSize
      let payloadMem ← CodegenM.withFuncBuilder do
        FuncBuilder.callNamed .ptr "soma_pool_alloc_raw" #[(.i64, .const (.int payloadBytes 64))]
      for i in [:payload.size] do
        if h : i < payload.size then
          let fieldOp := payload[i]
          let (fieldLLVMTy, fieldVal) ← convertOperandWithTy fieldOp
          let physIdx := layout.logToPhys.getD i i
          let fieldPtr ← CodegenM.withFuncBuilder do
            FuncBuilder.gepi32 layout.llvmTy (.local payloadMem) #[0, physIdx]
          CodegenM.withFuncBuilder do
            FuncBuilder.store fieldLLVMTy fieldVal (.local fieldPtr)
      let payloadPtrSlot ← CodegenM.withFuncBuilder do
        FuncBuilder.gepi32 taggedTy (.local taggedPtr) #[0, 1]
      CodegenM.withFuncBuilder do
        FuncBuilder.store .ptr (.local payloadMem) (.local payloadPtrSlot)
    else
      -- Store null for empty payload
      let payloadPtrSlot ← CodegenM.withFuncBuilder do
        FuncBuilder.gepi32 taggedTy (.local taggedPtr) #[0, 1]
      CodegenM.withFuncBuilder do
        FuncBuilder.store .ptr nullVal (.local payloadPtrSlot)
    let ref ← CodegenM.withFuncBuilder (FuncBuilder.load taggedTy (.local taggedPtr))
    pure (some (ref, ty))

  | .reuseTaggedLit tag payload reuseOp ty =>
    let reusePtr ← convertOperand reuseOp
    let fieldTypes ← payload.mapM fun op => operandTy op
    let layout := computePackedLayout fieldTypes (← get).ptrSize
    for i in [:payload.size] do
      if h : i < payload.size then
        let fieldOp := payload[i]
        let (fieldLLVMTy, fieldVal) ← convertOperandWithTy fieldOp
        let physIdx := layout.logToPhys.getD i i
        let fieldPtr ← CodegenM.withFuncBuilder do
          FuncBuilder.gepi32 layout.llvmTy reusePtr #[0, physIdx]
        CodegenM.withFuncBuilder do
          FuncBuilder.store fieldLLVMTy fieldVal (.local fieldPtr)
    -- Build the result struct {tag, reusePtr} on the stack
    let taggedPtr ← CodegenM.withFuncBuilder (FuncBuilder.alloca taggedTy)
    let tagPtr ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 taggedTy (.local taggedPtr) #[0, 0]
    CodegenM.withFuncBuilder do
      FuncBuilder.store .i32 (i32Val tag) (.local tagPtr)
    let payloadPtrSlot ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 taggedTy (.local taggedPtr) #[0, 1]
    CodegenM.withFuncBuilder do
      FuncBuilder.store .ptr reusePtr (.local payloadPtrSlot)
    let ref ← CodegenM.withFuncBuilder (FuncBuilder.load taggedTy (.local taggedPtr))
    pure (some (ref, ty))

  | .call func args retTy =>
    lowerDirectCall func.id args retTy

  | .callPoly func _typeArgs args retTy =>
    lowerDirectCall func.id args retTy

  | .callIndirect ptr args retTy =>
    let ptrVal ← convertOperand ptr
    let llvmRetTy := convertTy retTy
    let llvmArgs ← args.mapM fun arg => convertOperandWithTy arg
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.call llvmRetTy ptrVal llvmArgs
    pure (some (ref, retTy))

  | .callClosure closure args retTy =>
    let closureTyAlloy ← operandTy closure
    let closureLLVMTy := convertTy closureTyAlloy
    -- Check if closure operand is actually a closure type (not unit from ERA)
    if closureLLVMTy != closureTy then
      -- Not a real closure — unreachable at runtime. Emit panic + signal noreturn
      -- so that lowerBlock stops emitting dead code after this instruction.
      let panicName := (← get).panicStrName
      CodegenM.withFuncBuilder do
        FuncBuilder.callNamedVoid "soma_panic" #[(.ptr, globalVal panicName)]
      CodegenM.signalNoReturn
      pure none
    else
      -- Use soma_apply for closure calls to handle partial application (PAP), variable env sizes, and proper argument accumulation
      let closureVal ← convertOperand closure
      let argVal ← match args[0]? with
        | some arg => do
          let (argLLVMTy, argV) ← convertOperandWithTy arg
          if argLLVMTy == .ptr then pure argV
          else if argLLVMTy.isInt then do
            let converted ← CodegenM.withFuncBuilder (FuncBuilder.inttoptr argLLVMTy argV)
            pure (.local converted)
          else do
            -- Coerce aggregate to ptr via alloca+store
            let slot ← CodegenM.withFuncBuilder (FuncBuilder.alloca argLLVMTy)
            CodegenM.withFuncBuilder (FuncBuilder.store argLLVMTy argV (.local slot))
            pure (.local slot)
        | none => pure (.const .null)
      -- Coerce closure to ptr if needed
      let closurePtr ← do
        let closureLLVMTy := convertTy closureTyAlloy
        if closureLLVMTy == .ptr then pure closureVal
        else if closureLLVMTy.isInt then do
          let ref ← CodegenM.withFuncBuilder (FuncBuilder.inttoptr closureLLVMTy closureVal)
          pure (.local ref)
        else pure closureVal
      let ref ← CodegenM.withFuncBuilder do
        FuncBuilder.callNamed .ptr "soma_apply" #[(.ptr, closurePtr), (.ptr, argVal)]
      let ref ← unboxApplyResult ref retTy
      pure (some (ref, retTy))

  | .makeClosure funcRef env => emitMakeClosureImpl funcRef env
  | .makeClosurePoly funcRef _typeArgs env => emitMakeClosureImpl funcRef env

  | .makeClosureDyn fnClosure env resultTy =>
    -- The trampoline unpacks both from a composite env buffer and forwards the call
    let (fnClosureLLVMTy, fnClosureRaw) ← convertOperandWithTy fnClosure
    let fnClosureVal ← if fnClosureLLVMTy == .ptr then pure fnClosureRaw
      else coerceValue fnClosureLLVMTy .ptr fnClosureRaw
    let (envLLVMTy, envVal) ← convertOperandWithTy env
    let closureArity : Nat := match resultTy with
      | .closure argTys _ => argTys.size
      | _ => 0
    let trampolineName ← getOrCreateTrampoline closureArity
    let ps := (← get).ptrSize
    let compositeSize : Int := Int.ofNat (ps * 2)
    let compositeBuf ← CodegenM.withFuncBuilder do
      FuncBuilder.callNamed .ptr "malloc" #[(.i64, .const (.int compositeSize 64))]
    CodegenM.withFuncBuilder (FuncBuilder.store .ptr fnClosureVal (.local compositeBuf))
    let envSlotAddr ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 compositeEnvTy (.local compositeBuf) #[0, 1]
    let envAsPtr ← ensurePtr envLLVMTy envVal
    CodegenM.withFuncBuilder (FuncBuilder.store .ptr envAsPtr (.local envSlotAddr))
    -- Headerless closure: { i8 arity, [7xi8] pad, ptr func_ptr, i64 env }
    let closureHeaderSize := ps + ps
    let closureByteSize : Int := Int.ofNat (closureHeaderSize + ps)
    let closurePtr ← CodegenM.withFuncBuilder do
      FuncBuilder.callNamed .ptr "soma_pool_alloc_raw" #[(.i64, .const (.int closureByteSize 64))]
    -- Store arity
    let arityAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 0])
    CodegenM.withFuncBuilder (FuncBuilder.store .i8 (intVal (Int.ofNat closureArity) 8) (.local arityAddr))
    -- Store _pad[0] = NODE_CLOSURE sentinel
    let dynPad0Addr ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 1, 0]
    CodegenM.withFuncBuilder (FuncBuilder.store .i8 (intVal nodeClosureTag 8) (.local dynPad0Addr))
    -- Store env_size=1 in _pad[1..2]
    let dynPad1Addr ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 1, 1]
    CodegenM.withFuncBuilder (FuncBuilder.store .i8 (intVal 1 8) (.local dynPad1Addr))
    let dynPad2Addr ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 1, 2]
    CodegenM.withFuncBuilder (FuncBuilder.store .i8 (intVal 0 8) (.local dynPad2Addr))
    -- Store trampoline as the function pointer (field 2 = ptr in headerless layout)
    let funcFieldAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 2])
    CodegenM.withFuncBuilder (FuncBuilder.store .ptr (globalVal trampolineName) (.local funcFieldAddr))
    let closureEnvSlotAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[1])
    CodegenM.withFuncBuilder (FuncBuilder.store .ptr (.local compositeBuf) (.local closureEnvSlotAddr))
    pure (some (closurePtr, resultTy))

  | .closureFunc closure =>
    let closureVal ← convertOperand closure
    -- Headerless: func_ptr is field 2 of { i8, [7xi8], ptr }
    let funcPtrAddr ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 closureHeaderTy closureVal #[0, 2]
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.load .ptr (.local funcPtrAddr)
    pure (some (ref, .rawPtr))

  | .closureEnv closure =>
    let closureVal ← convertOperand closure
    -- Headerless: env is at GEP index 1 past the header struct
    let envBaseAddr ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 closureHeaderTy closureVal #[1]
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.load .ptr (.local envBaseAddr)
    pure (some (ref, .rawPtr))

  | .phi incoming ty =>
    let llvmTy := convertTy ty
    -- Filter out predecessors from dead blocks
    let liveIncoming ← incoming.filterM fun (_, blockId) => do
      let isDead ← CodegenM.isBlockDead blockId.id
      pure !isDead
    -- For each incoming value, check its ground-truth LLVM type
    let llvmIncoming ← liveIncoming.mapM fun (val, blockId) => do
      let label ← CodegenM.getOrCreateBlock blockId.id
      let (valTy, valLlvm) ← convertOperandWithTy val
      if valTy == llvmTy then
        pure (valLlvm, label)
      else
        -- Insert coercion in the predecessor block
        let coercedRef ← CodegenM.withFuncBuilder do
          if llvmTy == .ptr && valTy.isInt then
            FuncBuilder.insertInBlock label (.inttoptr valTy .ptr valLlvm)
          else if llvmTy.isInt && valTy == .ptr then
            FuncBuilder.insertInBlock label (.ptrtoint .ptr llvmTy valLlvm)
          else if llvmTy.isInt && valTy.isInt then
            let srcBits := valTy.intBits.getD 64
            let dstBits := llvmTy.intBits.getD 64
            if srcBits < dstBits then
              FuncBuilder.insertInBlock label (.zext valTy llvmTy valLlvm)
            else
              FuncBuilder.insertInBlock label (.trunc valTy llvmTy valLlvm)
          else if valTy == .ptr then
            -- ptr → aggregate: load the aggregate from the pointer
            FuncBuilder.insertInBlock label (.load llvmTy valLlvm none)
          else if llvmTy == .ptr then
            -- aggregate → ptr: alloca in entry block (stack safety), store+load in predecessor
            let allocaRef ← FuncBuilder.insertInEntryBlock (.alloca valTy none none)
            FuncBuilder.insertVoidInBlock label (.store valTy valLlvm (.local allocaRef) none)
            pure allocaRef
          else
            -- Mismatched non-ptr types: bitcast through alloca in entry block
            let allocaRef ← FuncBuilder.insertInEntryBlock (.alloca valTy none none)
            FuncBuilder.insertVoidInBlock label (.store valTy valLlvm (.local allocaRef) none)
            FuncBuilder.insertInBlock label (.load llvmTy (.local allocaRef) none)
        pure (.local coercedRef, label)
    -- If all predecessors are dead, this block is itself unreachable
    if llvmIncoming.size == 0 then
      let ref ← CodegenM.withFuncBuilder do
        if llvmTy == .ptr then FuncBuilder.asLocalRef .ptr (.const .null)
        else if llvmTy.isInt then FuncBuilder.add llvmTy (intVal 0 (llvmTy.intBits.getD 64)) (intVal 0 (llvmTy.intBits.getD 64))
        else do
          -- Dead block with aggregate type: alloca + load undef
          let allocaRef ← FuncBuilder.emit (.alloca llvmTy none none)
          FuncBuilder.emit (.load llvmTy (.local allocaRef) none)
      pure (some (ref, ty))
    else if llvmIncoming.size == 1 then
      let (val, _) := llvmIncoming[0]!
      match val with
      | .local r => pure (some (r, ty))
      | _ =>
        -- Constants need to be materialized
        let ref ← CodegenM.withFuncBuilder (FuncBuilder.phi llvmTy llvmIncoming)
        pure (some (ref, ty))
    else
      let ref ← CodegenM.withFuncBuilder (FuncBuilder.phi llvmTy llvmIncoming)
      pure (some (ref, ty))

  | .select cond thenVal elseVal =>
    let condVal ← convertOperand cond
    let thenTy ← operandTy thenVal
    let thenRef ← convertOperand thenVal
    let elseRef ← convertOperand elseVal
    let llvmTy := convertTy thenTy
    let ref ← CodegenM.withFuncBuilder (FuncBuilder.select llvmTy condVal thenRef elseRef)
    pure (some (ref, thenTy))

  | .memcpy dst src size =>
    let dstVal ← convertOperand dst
    let srcVal ← convertOperand src
    let sizeVal ← convertOperand size
    CodegenM.withFuncBuilder (FuncBuilder.memcpy dstVal srcVal sizeVal)
    pure none

  | .memset dst val size =>
    let dstVal ← convertOperand dst
    let valVal ← convertOperand val
    let sizeVal ← convertOperand size
    CodegenM.withFuncBuilder (FuncBuilder.memset dstVal valVal sizeVal)
    pure none

  | .lazySup label src ty =>
    -- Create a SUP node with a type descriptor for specialized clone/erase
    let srcVal ← convertOperand src
    let srcLlvmTy := convertTy (← operandTy src)
    let srcAsI64 ← toI64 srcLlvmTy srcVal
    -- Emit the TypeDesc global (contains clone_fn + erase_fn pointers)
    let typeDescName ← getOrEmitTypeDesc ty
    let typeDescPtr ← CodegenM.withFuncBuilder do
      FuncBuilder.asLocalRef .ptr (globalVal typeDescName)
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.callNamed .i64 "soma_dup_typed"
        #[(.i32, i32Val label.toNat), (.i64, .local srcAsI64),
          (.ptr, .local typeDescPtr)]
    pure (some (ref, .prim .i64))

  | .supProj0 src ty =>
    -- Project from SUP: soma_proj0(sup_i64) → i64, then convert to target type
    let srcVal ← convertOperand src
    -- src is i64 from lazySup; operandTy correctly reports i64
    let rawRef ← CodegenM.withFuncBuilder do
      FuncBuilder.callNamed .i64 "soma_proj0" #[(.i64, srcVal)]
    let targetLlvmTy := convertTy ty
    let ref ← fromI64 targetLlvmTy (.local rawRef)
    pure (some (ref, ty))

  | .supProj1 src ty =>
    -- Project from SUP: soma_proj1(sup_i64) → i64, then convert to target type
    let srcVal ← convertOperand src
    let rawRef ← CodegenM.withFuncBuilder do
      FuncBuilder.callNamed .i64 "soma_proj1" #[(.i64, srcVal)]
    let targetLlvmTy := convertTy ty
    let ref ← fromI64 targetLlvmTy (.local rawRef)
    pure (some (ref, ty))

  | .erase val ty =>
    if isUnitTy ty || !ty.needsErase then
      pure none
    else
      let valRef ← convertOperand val
      emitEraseForType valRef ty
      pure none

  | .clone val ty label =>
    let valRef ← convertOperand val
    let valLlvmTy := convertTy (← operandTy val)
    let valAsPtr ← ensurePtr valLlvmTy valRef
    let clonerName ← getOrEmitCloner ty
    let clonedPtr ← CodegenM.withFuncBuilder do
      FuncBuilder.callNamed .ptr clonerName
        #[(.ptr, valAsPtr), (.i32, i32Val label.toNat)]
    let targetLlvmTy := convertTy ty
    let resultRef ← coerceValue .ptr targetLlvmTy (.local clonedPtr)
    match resultRef with
    | .local ref => pure (some (ref, ty))
    | _ =>
      let ref ← CodegenM.withFuncBuilder (FuncBuilder.asLocalRef targetLlvmTy resultRef)
      pure (some (ref, ty))

  | .panic msgIdx line =>
    let _ := line
    CodegenM.withFuncBuilder do
      FuncBuilder.callNamedVoid "soma_panic" #[(.ptr, globalVal s!".str.{msgIdx}")]
    CodegenM.signalNoReturn
    pure none


  | .callIntrinsic op args retTy =>
    -- FFI intrinsic operations compile to inline LLVM instructions
    let llvmArgs ← args.mapM fun arg => convertOperandWithTy arg
    let llvmRetTy := convertTy retTy
    match op with
    | .ptrNull =>
      -- Null pointer constant
      let ref ← CodegenM.withFuncBuilder (FuncBuilder.bitcast .ptr .ptr nullVal)
      pure (some (ref, .rawPtr))

    | .ptrRead =>
      -- Load from pointer: ptr_read ptr -> value
      if llvmArgs.size > 0 then
        let (ptrTy, ptrVal) := llvmArgs[0]!
        -- Ensure the argument is actually a pointer (handle i64 undefs from dead code)
        let ptrVal' ← ensurePtr ptrTy ptrVal
        let ref ← CodegenM.withFuncBuilder (FuncBuilder.load llvmRetTy ptrVal')
        pure (some (ref, retTy))
      else
        pure none

    | .ptrWrite =>
      -- Store to pointer: ptr_write ptr val -> Unit
      if llvmArgs.size >= 2 then
        let (ptrTy, ptrVal) := llvmArgs[0]!
        let (valTy, valVal) := llvmArgs[1]!
        -- Ensure the argument is actually a pointer (handle i64 undefs from dead code)
        let ptrVal' ← ensurePtr ptrTy ptrVal
        CodegenM.withFuncBuilder (FuncBuilder.store valTy valVal ptrVal')
      pure none

    | .ptrAdd =>
      -- Pointer arithmetic: ptr_add ptr offset -> ptr
      if llvmArgs.size >= 2 then
        let (ptrTy, ptrVal) := llvmArgs[0]!
        let (offsetTy, offsetVal) := llvmArgs[1]!
        -- Ensure the argument is actually a pointer (handle i64 undefs from dead code)
        let ptrVal' ← ensurePtr ptrTy ptrVal
        -- GEP with byte offset (treat as i8*)
        let ref ← CodegenM.withFuncBuilder (FuncBuilder.gep .i8 ptrVal' #[(offsetTy, offsetVal)])
        pure (some (ref, .rawPtr))
      else
        pure none

    | .ptrDiff =>
      -- Pointer difference: ptr_diff ptr1 ptr2 -> i64
      if llvmArgs.size >= 2 then
        let (ty1, val1) := llvmArgs[0]!
        let (ty2, val2) := llvmArgs[1]!
        -- Convert both values to i64
        let i1 ← toI64 ty1 val1
        let i2 ← toI64 ty2 val2
        let ref ← CodegenM.withFuncBuilder (FuncBuilder.sub .i64 (.local i1) (.local i2))
        pure (some (ref, .prim .i64))
      else
        pure none

    | .ptrCast =>
      -- Pointer cast: just return the pointer (LLVM opaque pointers)
      if llvmArgs.size > 0 then
        let (ptrTy, ptrVal) := llvmArgs[0]!
        -- Ensure the argument is actually a pointer (handle i64 undefs from dead code)
        let ptrVal' ← ensurePtr ptrTy ptrVal
        let ref ← CodegenM.withFuncBuilder (FuncBuilder.bitcast .ptr .ptr ptrVal')
        pure (some (ref, .rawPtr))
      else
        pure none

    | .toCString =>
      -- Fat pointer string: extract field 0 (data pointer)
      if llvmArgs.size > 0 then
        let (strTy, strVal) := llvmArgs[0]!
        let ref ← CodegenM.withFuncBuilder (FuncBuilder.extractvalue strTy strVal #[0])
        pure (some (ref, .rawPtr))
      else
        pure none

    | .fromCString =>
      let strConsts ← do pure (← get).stringConstLocals
      let staticIdx? : Option Nat := match args[0]? with
        | some (Operand.const (Const.string idx _)) => some idx
        | some (Operand.local localId) => strConsts.get? localId.id
        | _ => none
      let somaStrTy : LLVMType := .struct false #[.ptr, .i64]
      match staticIdx? with
      | some idx =>
        -- Static string: look up length from string table and construct fat pointer inline
        let strTable := (← get).stringTable
        let len := if h : idx < strTable.size then strTable[idx].utf8ByteSize else 0
        let staticBit : Int := Int.ofNat (1 <<< 63)
        let staticLen : Int := (Int.ofNat len) + staticBit
        -- Build struct via insertvalue from undef (LLVM cannot bitcast struct constants)
        let r1 ← CodegenM.withFuncBuilder
          (FuncBuilder.insertvalue somaStrTy (.const (.undef somaStrTy))
            (.global ⟨s!".str.{idx}"⟩) #[0])
        let r2 ← CodegenM.withFuncBuilder
          (FuncBuilder.insertvalue somaStrTy (.local r1)
            (.const (.int staticLen 64)) #[1])
        pure (some (r2, Ty.string))
      | none =>
        -- Dynamic path: call soma_from_cstring which returns { ptr, i64 }
        let ref ← callCFuncStructABI somaStringLLVMTy "soma_from_cstring" llvmArgs
        pure (some (ref, Ty.string))

    | .cstringLen =>
      -- Removed: soma_cstring_len no longer exists in runtime
      pure none

    | .strcat =>
      -- String concatenation: struct args and struct return
      let ref ← callCFuncStructABI somaStringLLVMTy "soma_strcat" llvmArgs
      pure (some (ref, Ty.string))

    | .intToString =>
      -- Int to string: returns fat pointer struct
      let ref ← callCFuncStructABI somaStringLLVMTy "soma_int_to_string" llvmArgs
      pure (some (ref, Ty.string))


  | .callExtern name args retTy =>
    -- External function call: emit regular LLVM call to @name
    let llvmRetTy := convertTy retTy

    -- TODO: review workaround
    let isSomaRuntime := name.startsWith "soma_"
    let mut llvmArgs : Array (LLVMType × LLVMValue) := #[]
    for arg in args do
      let argAlloTy ← operandTy arg
      let (argLLVMTy, argVal) ← convertOperandWithTy arg
      if argAlloTy == Ty.string && !isSomaRuntime then
        -- Fat pointer → C string: extract data pointer (field 0)
        let cstr ← CodegenM.withFuncBuilder
          (FuncBuilder.extractvalue argLLVMTy argVal #[0])
        llvmArgs := llvmArgs.push (.ptr, .local cstr)
      else
        llvmArgs := llvmArgs.push (argLLVMTy, argVal)

    -- Check if any arg or return type is a struct (needs ABI handling)
    let hasStructTypes := llvmRetTy.isStruct || llvmArgs.any fun (ty, _) => ty.isStruct

    -- Declare the extern function if not already declared
    unless (← CodegenM.isExternDeclared name) do
      if !(hasStructTypes && isSomaRuntime) then
        let llvmParams := llvmArgs.mapIdx fun i (ty, _) =>
          { name := s!"arg{i}", ty := ty : LLVMParam }
        CodegenM.withModuleBuilder do
          ModuleBuilder.addFunc {
            name := name
            retTy := llvmRetTy
            params := llvmParams
            isDeclaration := true
          }
        CodegenM.markExternDeclared name

    if hasStructTypes && isSomaRuntime then
      if isUnitTy retTy || llvmRetTy == .void then
        callCFuncStructABIVoid name llvmArgs
        let unitRef ← CodegenM.withFuncBuilder (FuncBuilder.asLocalRef .i8 (intVal 0 8))
        pure (some (unitRef, retTy))
      else
        let ref ← callCFuncStructABI llvmRetTy name llvmArgs
        pure (some (ref, retTy))
    else
      let ref ← CodegenM.withFuncBuilder (FuncBuilder.callNamed llvmRetTy name llvmArgs)
      if isUnitTy retTy then
        let unitRef ← CodegenM.withFuncBuilder (FuncBuilder.asLocalRef .i8 (intVal 0 8))
        pure (some (unitRef, retTy))
      else
        pure (some (ref, retTy))

  | .callExternPoly name _typeArgs args retTy =>
    let llvmRetTy := convertTy retTy

    let isSomaRuntime := name.startsWith "soma_"
    let mut llvmArgs : Array (LLVMType × LLVMValue) := #[]
    for arg in args do
      let argAlloTy ← operandTy arg
      let (argLLVMTy, argVal) ← convertOperandWithTy arg
      if argAlloTy == Ty.string && !isSomaRuntime then
        let cstr ← CodegenM.withFuncBuilder
          (FuncBuilder.extractvalue argLLVMTy argVal #[0])
        llvmArgs := llvmArgs.push (.ptr, .local cstr)
      else
        llvmArgs := llvmArgs.push (argLLVMTy, argVal)

    let hasStructTypes := llvmRetTy.isStruct || llvmArgs.any fun (ty, _) => ty.isStruct

    unless (← CodegenM.isExternDeclared name) do
      if !(hasStructTypes && isSomaRuntime) then
        let llvmParams := llvmArgs.mapIdx fun i (ty, _) =>
          { name := s!"arg{i}", ty := ty : LLVMParam }
        CodegenM.withModuleBuilder do
          ModuleBuilder.addFunc {
            name := name
            retTy := llvmRetTy
            params := llvmParams
            isDeclaration := true
          }
        CodegenM.markExternDeclared name

    if hasStructTypes && isSomaRuntime then
      if isUnitTy retTy || llvmRetTy == .void then
        callCFuncStructABIVoid name llvmArgs
        let unitRef ← CodegenM.withFuncBuilder (FuncBuilder.asLocalRef .i8 (intVal 0 8))
        pure (some (unitRef, retTy))
      else
        let ref ← callCFuncStructABI llvmRetTy name llvmArgs
        pure (some (ref, retTy))
    else
      let ref ← CodegenM.withFuncBuilder (FuncBuilder.callNamed llvmRetTy name llvmArgs)
      if isUnitTy retTy then
        let unitRef ← CodegenM.withFuncBuilder (FuncBuilder.asLocalRef .i8 (intVal 0 8))
        pure (some (unitRef, retTy))
      else
        pure (some (ref, retTy))

/-- Lower an Alloy terminator to LLVM -/
def lowerTerminator (term : Terminator) (retTy : ClosedTy) (llvmRetOverride : Option LLVMType := none) : CodegenM Unit := do
  match term with
  | .jump target =>
    let label ← CodegenM.getOrCreateBlock target.id
    CodegenM.withFuncBuilder (FuncBuilder.br label)

  | .branch cond thenBlock elseBlock =>
    let condVal ← convertOperand cond
    let thenLabel ← CodegenM.getOrCreateBlock thenBlock.id
    let elseLabel ← CodegenM.getOrCreateBlock elseBlock.id
    CodegenM.withFuncBuilder (FuncBuilder.condBr condVal thenLabel elseLabel)

  | .switch val cases default =>
    let (valLLVMTy, valRef) ← convertOperandWithTy val
    let defaultLabel ← CodegenM.getOrCreateBlock default.id
    let llvmCases ← cases.mapM fun (intVal, blockId) => do
      let label ← CodegenM.getOrCreateBlock blockId.id
      let bits := valLLVMTy.intBits.getD 32
      pure (LLVMConst.int intVal bits, label)
    CodegenM.withFuncBuilder (FuncBuilder.switch valLLVMTy valRef defaultLabel llvmCases)

  | .ret val =>
    let actualRetTy := llvmRetOverride.getD (convertTy retTy)
    if isUnitTy retTy then
      match actualRetTy with
      | .void => CodegenM.withFuncBuilder FuncBuilder.retVoid
      | ty => CodegenM.withFuncBuilder (FuncBuilder.ret ty (intVal 0 (ty.intBits.getD 32)))
    else
      let (llvmValTy, valRef) ← convertOperandWithTy val
      if llvmRetOverride == some .i32 && llvmValTy == .ptr then
        -- IO action: call soma_apply(action, null_world) to execute it
        let nullWorld ← CodegenM.withFuncBuilder (FuncBuilder.asLocalRef .ptr (.const .null))
        let ioResult ← CodegenM.withFuncBuilder
          (FuncBuilder.callNamed .ptr "soma_apply" #[(.ptr, valRef), (.ptr, .local nullWorld)])
        -- Return 0 (success) since the IO action's side effects have been executed
        CodegenM.withFuncBuilder (FuncBuilder.ret .i32 (intVal 0 32))
      else if llvmValTy == actualRetTy then
        CodegenM.withFuncBuilder (FuncBuilder.ret actualRetTy valRef)
      else
        let coerced ← coerceValue llvmValTy actualRetTy valRef
        CodegenM.withFuncBuilder (FuncBuilder.ret actualRetTy coerced)

  | .retUnit =>
    match llvmRetOverride with
    | some ty =>
      if ty == .void then CodegenM.withFuncBuilder FuncBuilder.retVoid
      else CodegenM.withFuncBuilder (FuncBuilder.ret ty (intVal 0 (ty.intBits.getD 32)))
    | none => CodegenM.withFuncBuilder FuncBuilder.retVoid

  | .unreachable =>
    CodegenM.withFuncBuilder FuncBuilder.unreachable

/-- Collect LocalIds referenced in an instruction -/
def instReferencedLocals (inst : ClosedInst) : Array Nat :=
  let collectOp : Operand → Array Nat := fun op =>
    match op with
    | .local id => #[id.id]
    | _ => #[]
  let collectOps := fun ops => ops.foldl (fun acc op => acc ++ collectOp op) #[]
  match inst with
  | .binOp _ l r _ => collectOp l ++ collectOp r
  | .unOp _ op => collectOp op
  | .copy op => collectOp op
  | .load ptr _ => collectOp ptr
  | .store ptr val => collectOp ptr ++ collectOp val
  | .call _ args _ => collectOps args
  | .callIndirect ptr args _ => collectOp ptr ++ collectOps args
  | .callClosure cls args _ => collectOp cls ++ collectOps args
  | .phi incoming _ => incoming.foldl (fun acc (op, _) => acc ++ collectOp op) #[]
  | .select c t e => collectOp c ++ collectOp t ++ collectOp e
  | .structLit fields _ => collectOps fields
  | .extractField v _ => collectOp v
  | .getFieldPtr v _ _ => collectOp v
  | .makeClosure _ env => collectOp env
  | .makeClosureDyn fnClo env _ => collectOp fnClo ++ collectOp env
  | .malloc sz => collectOp sz
  | .free ptr => collectOp ptr
  | .callIntrinsic _ args _ => collectOps args
  | .callExtern _ args _ => collectOps args
  | .callExternPoly _ _ args _ => collectOps args
  | _ => #[]

/-- Lower an Alloy basic block to LLVM -/
def lowerBlock (block : ClosedBlock) (retTy : ClosedTy) (llvmRetOverride : Option LLVMType := none) : CodegenM Unit := do
  let label ← CodegenM.getOrCreateBlock block.id.id
  CodegenM.withFuncBuilder (FuncBuilder.startBlock label)

  -- Get the Alloy Func to look up local types
  let func? ← CodegenM.getCurrentFunc

  let callerActualRetTy := llvmRetOverride.getD (func?.map (fun f => convertRetTy f.sig.retTy) |>.getD .void)
  let tailCallResultId ← if llvmRetOverride.isSome then pure none else match block.terminator with
    | .ret (.local retId) => do
      let mut result : Option Nat := none
      for i in (List.range block.stmts.size).reverse do
        if result.isSome then break
        if let some stmt := block.stmts[i]? then
          if stmt.result == some retId then
            match stmt.inst with
            | .call funcId _ _ | .callPoly funcId _ _ _ =>
              let calleeSig ← CodegenM.getFuncSig funcId.id
              match calleeSig with
              | some sig =>
                let calleeActualRetTy := convertRetTy sig.retTy
                if callerActualRetTy == calleeActualRetTy then
                  result := some retId.id
              | none => pure ()
            | .callExtern _ _ callRetTy | .callExternPoly _ _ _ callRetTy =>
              let calleeActualRetTy := convertRetTy callRetTy
              if callerActualRetTy == calleeActualRetTy then
                result := some retId.id
            | _ => pure ()
      pure result
    | _ => pure none

  for stmt in block.stmts do
    if let some tcId := tailCallResultId then
      if stmt.result == some ⟨tcId⟩ then
        modify fun s => { s with emitAsTailCall := true }

    let maybeResult ← lowerInst stmt.inst
    match stmt.result, maybeResult with
    | some alloyLocal, some (llvmRef, _tyFromLowerInst) =>
      let tyFromAlloy := func?.bind (·.getLocalType alloyLocal)
      let ty := match tyFromAlloy with
        | some .rawPtr => _tyFromLowerInst
        | some t => t
        | none => _tyFromLowerInst
      CodegenM.mapLocal alloyLocal.id llvmRef ty
      match stmt.inst with
      | .copy (.const (.string idx _)) =>
        modify fun s => { s with stringConstLocals := s.stringConstLocals.insert alloyLocal.id idx }
      | _ => pure ()
    | none, _ => pure ()
    | some alloyLocal, none =>
      let tyFromAlloy := func?.bind (·.getLocalType alloyLocal)
        |>.orElse (fun _ => stmt.inst.resultTy)
        |>.getD (.prim .unit)
      let llvmTy := convertTy tyFromAlloy
      let dummyRef ← CodegenM.withFuncBuilder do
        if llvmTy == .ptr then
          FuncBuilder.asLocalRef .ptr (.const .null)
        else if llvmTy.isInt then
          FuncBuilder.add llvmTy (intVal 0 (llvmTy.intBits.getD 64)) (intVal 0 (llvmTy.intBits.getD 64))
        else do
          let allocaRef ← FuncBuilder.emit (.alloca llvmTy none none)
          FuncBuilder.emit (.load llvmTy (.local allocaRef) none)
      CodegenM.mapLocal alloyLocal.id dummyRef tyFromAlloy

    if (← CodegenM.consumeNoReturn) then
      CodegenM.markBlockDead block.id.id
      CodegenM.withFuncBuilder FuncBuilder.unreachable
      return

  lowerTerminator block.terminator retTy llvmRetOverride

/-- Lower an Alloy function to LLVM with explicit name -/
def lowerFuncWithName (func : ClosedFunc) (name : String) : CodegenM LLVMFunc := do
  CodegenM.clearFuncState
  CodegenM.setCurrentFunc func

  -- Map parameter locals to their types first (to get consistent numbering)
  for param in func.sig.params do
    let localRef ← CodegenM.withFuncBuilder FuncBuilder.freshLocal
    CodegenM.mapLocal param.id.id localRef param.ty

  -- Convert parameters using numeric names matching the LocalRef IDs
  let funcBorrowInfo := (← get).borrowInfo.get? func.id.id
  let llvmParams : Array LLVMParam ← func.sig.params.mapIdxM fun i p => do
    let llvmTy := convertTy p.ty
    let attrs := match funcBorrowInfo with
      | some borrowed =>
        if borrowed.getD i false && llvmTy == .ptr then #["nocapture", "readonly"] else #[]
      | none => #[]
    match ← CodegenM.getLocal p.id.id with
    | some ref => pure { name := s!"v{ref.id}", ty := llvmTy, attrs }
    | none => pure { name := p.name, ty := llvmTy, attrs }

  -- Convert return type
  let isMain := name == "soma_main"
  let llvmRetTy := if isMain then .i32 else convertRetTy func.sig.retTy

  -- Convert attributes
  let llvmAttrs : LLVMFuncAttrs := {
    nounwind := true
    alwaysInline := func.attrs.inline
    noInline := func.attrs.noInline
    callconv := if isMain then none else some .fast
  }

  match func.body with
  | none =>
    pure {
      name := name
      retTy := llvmRetTy
      params := llvmParams
      attrs := llvmAttrs
      isDeclaration := true
    }
  | some cfg =>
    -- Pre-create labels for all blocks
    for block in cfg.allBlocks do
      let _ ← CodegenM.getOrCreateBlock block.id.id

    -- Lower all blocks
    let blockOrder := cfg.reversePostorder
    let reachable : Std.HashSet Nat := blockOrder.foldl (fun s bid => s.insert bid.id) {}
    for block in cfg.allBlocks do
      if !reachable.contains block.id.id then
        CodegenM.markBlockDead block.id.id
    for blockId in blockOrder do
      if let some block := cfg.getBlock blockId then
        lowerBlock block func.sig.retTy (if isMain then some .i32 else none)

    let blocks ← CodegenM.withFuncBuilder FuncBuilder.getBlocks

    pure {
      name := name
      retTy := llvmRetTy
      params := llvmParams
      attrs := llvmAttrs
      blocks := blocks
      isDeclaration := false
    }

/-- Lower an Alloy function to LLVM -/
def lowerFunc (func : ClosedFunc) : CodegenM LLVMFunc := do
  lowerFuncWithName func func.sig.name

/-- Add runtime function declarations -/
def addRuntimeDeclarations : CodegenM Unit := do
  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "malloc"
      retTy := .ptr
      returnAttrs := #["noalias"]
      params := #[{ name := "size", ty := .i64 }]
      attrs := { nounwind := true, willreturn := true,
                 memory := some "inaccessiblemem: readwrite" }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "free"
      retTy := .void
      params := #[{ name := "ptr", ty := .ptr, attrs := #["nocapture"] }]
      attrs := { nounwind := true, willreturn := true,
                 memory := some "argmem: readwrite, inaccessiblemem: readwrite" }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_era_free"
      retTy := .void
      params := #[{ name := "ptr", ty := .ptr, attrs := #["nocapture"] }]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_era_closure"
      retTy := .void
      params := #[{ name := "ptr", ty := .ptr, attrs := #["nocapture"] }]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  -- String runtime functions: on Windows, structs > 8 bytes use byval/sret ABI
  let strTy := somaStringLLVMTy
  let strTyStr := strTy.toLLVM
  if (← get).targetOs.isWindowsABI then
    -- Windows x64: structs passed by hidden pointer (byval), returned via sret
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_era_string"
        retTy := .void
        params := #[{ name := "str", ty := .ptr, attrs := #[s!"byval({strTyStr})"] }]
        attrs := { nounwind := true }
        isDeclaration := true
      }

    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_from_cstring"
        retTy := .void
        params := #[
          { name := "ret", ty := .ptr, attrs := #[s!"sret({strTyStr})"] },
          { name := "cstr", ty := .ptr, attrs := #["nocapture", "readonly"] }
        ]
        attrs := { nounwind := true }
        isDeclaration := true
      }

    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_strcat"
        retTy := .void
        params := #[
          { name := "ret", ty := .ptr, attrs := #[s!"sret({strTyStr})"] },
          { name := "a", ty := .ptr, attrs := #[s!"byval({strTyStr})"] },
          { name := "b", ty := .ptr, attrs := #[s!"byval({strTyStr})"] }
        ]
        attrs := { nounwind := true }
        isDeclaration := true
      }

    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_int_to_string"
        retTy := .void
        params := #[
          { name := "ret", ty := .ptr, attrs := #[s!"sret({strTyStr})"] },
          { name := "val", ty := .i32 }
        ]
        attrs := { nounwind := true }
        isDeclaration := true
      }
  else
    -- Non-Windows (SysV): coerce string struct to { i64, i64 } for correct ABI
    let coercedStrTy := sysVCoercedType strTy
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_era_string"
        retTy := .void
        params := #[{ name := "str", ty := coercedStrTy }]
        attrs := { nounwind := true }
        isDeclaration := true
      }

    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_from_cstring"
        retTy := coercedStrTy
        params := #[{ name := "cstr", ty := .ptr, attrs := #["nocapture", "readonly"] }]
        attrs := { nounwind := true }
        isDeclaration := true
      }

    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_strcat"
        retTy := coercedStrTy
        params := #[
          { name := "a", ty := coercedStrTy },
          { name := "b", ty := coercedStrTy }
        ]
        attrs := { nounwind := true }
        isDeclaration := true
      }

    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_int_to_string"
        retTy := coercedStrTy
        params := #[{ name := "val", ty := .i32 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_pool_alloc_raw"
      retTy := .ptr
      returnAttrs := #["noalias"]
      params := #[{ name := "byte_size", ty := .i64 }]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_pool_free_raw"
      retTy := .void
      params := #[{ name := "ptr", ty := .ptr, attrs := #["nocapture"] },
                  { name := "byte_size", ty := .i64 }]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_panic"
      retTy := .void
      params := #[{ name := "msg", ty := .ptr, attrs := #["nocapture", "readonly"] }]
      attrs := { noreturn := true, nounwind := true, cold := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "llvm.memcpy.p0.p0.i64"
      retTy := .void
      params := #[
        { name := "dst", ty := .ptr, attrs := #["nocapture", "writeonly"] },
        { name := "src", ty := .ptr, attrs := #["nocapture", "readonly"] },
        { name := "len", ty := .i64 },
        { name := "isvolatile", ty := .i1 }
      ]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "llvm.memset.p0.i64"
      retTy := .void
      params := #[
        { name := "dst", ty := .ptr, attrs := #["nocapture", "writeonly"] },
        { name := "val", ty := .i8 },
        { name := "len", ty := .i64 },
        { name := "isvolatile", ty := .i1 }
      ]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_apply"
      retTy := .ptr
      params := #[{ name := "closure", ty := .ptr }, { name := "arg", ty := .ptr }]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  -- SUP operations
  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_dup_typed"
      retTy := .i64
      params := #[{ name := "label", ty := .i32 }, { name := "value", ty := .i64 },
                  { name := "type_desc", ty := .ptr }]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_clone_closure"
      retTy := .ptr
      params := #[{ name := "closure", ty := .ptr }, { name := "label", ty := .i32 }]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_clone_heap_value_for_dup"
      retTy := .ptr
      params := #[{ name := "value", ty := .ptr }, { name := "label", ty := .i32 }]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_proj0"
      retTy := .i64
      params := #[{ name := "sup_val", ty := .i64 }]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_proj1"
      retTy := .i64
      params := #[{ name := "sup_val", ty := .i64 }]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  -- Legacy flat array view operations
  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_clone_flat_array_view"
      retTy := .ptr
      returnAttrs := #["noalias"]
      params := #[{ name := "src", ty := .ptr, attrs := #["nocapture", "readonly"] }]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_alloc_view"
      retTy := .ptr
      returnAttrs := #["noalias"]
      params := #[]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_free_view"
      retTy := .void
      params := #[{ name := "ptr", ty := .ptr, attrs := #["nocapture"] }]
      attrs := { nounwind := true }
      isDeclaration := true
    }

  -- SysV x86-64: fits in 2 registers. Win64: still needs byval/sret (>8 bytes)
  let listTy := somaListLLVMTy
  let listTyStr := listTy.toLLVM
  if (← get).targetOs.isWindowsABI then
    -- Windows x64: SomaList (32 bytes) passed via hidden pointer
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_cons"
        retTy := .void
        params := #[
          { name := "ret", ty := .ptr, attrs := #[s!"sret({listTyStr})"] },
          { name := "elem", ty := .ptr, attrs := #["nocapture", "readonly"] },
          { name := "tail", ty := .ptr, attrs := #[s!"byval({listTyStr})"] },
          { name := "elem_size", ty := .i16 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_head"
        retTy := .ptr
        params := #[
          { name := "list", ty := .ptr, attrs := #[s!"byval({listTyStr})"] },
          { name := "elem_size", ty := .i16 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_tail"
        retTy := .void
        params := #[
          { name := "ret", ty := .ptr, attrs := #[s!"sret({listTyStr})"] },
          { name := "list", ty := .ptr, attrs := #[s!"byval({listTyStr})"] },
          { name := "elem_size", ty := .i16 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_dup"
        retTy := .void
        params := #[
          { name := "ret", ty := .ptr, attrs := #[s!"sret({listTyStr})"] },
          { name := "list", ty := .ptr, attrs := #[s!"byval({listTyStr})"] },
          { name := "elem_size", ty := .i16 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_era"
        retTy := .void
        params := #[{ name := "list", ty := .ptr, attrs := #[s!"byval({listTyStr})"] }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_from_array"
        retTy := .void
        params := #[
          { name := "ret", ty := .ptr, attrs := #[s!"sret({listTyStr})"] },
          { name := "data", ty := .ptr, attrs := #["nocapture", "readonly"] },
          { name := "len", ty := .i32 },
          { name := "elem_size", ty := .i16 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
  else
    -- Non-Windows (SysV): coerce SomaList struct to { i64, i64 } for correct ABI
    let coercedListTy := sysVCoercedType listTy
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_cons"
        retTy := coercedListTy
        params := #[
          { name := "elem", ty := .ptr, attrs := #["nocapture", "readonly"] },
          { name := "tail", ty := coercedListTy },
          { name := "elem_size", ty := .i16 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_head"
        retTy := .ptr
        params := #[{ name := "list", ty := coercedListTy }, { name := "elem_size", ty := .i16 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_tail"
        retTy := coercedListTy
        params := #[{ name := "list", ty := coercedListTy }, { name := "elem_size", ty := .i16 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_dup"
        retTy := coercedListTy
        params := #[{ name := "list", ty := coercedListTy }, { name := "elem_size", ty := .i16 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_era"
        retTy := .void
        params := #[{ name := "list", ty := coercedListTy }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_from_array"
        retTy := coercedListTy
        params := #[
          { name := "data", ty := .ptr, attrs := #["nocapture", "readonly"] },
          { name := "len", ty := .i32 },
          { name := "elem_size", ty := .i16 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
  -- SUP integration: box/unbox/dup_typed_list use simpler ABIs
  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_dup_typed_list"
      retTy := .i64
      params := #[{ name := "label", ty := .i32 }, { name := "boxed", ty := .ptr }]
      attrs := { nounwind := true }
      isDeclaration := true
    }
  -- soma_list_unbox(boxed: ptr) → SomaList (struct return)
  -- soma_list_box_for_sup(list: SomaList, elem_size: i16) → ptr
  -- These have struct types so need platform-specific declarations like other list ops
  if (← get).targetOs.isWindowsABI then
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_box_for_sup"
        retTy := .ptr
        params := #[
          { name := "list", ty := .ptr, attrs := #[s!"byval({listTyStr})"] },
          { name := "elem_size", ty := .i16 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_unbox"
        retTy := .void
        params := #[
          { name := "ret", ty := .ptr, attrs := #[s!"sret({listTyStr})"] },
          { name := "boxed", ty := .ptr }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
  else
    let coercedListTy := sysVCoercedType listTy
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_box_for_sup"
        retTy := .ptr
        params := #[{ name := "list", ty := coercedListTy }, { name := "elem_size", ty := .i16 }]
        attrs := { nounwind := true }
        isDeclaration := true
      }
    CodegenM.withModuleBuilder do
      ModuleBuilder.addFunc {
        name := "soma_list_unbox"
        retTy := coercedListTy
        params := #[{ name := "boxed", ty := .ptr }]
        attrs := { nounwind := true }
        isDeclaration := true
      }

  for listFn in #["soma_list_cons", "soma_list_head", "soma_list_tail",
                   "soma_list_dup", "soma_list_era", "soma_list_from_array",
                   "soma_list_box_for_sup", "soma_list_unbox", "soma_dup_typed_list"] do
    CodegenM.markExternDeclared listFn

  let runtimeNames := #[
    "malloc", "free",
    "soma_era_free", "soma_era_closure", "soma_era_string", "soma_panic",
    "llvm.memcpy.p0.p0.i64", "llvm.memset.p0.i64",
    "soma_pool_alloc_raw", "soma_pool_free_raw",
    "soma_from_cstring",
    "soma_strcat", "soma_int_to_string",
    "soma_apply", "soma_dup_typed", "soma_proj0", "soma_proj1",
    "soma_clone_closure", "soma_clone_heap_value_for_dup",
    "soma_clone_flat_array_view", "soma_alloc_view", "soma_free_view"
  ]
  for name in runtimeNames do
    CodegenM.markExternDeclared name

/-- Lower an Alloy module to LLVM -/
def lowerModule (alloyModule : Module) : CodegenM LLVMModule := do
  let monoFuncs := alloyModule.monoFuncs

  -- Register all functions first (names and signatures)
  let mut seenNames : Std.HashMap String Nat := {}
  for func in monoFuncs do
    let isMain := alloyModule.mainFunc == some func.id
    let baseName := if isMain then "soma_main" else func.sig.name
    let name := match seenNames.get? baseName with
      | none => baseName
      | some count => s!"{baseName}$$mono{count}"
    seenNames := seenNames.insert baseName ((seenNames.get? baseName |>.getD 0) + 1)
    CodegenM.registerFunc func.id.id name func.sig

  addRuntimeDeclarations

  -- Find panic string index in the string table
  let panicMsg := "soma: unreachable code"
  let panicStrIdx := alloyModule.strings.strings.findIdx? (· == panicMsg) |>.getD 0
  modify fun s => { s with
    panicStrName := s!".str.{panicStrIdx}"
    stringTable := alloyModule.strings.strings
  }

  -- Emit string table as LLVM global constants
  for (s, idx) in alloyModule.strings.strings.zipIdx do
    let strBytes := s.utf8ByteSize + 1
    let rawGlobal : LLVMGlobal := {
      name := s!".str.{idx}"
      ty := .array strBytes .i8
      init := some (.string s)
      linkage := .private_
      isConstant := true
      align := some 1
    }
    CodegenM.withModuleBuilder do
      modify fun st => { st with module := { st.module with
        globals := st.module.globals.push rawGlobal } }

  -- Add type definitions
  for typedef in alloyModule.types do
    let fields := match typedef.ty with
      | .struct fs => fs.map fun (_, t) => convertTy t
      | _ => #[]
    CodegenM.withModuleBuilder (ModuleBuilder.addType typedef.name fields)

  -- Add globals
  for global in alloyModule.globals do
    let llvmGlobal : LLVMGlobal := {
      name := global.name
      ty := convertTy global.ty
      init := global.init.map fun c =>
        match c with
        | .int v t =>
          let bits := match t with
            | .i8 | .u8 => 8 | .i16 | .u16 => 16 | .i32 | .u32 => 32 | _ => 64
          .int v bits
        | .float v _ => .float64 v
        | .bool b => .bool b
        | .unit => .int 0 1
        | .null _ => .null
        | _ => .null
      isConstant := !global.mutable
    }
    CodegenM.withModuleBuilder (ModuleBuilder.addGlobal llvmGlobal)

  -- Lower all monomorphic functions
  for func in monoFuncs do
    let funcName ← CodegenM.getFuncName func.id.id
    let llvmFunc ← lowerFuncWithName func funcName
    CodegenM.withModuleBuilder (ModuleBuilder.addFunc llvmFunc)

  CodegenM.withModuleBuilder ModuleBuilder.getModule

/-- Generate LLVM IR from an Alloy module -/
def codegen (alloyModule : Module) (targetTriple : Option String := none)
    (targetOs : TargetOS) (ptrSize : Nat)
    (borrowInfo : Std.HashMap Nat (Array Bool) := {})
    (dataLayout : Option String := none) : LLVMModule :=
  let initState : CodegenState :=
    { CodegenM.init alloyModule.name targetTriple dataLayout ptrSize targetOs with borrowInfo }
  let (llvmModule, _) := Id.run (StateT.run (lowerModule alloyModule) initState)
  llvmModule

/-- Generate LLVM IR text from an Alloy module -/
def codegenToString (alloyModule : Module) (targetTriple : Option String := none)
    (targetOs : TargetOS) (ptrSize : Nat)
    (borrowInfo : Std.HashMap Nat (Array Bool) := {})
    (dataLayout : Option String := none) : String :=
  let llvmModule := codegen alloyModule targetTriple targetOs ptrSize borrowInfo dataLayout
  llvmModule.toLLVM

end Somac.Llvm.Codegen
