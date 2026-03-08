import Somac.Alloy.Func
import Somac.Llvm.Builder
import Std.Data.HashMap

namespace Somac.Llvm.Codegen

open Somac.Alloy
open Somac.Llvm
open Somac.Llvm.Builder

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
  | .prim .unit => .i8
  | other => convertTy other

/-- Runtime closure object pointer type -/
def closureTy : LLVMType := .ptr

/-- Closure header struct for inline GEP field access -/
def closureHeaderTy : LLVMType := .struct false #[.i8, .i8, .i16, .i32, .ptr]

/-- env_kind constants  -/
def envKindDefault : Int := 0
def envKindFlat    : Int := 1
def envKindTagged  : Int := 2
def envKindList    : Int := 3

/-- NODE_CLOSURE tag constant -/
def nodeClosureTag : Int := 1

/-- The tagged union struct type -/
def taggedTy : LLVMType := .struct false #[.i32, .ptr]

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
  ty == (.ptr (.struct #[("length", .prim .i64), ("data", .rawPtr)]) : ClosedTy)

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
  deriving Inhabited

/-- Codegen monad -/
abbrev CodegenM := StateM CodegenState

namespace CodegenM

/-- Initialize codegen state -/
def init (name : String) (triple : Option String := none) : CodegenState :=
  { moduleState := ModuleBuilder.init name triple }

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
def clearFuncState : CodegenM Unit := do
  modify fun s => { s with
    localMap := {}
    localTypes := {}
    blockMap := {}
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
    -- First try the Alloy Func's localTypes (authoritative source)
    let func? ← CodegenM.getCurrentFunc
    match func?.bind (·.getLocalType id) with
    | some ty => pure ty
    | none =>
      -- Fall back to CodegenState.localTypes
      CodegenM.getLocalTy id.id
  | .const c => pure c.ty
  | .global _ => pure .rawPtr
  | .func _ => pure .rawPtr

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
        else FuncBuilder.add dstTy val (intVal 0 dstBits)
      -- Tagged union struct { i32, ptr } → extract tag (i32) or payload (ptr)
      else if srcTy == taggedTy then
        match dstTy with
        | .i32 => FuncBuilder.extractvalue srcTy val #[0]
        | .ptr => FuncBuilder.extractvalue srcTy val #[1]
        | _ => panic! s!"CODEGEN BUG: coerceValue cannot convert {srcTy.toLLVM} to {dstTy.toLLVM}"
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
      panic! s!"CODEGEN BUG: local %{id.id} not found"
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
    | .string idx _ => pure (.global ⟨s!".str.{idx}"⟩)
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
    -- Already i64, just need to produce an SSA value
    CodegenM.withFuncBuilder (FuncBuilder.add .i64 val (intVal 0 64))
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
    CodegenM.withFuncBuilder (FuncBuilder.add .i64 val (intVal 0 64))
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
        -- Same type, no-op (just produce SSA value)
        if toTy.isInt then
          FuncBuilder.add toTy operand (intVal 0 (toTy.intBits.getD 64))
        else if toTy == .ptr then
          FuncBuilder.bitcast .ptr .ptr operand
        else
          -- For structs/other types, use select to produce new SSA value
          FuncBuilder.select toTy (boolVal true) operand operand
      else if llvmSrcTy.isInt && toTy == .ptr then
        FuncBuilder.inttoptr llvmSrcTy operand
      else if llvmSrcTy == .ptr && toTy.isInt then
        FuncBuilder.ptrtoint toTy operand
      else if llvmSrcTy == .ptr && toTy == .ptr then
        FuncBuilder.bitcast .ptr .ptr operand
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
          FuncBuilder.add llvmSrcTy operand (intVal 0 srcBits)
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
    if isStringObjTy ty then
      CodegenM.withFuncBuilder do
        FuncBuilder.callNamedVoid "soma_era_string" #[(.ptr, valRef)]
    else
      CodegenM.withFuncBuilder do
        FuncBuilder.callNamedVoid "soma_era_free" #[(.ptr, valRef)]
  | .tagged _ _ =>
    -- Tagged union {i32, ptr}: free the payload buffer via runtime helper
    -- that reads the count prefix and recursively frees pointer-valued fields.
    let payloadPtr ← CodegenM.withFuncBuilder do
      FuncBuilder.extractvalue taggedTy valRef #[1]
    CodegenM.withFuncBuilder do
      FuncBuilder.callNamedVoid "soma_era_tagged_payload" #[(.ptr, .local payloadPtr)]
  | .closure _ _ =>
    -- Runtime closure object pointer.
    CodegenM.withFuncBuilder do
      FuncBuilder.callNamedVoid "soma_era_free" #[(.ptr, valRef)]
  | .struct fields =>
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

/-- Lower a direct function call -/
def lowerDirectCall (funcId : Nat) (args : Array Operand) (retTy : ClosedTy)
    : CodegenM (Option (LocalRef × ClosedTy)) := do
  let funcName ← CodegenM.getFuncName funcId
  let llvmRetTy := convertTy retTy
  let maybeSig ← CodegenM.getFuncSig funcId
  let llvmArgs ← args.mapIdxM fun i arg => do
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
  let ref ← CodegenM.withFuncBuilder do
    FuncBuilder.callNamed llvmRetTy funcName llvmArgs
  pure (some (ref, retTy))

/-- Lower an Alloy instruction to LLVM, returning result ref and result type -/
def lowerInst (inst : ClosedInst) : CodegenM (Option (LocalRef × ClosedTy)) := do
  match inst with
  | .binOp op lhs rhs ty =>
    let lhsVal ← convertOperand lhs
    let rhsVal ← convertOperand rhs
    let ref ← convertBinOp op ty lhsVal rhsVal
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
    | .const (.undef _) =>
      -- Return none to let the statement handler emit a correctly-typed value
      pure none
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
            -- todo: consider optimizing
            FuncBuilder.inttoptr .i64 (intVal 0 64)
          | .const (.int v bits) =>
            -- todo: consider optimizing
            FuncBuilder.add llvmTy srcVal (intVal 0 bits)
          | _ =>
            -- For other values, bitcast to same type (LLVM will eliminate)
            if llvmTy == .ptr then
              FuncBuilder.bitcast .ptr .ptr srcVal
            else if llvmTy.isInt then
              FuncBuilder.add llvmTy srcVal (intVal 0 (llvmTy.intBits.getD 64))
            else
              FuncBuilder.bitcast llvmTy llvmTy srcVal
        pure (some (ref, srcTy))

  | .alloca ty =>
    let llvmTy := convertTy ty
    let ref ← CodegenM.withFuncBuilder (FuncBuilder.alloca llvmTy (some 8))
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
    -- Allocate and initialize struct
    let structPtr ← CodegenM.withFuncBuilder (FuncBuilder.alloca llvmTy)
    for i in [:fields.size] do
      if h : i < fields.size then
        let fieldOp := fields[i]
        let (fieldLLVMTy, fieldVal) ← convertOperandWithTy fieldOp
        let fieldPtr ← CodegenM.withFuncBuilder do
          FuncBuilder.gepi32 llvmTy (.local structPtr) #[0, i]
        CodegenM.withFuncBuilder do
          FuncBuilder.store fieldLLVMTy fieldVal (.local fieldPtr)
    let ref ← CodegenM.withFuncBuilder (FuncBuilder.load llvmTy (.local structPtr))
    pure (some (ref, ty))

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
        -- First field is not a tagged union, extract it as the tag
        let ref ← CodegenM.withFuncBuilder do
          FuncBuilder.extractvalue llvmValTy valRef #[0]
        pure (some (ref, .prim .u32))
    | .prim .bool =>
      -- Bool: zext i1 to i32
      let ref ← CodegenM.withFuncBuilder do
        FuncBuilder.zext .i1 .i32 valRef
      pure (some (ref, .prim .u32))
    | _ =>
      match llvmValTy with
      | .i32 =>
        -- Already i32, just copy it (for simple enums)
        let ref ← CodegenM.withFuncBuilder do
          FuncBuilder.add .i32 valRef (intVal 0 32)
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
    -- Payload layout: [tag+pad : 8B, count : i64, field0 : i64, ...]
    -- Fields start at i64 index 2 (after 8-byte header + 8-byte count)
    let fieldPtr ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi64 .i64 (.local payloadPtr) #[fieldIdx + 2]
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.load llvmResultTy (.local fieldPtr)
    pure (some (ref, resultTy))

  | .taggedLit tag payload ty =>
    let taggedPtr ← CodegenM.withFuncBuilder (FuncBuilder.alloca taggedTy)
    -- Store tag
    let tagPtr ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 taggedTy (.local taggedPtr) #[0, 0]
    CodegenM.withFuncBuilder do
      FuncBuilder.store .i32 (i32Val tag) (.local tagPtr)
    -- Allocate and store payload if non-empty
    if payload.size > 0 then
      -- Payload layout: [tag+pad : 8B, count : i64, field0 : i64, ...]
      -- Fields start at i64 index 2 (after 8-byte header + 8-byte count)
      let payloadMem ← CodegenM.withFuncBuilder do
        FuncBuilder.callNamed .ptr "soma_alloc_tagged_payload" #[(.i64, i64Val payload.size)]
      for i in [:payload.size] do
        if h : i < payload.size then
          let fieldOp := payload[i]
          let (fieldLLVMTy, fieldVal) ← convertOperandWithTy fieldOp
          let fieldPtr ← CodegenM.withFuncBuilder do
            FuncBuilder.gepi64 .i64 (.local payloadMem) #[i + 2]
          -- Store as i64 to match the i64-slot payload layout used by taggedFieldAccess
          let i64Val ← toI64 fieldLLVMTy fieldVal
          CodegenM.withFuncBuilder do
            FuncBuilder.store .i64 (.local i64Val) (.local fieldPtr)
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
    let llvmRetTy := convertTy retTy
    -- Check if closure operand is actually a closure type (not unit from ERA)
    if closureLLVMTy != closureTy then
      -- Not a real closure
      CodegenM.withFuncBuilder do
        FuncBuilder.callNamedVoid "soma_panic" #[(.ptr, globalVal ".str.panic")]
      let ref ← CodegenM.withFuncBuilder do
        if llvmRetTy == .ptr then
          FuncBuilder.inttoptr .i64 (intVal 0 64)
        else
          FuncBuilder.add .i64 (intVal 0 64) (intVal 0 64)
      pure (some (ref, retTy))
    else
      let closureVal ← convertOperand closure
      -- Inline closure field access via GEP
      let funcPtrAddr ← CodegenM.withFuncBuilder do
        FuncBuilder.gepi32 closureHeaderTy closureVal #[0, 4]
      let fnPtr ← CodegenM.withFuncBuilder do
        FuncBuilder.load .ptr (.local funcPtrAddr)
      let envBaseAddr ← CodegenM.withFuncBuilder do
        FuncBuilder.gepi32 closureHeaderTy closureVal #[1]
      let envRaw ← CodegenM.withFuncBuilder do
        FuncBuilder.load .i64 (.local envBaseAddr)
      let envPtr ← CodegenM.withFuncBuilder do
        FuncBuilder.inttoptr .i64 (.local envRaw)
      -- Build args: env first, then regular args
      let mut llvmArgs : Array (LLVMType × LLVMValue) := #[(.ptr, .local envPtr)]
      for arg in args do
        let argWithTy ← convertOperandWithTy arg
        llvmArgs := llvmArgs.push argWithTy
      let ref ← CodegenM.withFuncBuilder do
        FuncBuilder.call llvmRetTy (.local fnPtr) llvmArgs
      pure (some (ref, retTy))

  | .makeClosure funcRef env =>
    let funcId := match funcRef with
      | .local id => id
      | _ => FuncId.mk 0 -- todo: consider panicking
    let funcName ← CodegenM.getFuncName funcId.id
    let (envLLVMTy, envVal) ← convertOperandWithTy env
    let envAlloTy ← operandTy env
    let closureArity : Nat ← do
      match ← CodegenM.getFuncSig funcId.id with
      | some sig =>
        let n := sig.params.size
        pure (if n == 0 then 0 else n - 1)
      | none => pure 0
    let envKind : Int := match envAlloTy with
      | .tagged _ _ => envKindTagged
      | .prim _ => envKindFlat
      | _ => envKindDefault
    -- Convert env to pointer based on its type
    let envPtrVal ← if envLLVMTy == .ptr then pure envVal
                    else if envLLVMTy.isInt then do
                      let converted ← CodegenM.withFuncBuilder do
                        FuncBuilder.inttoptr envLLVMTy envVal
                      pure (.local converted)
                    else do
                      -- Struct/aggregate type: heap-allocate via malloc so the
                      -- pointer survives closure cloning and can be freed on erase
                      let sizePtr ← CodegenM.withFuncBuilder
                        (FuncBuilder.gepi32 envLLVMTy (.const .null) #[1])
                      let sizeI64 ← CodegenM.withFuncBuilder
                        (FuncBuilder.ptrtoint .i64 (.local sizePtr))
                      let boxPtr ← CodegenM.withFuncBuilder do
                        FuncBuilder.callNamed .ptr "malloc" #[(.i64, .local sizeI64)]
                      CodegenM.withFuncBuilder do
                        FuncBuilder.store envLLVMTy envVal (.local boxPtr)
                      pure (.local boxPtr)
    let closurePtr ← CodegenM.withFuncBuilder do
      FuncBuilder.callNamed .ptr "soma_pool_alloc_closure" #[(.i16, intVal 1 16)]
    -- Initialize header fields inline via GEP+store
    let tagAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 0])
    CodegenM.withFuncBuilder (FuncBuilder.store .i8 (intVal nodeClosureTag 8) (.local tagAddr))
    let arityAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 1])
    CodegenM.withFuncBuilder (FuncBuilder.store .i8 (intVal (Int.ofNat closureArity) 8) (.local arityAddr))
    let envSizeAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 2])
    CodegenM.withFuncBuilder (FuncBuilder.store .i16 (intVal 1 16) (.local envSizeAddr))
    -- Store env_kind (type-directed clone/erase discriminator)
    let envKindAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 3])
    CodegenM.withFuncBuilder (FuncBuilder.store .i32 (intVal envKind 32) (.local envKindAddr))
    let funcFieldAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 4])
    CodegenM.withFuncBuilder (FuncBuilder.store .ptr (globalVal funcName) (.local funcFieldAddr))
    -- Store env[0] at offset 16 (one struct-width past header)
    let envAsI64 ← CodegenM.withFuncBuilder do
      FuncBuilder.ptrtoint .i64 envPtrVal
    let envSlotAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[1])
    CodegenM.withFuncBuilder (FuncBuilder.store .i64 (.local envAsI64) (.local envSlotAddr))
    -- Get closure type from function signature if available
    let closureTyAlloy ← do
      match ← CodegenM.getFuncSig funcId.id with
      | some sig => pure (.closure (sig.params.map (·.ty)) sig.retTy)
      | none => pure (.closure #[] (.prim .i64))
    pure (some (closurePtr, closureTyAlloy))

  | .makeClosurePoly funcRef _typeArgs env =>
    -- Same as makeClosure
    let funcId := match funcRef with
      | .local id => id
      | _ => FuncId.mk 0 -- todo: consider panicking
    let funcName ← CodegenM.getFuncName funcId.id
    let (envLLVMTy, envVal) ← convertOperandWithTy env
    let envAlloTy ← operandTy env
    let closureArity : Nat ← do
      match ← CodegenM.getFuncSig funcId.id with
      | some sig =>
        let n := sig.params.size
        pure (if n == 0 then 0 else n - 1)
      | none => pure 0
    -- Determine env_kind from the Alloy type of the env operand
    let envKind : Int := match envAlloTy with
      | .tagged _ _ => envKindTagged
      | .prim _ => envKindFlat
      | _ => envKindDefault
    -- Convert env to pointer based on its type
    let envPtrVal ← if envLLVMTy == .ptr then pure envVal
                    else if envLLVMTy.isInt then do
                      let converted ← CodegenM.withFuncBuilder do
                        FuncBuilder.inttoptr envLLVMTy envVal
                      pure (.local converted)
                    else do
                      -- Struct/aggregate type: heap-allocate via malloc so the
                      -- pointer survives closure cloning and can be freed on erase.
                      let sizePtr ← CodegenM.withFuncBuilder
                        (FuncBuilder.gepi32 envLLVMTy (.const .null) #[1])
                      let sizeI64 ← CodegenM.withFuncBuilder
                        (FuncBuilder.ptrtoint .i64 (.local sizePtr))
                      let boxPtr ← CodegenM.withFuncBuilder do
                        FuncBuilder.callNamed .ptr "malloc" #[(.i64, .local sizeI64)]
                      CodegenM.withFuncBuilder do
                        FuncBuilder.store envLLVMTy envVal (.local boxPtr)
                      pure (.local boxPtr)
    let closurePtr ← CodegenM.withFuncBuilder do
      FuncBuilder.callNamed .ptr "soma_pool_alloc_closure" #[(.i16, intVal 1 16)]
    let tagAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 0])
    CodegenM.withFuncBuilder (FuncBuilder.store .i8 (intVal nodeClosureTag 8) (.local tagAddr))
    let arityAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 1])
    CodegenM.withFuncBuilder (FuncBuilder.store .i8 (intVal (Int.ofNat closureArity) 8) (.local arityAddr))
    let envSizeAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 2])
    CodegenM.withFuncBuilder (FuncBuilder.store .i16 (intVal 1 16) (.local envSizeAddr))
    -- Store env_kind (type-directed clone/erase discriminator)
    let envKindAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 3])
    CodegenM.withFuncBuilder (FuncBuilder.store .i32 (intVal envKind 32) (.local envKindAddr))
    let funcFieldAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[0, 4])
    CodegenM.withFuncBuilder (FuncBuilder.store .ptr (globalVal funcName) (.local funcFieldAddr))
    -- Store env[0] at offset 16
    let envAsI64 ← CodegenM.withFuncBuilder do
      FuncBuilder.ptrtoint .i64 envPtrVal
    let envSlotAddr ← CodegenM.withFuncBuilder (FuncBuilder.gepi32 closureHeaderTy (.local closurePtr) #[1])
    CodegenM.withFuncBuilder (FuncBuilder.store .i64 (.local envAsI64) (.local envSlotAddr))
    let closureTyAlloy ← do
      match ← CodegenM.getFuncSig funcId.id with
      | some sig => pure (.closure (sig.params.map (·.ty)) sig.retTy)
      | none => pure (.closure #[] (.prim .i64))
    pure (some (closurePtr, closureTyAlloy))

  | .closureFunc closure =>
    let closureVal ← convertOperand closure
    let funcPtrAddr ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 closureHeaderTy closureVal #[0, 4]
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.load .ptr (.local funcPtrAddr)
    pure (some (ref, .rawPtr))

  | .closureEnv closure =>
    let closureVal ← convertOperand closure
    let envBaseAddr ← CodegenM.withFuncBuilder do
      FuncBuilder.gepi32 closureHeaderTy closureVal #[1]
    let rawRef ← CodegenM.withFuncBuilder do
      FuncBuilder.load .i64 (.local envBaseAddr)
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.inttoptr .i64 (.local rawRef)
    pure (some (ref, .rawPtr))

  | .phi incoming ty =>
    let llvmTy := convertTy ty
    let llvmIncoming ← incoming.mapM fun (val, blockId) => do
      let label ← CodegenM.getOrCreateBlock blockId.id
      match val with
      | .local id =>
        match ← CodegenM.getLocal id.id with
        | some ref =>
          let valTy ← CodegenM.getLocalTy id.id
          let valLlvmTy := convertTy valTy
          if valLlvmTy == llvmTy then
            pure (LLVMValue.local ref, label)
          else
            panic! s!"CODEGEN BUG: phi node type mismatch - expected {llvmTy.toLLVM} but got {valLlvmTy.toLLVM} for local %{id.id}"
        | none =>
          panic! s!"CODEGEN BUG: phi node references undefined local %{id.id}"
      | .const c =>
        let constVal ← convertOperand val
        pure (constVal, label)
      | _ =>
        let opVal ← convertOperand val
        pure (opVal, label)
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

  | .lazySup label src _ty =>
    -- Create a SUP node: soma_dup(label, value_as_i64) → i64 tagged pointer
    let srcVal ← convertOperand src
    let srcLlvmTy := convertTy (← operandTy src)
    let srcAsI64 ← toI64 srcLlvmTy srcVal
    let ref ← CodegenM.withFuncBuilder do
      FuncBuilder.callNamed .i64 "soma_dup" #[(.i32, i32Val label.toNat), (.i64, .local srcAsI64)]
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

  | .panic msgIdx line =>
    let _ := line
    CodegenM.withFuncBuilder do
      FuncBuilder.callNamedVoid "soma_panic" #[(.ptr, globalVal s!".str.{msgIdx}")]
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
      -- Convert String to C string: call runtime function
      let ref ← CodegenM.withFuncBuilder (FuncBuilder.callNamed .ptr "soma_to_cstring" llvmArgs)
      pure (some (ref, .rawPtr))

    | .fromCString =>
      -- Convert C string to String: call runtime function
      let ref ← CodegenM.withFuncBuilder (FuncBuilder.callNamed .ptr "soma_from_cstring" llvmArgs)
      pure (some (ref, .rawPtr))

    | .cstringLen =>
      -- Get C string length: call runtime function
      let ref ← CodegenM.withFuncBuilder (FuncBuilder.callNamed .i64 "soma_cstring_len" llvmArgs)
      pure (some (ref, .prim .u64))

    | .strcat =>
      -- String concatenation: call runtime function
      let ref ← CodegenM.withFuncBuilder (FuncBuilder.callNamed .ptr "soma_strcat" llvmArgs)
      pure (some (ref, .rawPtr))

    | .intToString =>
      -- Integer to string: call runtime function
      let ref ← CodegenM.withFuncBuilder (FuncBuilder.callNamed .ptr "soma_int_to_string" llvmArgs)
      pure (some (ref, .rawPtr))

    | .pureIO =>
      -- pure_io is identity at runtime (IO is just a newtype wrapper)
      -- Just return the argument as-is
      if llvmArgs.size > 0 then
        let (_, argVal) := llvmArgs[0]!
        -- Use a no-op bitcast to same type as identity operation
        let ref ← CodegenM.withFuncBuilder (FuncBuilder.bitcast llvmRetTy llvmRetTy argVal)
        pure (some (ref, retTy))
      else
        pure none

    | .bindIO =>
      -- io_bind m f = f(m): IO erases, so this is just closure application
      if llvmArgs.size >= 2 then
        let (ioTy, ioValRaw) := llvmArgs[0]!
        let ioVal ← if ioTy == .i64 then pure ioValRaw
                     else coerceValue ioTy .i64 ioValRaw
        let (funcTy, funcVal) := llvmArgs[1]!
        let funcPtr ← if funcTy == .ptr then pure funcVal
                       else do
                         let ref ← CodegenM.withFuncBuilder (FuncBuilder.inttoptr funcTy funcVal)
                         pure (.local ref)
        let funcPtrAddr ← CodegenM.withFuncBuilder do
          FuncBuilder.gepi32 closureHeaderTy funcPtr #[0, 4]
        let fnPtr ← CodegenM.withFuncBuilder do
          FuncBuilder.load .ptr (.local funcPtrAddr)
        let envBaseAddr ← CodegenM.withFuncBuilder do
          FuncBuilder.gepi32 closureHeaderTy funcPtr #[1]
        let envRaw ← CodegenM.withFuncBuilder do
          FuncBuilder.load .i64 (.local envBaseAddr)
        let envPtr ← CodegenM.withFuncBuilder do
          FuncBuilder.inttoptr .i64 (.local envRaw)
        let ref ← CodegenM.withFuncBuilder do
          FuncBuilder.call llvmRetTy (.local fnPtr) #[(.ptr, .local envPtr), (.i64, ioVal)]
        pure (some (ref, retTy))
      else
        pure none

  | .callExtern name args retTy =>
    -- External function call: emit regular LLVM call to @name
    let llvmRetTy := convertTy retTy
    let llvmArgs ← args.mapM fun arg => convertOperandWithTy arg

    -- Declare the extern function if not already declared
    unless (← CodegenM.isExternDeclared name) do
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

    let ref ← CodegenM.withFuncBuilder (FuncBuilder.callNamed llvmRetTy name llvmArgs)
    pure (some (ref, retTy))

/-- Lower an Alloy terminator to LLVM -/
def lowerTerminator (term : Terminator) (retTy : ClosedTy) : CodegenM Unit := do
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
    let valTy ← operandTy val
    let llvmRetTy := convertTy retTy
    if isUnitTy retTy then
      CodegenM.withFuncBuilder (FuncBuilder.ret .i8 (intVal 0 8))
    else
      let valRef ← convertOperand val
      let llvmValTy := convertTy valTy
      if llvmValTy == llvmRetTy then
        CodegenM.withFuncBuilder (FuncBuilder.ret llvmRetTy valRef)
      else
        let converted ← CodegenM.withFuncBuilder do
          if llvmRetTy == .ptr && llvmValTy.isInt then
            FuncBuilder.inttoptr llvmValTy valRef
          else if llvmRetTy.isInt && llvmValTy == .ptr then
            FuncBuilder.ptrtoint llvmRetTy valRef
          else if llvmRetTy == .ptr && llvmValTy == .ptr then
            pure (match valRef with | .local r => r | _ => ⟨0⟩)
          else if llvmRetTy.isInt && llvmValTy.isInt then
            let srcBits := llvmValTy.intBits.getD 64
            let dstBits := llvmRetTy.intBits.getD 64
            if srcBits < dstBits then FuncBuilder.zext llvmValTy llvmRetTy valRef
            else if srcBits > dstBits then FuncBuilder.trunc llvmValTy llvmRetTy valRef
            else pure (match valRef with | .local r => r | _ => ⟨0⟩)
          else
            panic! s!"CODEGEN BUG: return type mismatch - expected {llvmRetTy.toLLVM} but got {llvmValTy.toLLVM}"
        CodegenM.withFuncBuilder (FuncBuilder.ret llvmRetTy (.local converted))

  | .retUnit =>
    CodegenM.withFuncBuilder (FuncBuilder.ret .i8 (intVal 0 8))

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
  | .malloc sz => collectOp sz
  | .free ptr => collectOp ptr
  | .callIntrinsic _ args _ => collectOps args
  | .callExtern _ args _ => collectOps args
  | _ => #[]

/-- Lower an Alloy basic block to LLVM -/
def lowerBlock (block : ClosedBlock) (retTy : ClosedTy) : CodegenM Unit := do
  let label ← CodegenM.getOrCreateBlock block.id.id
  CodegenM.withFuncBuilder (FuncBuilder.startBlock label)

  -- Get the Alloy Func to look up local types
  let func? ← CodegenM.getCurrentFunc

  for stmt in block.stmts do
    let maybeResult ← lowerInst stmt.inst
    match stmt.result, maybeResult with
    | some alloyLocal, some (llvmRef, _tyFromLowerInst) =>
      let tyFromAlloy := func?.bind (·.getLocalType alloyLocal)
      let ty := tyFromAlloy.getD _tyFromLowerInst
      CodegenM.mapLocal alloyLocal.id llvmRef ty
    | some alloyLocal, none =>
      -- Statement has a result LocalId but lowerInst returned none
      let tyFromAlloy := func?.bind (·.getLocalType alloyLocal) |>.getD (.prim .unit)
      let llvmTy := convertTy tyFromAlloy
      let dummyRef ← CodegenM.withFuncBuilder do
        if llvmTy == .ptr then
          FuncBuilder.inttoptr .i64 (intVal 0 64)
        else if llvmTy.isInt then
          FuncBuilder.add llvmTy (intVal 0 (llvmTy.intBits.getD 64)) (intVal 0 (llvmTy.intBits.getD 64))
        else
          FuncBuilder.add .i64 (intVal 0 64) (intVal 0 64)
      CodegenM.mapLocal alloyLocal.id dummyRef tyFromAlloy
    | none, _ => pure ()

  lowerTerminator block.terminator retTy

/-- Lower an Alloy function to LLVM with explicit name -/
def lowerFuncWithName (func : ClosedFunc) (name : String) : CodegenM LLVMFunc := do
  CodegenM.clearFuncState
  CodegenM.setCurrentFunc func

  -- Map parameter locals to their types first (to get consistent numbering)
  for param in func.sig.params do
    let localRef ← CodegenM.withFuncBuilder FuncBuilder.freshLocal
    CodegenM.mapLocal param.id.id localRef param.ty

  -- Convert parameters using numeric names matching the LocalRef IDs
  let llvmParams : Array LLVMParam ← func.sig.params.mapM fun p => do
    match ← CodegenM.getLocal p.id.id with
    | some ref => pure { name := s!"{ref.id}", ty := convertTy p.ty }
    | none => pure { name := p.name, ty := convertTy p.ty }

  -- Convert return type
  let llvmRetTy := convertRetTy func.sig.retTy

  -- Convert attributes
  let llvmAttrs : LLVMFuncAttrs := {
    nounwind := true
    alwaysInline := func.attrs.inline
    noInline := func.attrs.noInline
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
    for blockId in blockOrder do
      if let some block := cfg.getBlock blockId then
        lowerBlock block func.sig.retTy

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
      params := #[{ name := "size", ty := .i64 }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "free"
      retTy := .void
      params := #[{ name := "ptr", ty := .ptr }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_era_free"
      retTy := .void
      params := #[{ name := "ptr", ty := .ptr }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_era_string"
      retTy := .void
      params := #[{ name := "ptr", ty := .ptr }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_era_tagged_payload"
      retTy := .void
      params := #[{ name := "payload", ty := .ptr }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_alloc_tagged_payload"
      retTy := .ptr
      params := #[{ name := "field_count", ty := .i64 }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_panic"
      retTy := .void
      params := #[{ name := "msg", ty := .ptr }]
      attrs := { noreturn := true }
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "llvm.memcpy.p0.p0.i64"
      retTy := .void
      params := #[
        { name := "dst", ty := .ptr },
        { name := "src", ty := .ptr },
        { name := "len", ty := .i64 },
        { name := "isvolatile", ty := .i1 }
      ]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "llvm.memset.p0.i64"
      retTy := .void
      params := #[
        { name := "dst", ty := .ptr },
        { name := "val", ty := .i8 },
        { name := "len", ty := .i64 },
        { name := "isvolatile", ty := .i1 }
      ]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_to_cstring"
      retTy := .ptr
      params := #[{ name := "str", ty := .ptr }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_from_cstring"
      retTy := .ptr
      params := #[{ name := "cstr", ty := .ptr }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_cstring_len"
      retTy := .i64
      params := #[{ name := "cstr", ty := .ptr }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_strcat"
      retTy := .ptr
      params := #[{ name := "a", ty := .ptr }, { name := "b", ty := .ptr }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_int_to_string"
      retTy := .ptr
      params := #[{ name := "val", ty := .i32 }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_pool_alloc_closure"
      retTy := .ptr
      params := #[{ name := "env_size", ty := .i16 }]
      isDeclaration := true
    }

  -- SUP operations (lazy duplication via superposition nodes)
  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_dup"
      retTy := .i64
      params := #[{ name := "label", ty := .i32 }, { name := "value", ty := .i64 }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_proj0"
      retTy := .i64
      params := #[{ name := "sup_val", ty := .i64 }]
      isDeclaration := true
    }

  CodegenM.withModuleBuilder do
    ModuleBuilder.addFunc {
      name := "soma_proj1"
      retTy := .i64
      params := #[{ name := "sup_val", ty := .i64 }]
      isDeclaration := true
    }

  let runtimeNames := #[
    "malloc", "free", "soma_era_free", "soma_era_string",
    "soma_era_tagged_payload", "soma_alloc_tagged_payload",
    "soma_panic",
    "llvm.memcpy.p0.p0.i64", "llvm.memset.p0.i64",
    "soma_to_cstring", "soma_from_cstring", "soma_cstring_len",
    "soma_strcat", "soma_int_to_string", "soma_pool_alloc_closure",
    "soma_dup", "soma_proj0", "soma_proj1"
  ]
  for name in runtimeNames do
    CodegenM.markExternDeclared name

/-- Lower an Alloy module to LLVM -/
def lowerModule (alloyModule : Module) : CodegenM LLVMModule := do
  let monoFuncs := alloyModule.monoFuncs

  -- Register all functions first (names and signatures)
  for func in monoFuncs do
    let isMain := alloyModule.mainFunc == some func.id
    let name := if isMain then "soma_main" else func.sig.name
    CodegenM.registerFunc func.id.id name func.sig

  addRuntimeDeclarations

  let panicMsg := "soma: unreachable code"
  let panicGlobal : LLVMGlobal := {
    name := ".str.panic"
    ty := .array (panicMsg.utf8ByteSize + 1) .i8
    init := some (.string panicMsg)
    linkage := .private_
    isConstant := true
    align := some 1
  }
  CodegenM.withModuleBuilder do
    modify fun st => { st with module := { st.module with globals := st.module.globals.push panicGlobal } }

  -- Emit string table as LLVM global constants
  for (s, idx) in alloyModule.strings.strings.zipIdx do
    let strBytes := s.utf8ByteSize + 1
    let global : LLVMGlobal := {
      name := s!".str.{idx}"
      ty := .array strBytes .i8
      init := some (.string s)
      linkage := .private_
      isConstant := true
      align := some 1
    }
    CodegenM.withModuleBuilder do
      modify fun st => { st with module := { st.module with globals := st.module.globals.push global } }

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
    let isMain := alloyModule.mainFunc == some func.id
    let funcName := if isMain then "soma_main" else func.sig.name
    let llvmFunc ← lowerFuncWithName func funcName
    CodegenM.withModuleBuilder (ModuleBuilder.addFunc llvmFunc)

  CodegenM.withModuleBuilder ModuleBuilder.getModule

/-- Generate LLVM IR from an Alloy module -/
def codegen (alloyModule : Module) (targetTriple : Option String := none) : LLVMModule :=
  let initState := CodegenM.init alloyModule.name targetTriple
  let (llvmModule, _) := Id.run (StateT.run (lowerModule alloyModule) initState)
  llvmModule

/-- Generate LLVM IR text from an Alloy module -/
def codegenToString (alloyModule : Module) (targetTriple : Option String := none) : String :=
  let llvmModule := codegen alloyModule targetTriple
  llvmModule.toLLVM

end Somac.Llvm.Codegen
