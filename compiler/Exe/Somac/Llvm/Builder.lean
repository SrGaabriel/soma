import Somac.Llvm.Types
import Std.Data.HashMap

namespace Somac.Llvm.Builder

open Somac.Llvm

/-- State for building an LLVM function -/
structure FuncBuilderState where
  /-- Next available local ID -/
  nextLocalId : Nat := 0
  /-- Next available block ID -/
  nextBlockId : Nat := 0
  /-- Current block being built -/
  currentBlock : Option Label := none
  /-- Statements in the current block in reverse order -/
  currentStmts : Array LLVMStmt := #[]
  /-- Completed blocks -/
  blocks : Array LLVMBlock := #[]
  /-- Block order (for deterministic output) -/
  blockOrder : Array Label := #[]
  /-- LLVM types for each local SSA value, keyed by LocalRef id -/
  localTypes : Std.HashMap Nat LLVMType := {}
  deriving Inhabited

/-- State for building an LLVM module -/
structure ModuleBuilderState where
  /-- Module being built -/
  module : LLVMModule
  /-- Function name to index mapping -/
  funcIndex : Std.HashMap String Nat := {}
  /-- Global name to index mapping -/
  globalIndex : Std.HashMap String Nat := {}
  /-- Type name to index mapping -/
  typeIndex : Std.HashMap String Nat := {}
  /-- String table for string literals -/
  stringTable : Array String := #[]
  /-- String to global name mapping -/
  stringIndex : Std.HashMap String String := {}
  deriving Inhabited

/-- Monad for building a single function -/
abbrev FuncBuilder := StateM FuncBuilderState

namespace FuncBuilder

/-- Allocate a fresh local reference -/
def freshLocal : FuncBuilder LocalRef := do
  let s ← get
  let ref := LocalRef.mk s.nextLocalId
  set { s with nextLocalId := s.nextLocalId + 1 }
  pure ref

/-- Allocate a fresh block label -/
def freshLabel (labelPrefix : String := "bb") : FuncBuilder Label := do
  let s ← get
  let label := Label.mk s!"{labelPrefix}{s.nextBlockId}"
  set { s with nextBlockId := s.nextBlockId + 1 }
  pure label

/-- Start a new basic block -/
def startBlock (label : Label) : FuncBuilder Unit := do
  let s ← get
  -- Finish current block if any (without terminator, will error if not terminated properly)
  set { s with
    currentBlock := some label
    currentStmts := #[]
    blockOrder := s.blockOrder.push label
  }

/-- Emit an instruction with a result -/
def emit (inst : LLVMInst) : FuncBuilder LocalRef := do
  let ref ← freshLocal
  let stmt := LLVMStmt.mk (some ref) inst
  modify fun s =>
    let s := { s with currentStmts := s.currentStmts.push stmt }
    match inst.instResultTy with
    | some ty => { s with localTypes := s.localTypes.insert ref.id ty }
    | none => s
  pure ref

/-- Look up the LLVM type of a local SSA value -/
def getLocalType (ref : LocalRef) : FuncBuilder (Option LLVMType) := do
  let s ← get
  pure (s.localTypes.get? ref.id)

/-- Emit a void instruction (no result) -/
def emitVoid (inst : LLVMInst) : FuncBuilder Unit := do
  let stmt := LLVMStmt.mk none inst
  modify fun s => { s with currentStmts := s.currentStmts.push stmt }

/-- Terminate the current block -/
def terminate (term : LLVMTerminator) : FuncBuilder Unit := do
  let s ← get
  match s.currentBlock with
  | some label =>
    let block : LLVMBlock := {
      label := label
      stmts := s.currentStmts
      terminator := term
    }
    set { s with
      blocks := s.blocks.push block
      currentBlock := none
      currentStmts := #[]
    }
  | none => pure () -- No current block to terminate

/-- Get all built blocks -/
def getBlocks : FuncBuilder (Array LLVMBlock) := do
  let s ← get
  pure s.blocks

/-- Get the current block label -/
def getCurrentLabel : FuncBuilder (Option Label) := do
  let s ← get
  pure s.currentBlock

end FuncBuilder

/-- Monad for building a module -/
abbrev ModuleBuilder := StateM ModuleBuilderState

namespace ModuleBuilder

/-- Initialize a module builder -/
def init (name : String) (triple : Option String := none) (dataLayout : Option String := none)
    : ModuleBuilderState :=
  { module := {
      name := name
      targetTriple := triple
      dataLayout := dataLayout
    }
  }

/-- Add a type definition -/
def addType (name : String) (fields : Array LLVMType) (packed : Bool := false)
    : ModuleBuilder Unit := do
  let s ← get
  if s.typeIndex.contains name then return ()
  let idx := s.module.types.size
  let typedef : LLVMTypeDef := { name, fields, packed }
  set { s with
    module := { s.module with types := s.module.types.push typedef }
    typeIndex := s.typeIndex.insert name idx
  }

/-- Add a global variable -/
def addGlobal (g : LLVMGlobal) : ModuleBuilder Unit := do
  let s ← get
  let idx := s.module.globals.size
  set { s with
    module := { s.module with globals := s.module.globals.push g }
    globalIndex := s.globalIndex.insert g.name idx
  }

/-- Add a function -/
def addFunc (f : LLVMFunc) : ModuleBuilder Unit := do
  let s ← get
  let idx := s.module.funcs.size
  set { s with
    module := { s.module with funcs := s.module.funcs.push f }
    funcIndex := s.funcIndex.insert f.name idx
  }

/-- Intern a string literal, returning the global name -/
def internString (s : String) : ModuleBuilder String := do
  let st ← get
  match st.stringIndex.get? s with
  | some name => pure name
  | none =>
    let idx := st.stringTable.size
    let name := s!".str.{idx}"
    -- Create global constant for the string
    let strBytes := s.utf8ByteSize + 1 -- +1 for null terminator
    let global : LLVMGlobal := {
      name := name
      ty := .array strBytes .i8
      init := some (.string s)
      linkage := .private_
      isConstant := true
      align := some 1
    }
    set { st with
      stringTable := st.stringTable.push s
      stringIndex := st.stringIndex.insert s name
      module := { st.module with globals := st.module.globals.push global }
    }
    pure name

/-- Get the built module -/
def getModule : ModuleBuilder LLVMModule := do
  let s ← get
  pure s.module

end ModuleBuilder

namespace FuncBuilder

/-- Add two integers -/
def add (ty : LLVMType) (lhs rhs : LLVMValue) (nuw nsw : Bool := false)
    : FuncBuilder LocalRef :=
  emit (.add nuw nsw ty lhs rhs)

/-- Subtract two integers -/
def sub (ty : LLVMType) (lhs rhs : LLVMValue) (nuw nsw : Bool := false)
    : FuncBuilder LocalRef :=
  emit (.sub nuw nsw ty lhs rhs)

/-- Multiply two integers -/
def mul (ty : LLVMType) (lhs rhs : LLVMValue) (nuw nsw : Bool := false)
    : FuncBuilder LocalRef :=
  emit (.mul nuw nsw ty lhs rhs)

/-- Unsigned divide -/
def udiv (ty : LLVMType) (lhs rhs : LLVMValue) (exact : Bool := false)
    : FuncBuilder LocalRef :=
  emit (.udiv exact ty lhs rhs)

/-- Signed divide -/
def sdiv (ty : LLVMType) (lhs rhs : LLVMValue) (exact : Bool := false)
    : FuncBuilder LocalRef :=
  emit (.sdiv exact ty lhs rhs)

/-- Unsigned remainder -/
def urem (ty : LLVMType) (lhs rhs : LLVMValue) : FuncBuilder LocalRef :=
  emit (.urem ty lhs rhs)

/-- Signed remainder -/
def srem (ty : LLVMType) (lhs rhs : LLVMValue) : FuncBuilder LocalRef :=
  emit (.srem ty lhs rhs)

/-- Floating point add -/
def fadd (ty : LLVMType) (lhs rhs : LLVMValue) : FuncBuilder LocalRef :=
  emit (.fadd ty lhs rhs)

/-- Floating point subtract -/
def fsub (ty : LLVMType) (lhs rhs : LLVMValue) : FuncBuilder LocalRef :=
  emit (.fsub ty lhs rhs)

/-- Floating point multiply -/
def fmul (ty : LLVMType) (lhs rhs : LLVMValue) : FuncBuilder LocalRef :=
  emit (.fmul ty lhs rhs)

/-- Floating point divide -/
def fdiv (ty : LLVMType) (lhs rhs : LLVMValue) : FuncBuilder LocalRef :=
  emit (.fdiv ty lhs rhs)

/-- Floating point remainder -/
def frem (ty : LLVMType) (lhs rhs : LLVMValue) : FuncBuilder LocalRef :=
  emit (.frem ty lhs rhs)

/-- Floating point negate -/
def fneg (ty : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.fneg ty val)

/-- Left shift -/
def shl (ty : LLVMType) (lhs rhs : LLVMValue) (nuw nsw : Bool := false)
    : FuncBuilder LocalRef :=
  emit (.shl nuw nsw ty lhs rhs)

/-- Logical right shift -/
def lshr (ty : LLVMType) (lhs rhs : LLVMValue) (exact : Bool := false)
    : FuncBuilder LocalRef :=
  emit (.lshr exact ty lhs rhs)

/-- Arithmetic right shift -/
def ashr (ty : LLVMType) (lhs rhs : LLVMValue) (exact : Bool := false)
    : FuncBuilder LocalRef :=
  emit (.ashr exact ty lhs rhs)

/-- Bitwise AND -/
def and_ (ty : LLVMType) (lhs rhs : LLVMValue) : FuncBuilder LocalRef :=
  emit (.and_ ty lhs rhs)

/-- Bitwise OR -/
def or_ (ty : LLVMType) (lhs rhs : LLVMValue) : FuncBuilder LocalRef :=
  emit (.or_ ty lhs rhs)

/-- Bitwise XOR -/
def xor_ (ty : LLVMType) (lhs rhs : LLVMValue) : FuncBuilder LocalRef :=
  emit (.xor_ ty lhs rhs)

/-- Integer comparison -/
def icmp (pred : ICmpPred) (ty : LLVMType) (lhs rhs : LLVMValue)
    : FuncBuilder LocalRef :=
  emit (.icmp pred ty lhs rhs)

/-- Floating point comparison -/
def fcmp (pred : FCmpPred) (ty : LLVMType) (lhs rhs : LLVMValue)
    : FuncBuilder LocalRef :=
  emit (.fcmp pred ty lhs rhs)

/-- Truncate to smaller type -/
def trunc (fromTy toTy : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.trunc fromTy toTy val)

/-- Zero-extend to larger type -/
def zext (fromTy toTy : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.zext fromTy toTy val)

/-- Sign-extend to larger type -/
def sext (fromTy toTy : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.sext fromTy toTy val)

/-- Float truncate -/
def fptrunc (fromTy toTy : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.fptrunc fromTy toTy val)

/-- Float extend -/
def fpext (fromTy toTy : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.fpext fromTy toTy val)

/-- Float to unsigned int -/
def fptoui (fromTy toTy : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.fptoui fromTy toTy val)

/-- Float to signed int -/
def fptosi (fromTy toTy : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.fptosi fromTy toTy val)

/-- Unsigned int to float -/
def uitofp (fromTy toTy : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.uitofp fromTy toTy val)

/-- Signed int to float -/
def sitofp (fromTy toTy : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.sitofp fromTy toTy val)

/-- Pointer to integer -/
def ptrtoint (toTy : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.ptrtoint .ptr toTy val)

/-- Integer to pointer -/
def inttoptr (fromTy : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.inttoptr fromTy .ptr val)

/-- Bitcast (reinterpret bits) -/
def bitcast (fromTy toTy : LLVMType) (val : LLVMValue) : FuncBuilder LocalRef :=
  emit (.bitcast fromTy toTy val)

/-- Allocate stack space -/
def alloca (ty : LLVMType) (align : Option Nat := none) : FuncBuilder LocalRef :=
  emit (.alloca ty none align)

/-- Allocate array on stack -/
def allocaArray (ty : LLVMType) (numElems : LLVMValue) (align : Option Nat := none)
    : FuncBuilder LocalRef :=
  emit (.alloca ty (some numElems) align)

/-- Load from pointer -/
def load (ty : LLVMType) (ptr : LLVMValue) (align : Option Nat := none)
    : FuncBuilder LocalRef :=
  emit (.load ty ptr align)

/-- Store to pointer -/
def store (ty : LLVMType) (val ptr : LLVMValue) (align : Option Nat := none)
    : FuncBuilder Unit :=
  emitVoid (.store ty val ptr align)

/-- Get element pointer -/
def gep (baseTy : LLVMType) (ptr : LLVMValue) (indices : Array (LLVMType × LLVMValue))
    (inbounds : Bool := true) : FuncBuilder LocalRef :=
  emit (.getelementptr inbounds baseTy ptr indices)

/-- Get element pointer with i32 indices -/
def gepi32 (baseTy : LLVMType) (ptr : LLVMValue) (indices : Array Int)
    (inbounds : Bool := true) : FuncBuilder LocalRef :=
  let idxVals := indices.map fun i => (.i32, LLVMValue.intConst i 32)
  emit (.getelementptr inbounds baseTy ptr idxVals)

/-- Get element pointer with i64 indices -/
def gepi64 (baseTy : LLVMType) (ptr : LLVMValue) (indices : Array Int)
    (inbounds : Bool := true) : FuncBuilder LocalRef :=
  let idxVals := indices.map fun i => (.i64, LLVMValue.intConst i 64)
  emit (.getelementptr inbounds baseTy ptr idxVals)

/-- Extract value from aggregate -/
def extractvalue (aggTy : LLVMType) (agg : LLVMValue) (indices : Array Nat)
    : FuncBuilder LocalRef :=
  emit (.extractvalue aggTy agg indices)

/-- Insert value into aggregate -/
def insertvalue (aggTy : LLVMType) (agg val : LLVMValue) (indices : Array Nat)
    : FuncBuilder LocalRef :=
  emit (.insertvalue aggTy agg val indices)

/-- Call a function -/
def call (retTy : LLVMType) (func : LLVMValue) (args : Array (LLVMType × LLVMValue))
    (tailcall : Bool := false) (callconv : Option CallConv := none)
    : FuncBuilder LocalRef :=
  emit (.call tailcall callconv retTy func args)

/-- Call a void function -/
def callVoid (func : LLVMValue) (args : Array (LLVMType × LLVMValue))
    (tailcall : Bool := false) (callconv : Option CallConv := none)
    : FuncBuilder Unit :=
  emitVoid (.call tailcall callconv .void func args)

/-- Call a function by name -/
def callNamed (retTy : LLVMType) (name : String) (args : Array (LLVMType × LLVMValue))
    (tailcall : Bool := false) : FuncBuilder LocalRef :=
  call retTy (.global ⟨name⟩) args tailcall

/-- Call a void function by name -/
def callNamedVoid (name : String) (args : Array (LLVMType × LLVMValue))
    (tailcall : Bool := false) : FuncBuilder Unit :=
  callVoid (.global ⟨name⟩) args tailcall

/-- Select between two values based on condition -/
def select (resTy : LLVMType) (cond thenVal elseVal : LLVMValue)
    : FuncBuilder LocalRef :=
  emit (.select .i1 resTy cond thenVal elseVal)

/-- Phi node -/
def phi (ty : LLVMType) (incoming : Array (LLVMValue × Label))
    : FuncBuilder LocalRef :=
  emit (.phi ty incoming)

/-- Memory copy -/
def memcpy (dst src len : LLVMValue) (align : Nat := 1) (isVolatile : Bool := false)
    : FuncBuilder Unit :=
  emitVoid (.memcpy dst src len align isVolatile)

/-- Memory set -/
def memset (dst val len : LLVMValue) (align : Nat := 1) (isVolatile : Bool := false)
    : FuncBuilder Unit :=
  emitVoid (.memset dst val len align isVolatile)

/-- Memory move -/
def memmove (dst src len : LLVMValue) (align : Nat := 1) (isVolatile : Bool := false)
    : FuncBuilder Unit :=
  emitVoid (.memmove dst src len align isVolatile)

/-- Return a value -/
def ret (ty : LLVMType) (val : LLVMValue) : FuncBuilder Unit :=
  terminate (.ret ty (some val))

/-- Return void -/
def retVoid : FuncBuilder Unit :=
  terminate (.ret .void none)

/-- Unconditional branch -/
def br (target : Label) : FuncBuilder Unit :=
  terminate (.br target)

/-- Conditional branch -/
def condBr (cond : LLVMValue) (thenLabel elseLabel : Label) : FuncBuilder Unit :=
  terminate (.condBr cond thenLabel elseLabel)

/-- Switch statement -/
def switch (ty : LLVMType) (val : LLVMValue) (default : Label)
    (cases : Array (LLVMConst × Label)) : FuncBuilder Unit :=
  terminate (.switch ty val default cases)

/-- Unreachable terminator -/
def unreachable : FuncBuilder Unit :=
  terminate .unreachable

end FuncBuilder

/-- Convert a LocalRef to an LLVMValue -/
def localVal (ref : LocalRef) : LLVMValue := .local ref

/-- Create an integer constant value -/
def intVal (val : Int) (bits : Nat := 64) : LLVMValue := .const (.int val bits)

/-- Create an i32 constant -/
def i32Val (val : Int) : LLVMValue := .const (.int val 32)

/-- Create an i64 constant -/
def i64Val (val : Int) : LLVMValue := .const (.int val 64)

/-- Create a boolean constant -/
def boolVal (val : Bool) : LLVMValue := .const (.bool val)

/-- Create a null pointer constant -/
def nullVal : LLVMValue := .const .null

/-- Create a global reference -/
def globalVal (name : String) : LLVMValue := .global ⟨name⟩

/-- Create a function reference -/
def funcVal (name : String) : LLVMValue := .global ⟨name⟩

/-- Build a function -/
def buildFunc (name : String) (retTy : LLVMType) (params : Array LLVMParam)
    (attrs : LLVMFuncAttrs := {})
    (builder : FuncBuilder Unit) : LLVMFunc :=
  let ((), state) := Id.run (StateT.run builder {})
  { name, retTy, params, attrs, blocks := state.blocks, isDeclaration := false }

/-- Build a function with entry block -/
def buildFuncWithEntry (name : String) (retTy : LLVMType) (params : Array LLVMParam)
    (attrs : LLVMFuncAttrs := {})
    (builder : FuncBuilder Unit) : LLVMFunc :=
  let initState : FuncBuilderState := {
    currentBlock := some ⟨"entry"⟩
    blockOrder := #[⟨"entry"⟩]
  }
  let ((), state) := Id.run (StateT.run builder initState)
  { name, retTy, params, attrs, blocks := state.blocks, isDeclaration := false }

end Somac.Llvm.Builder
