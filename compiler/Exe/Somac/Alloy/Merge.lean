import Somac.Alloy.Func
import Std.Data.HashMap

namespace Somac.Alloy.Merge

open Somac.Alloy

/-- Mapping from old IDs to new IDs during merge -/
structure IdRemap where
  /-- Module name → (old FuncId → new FuncId) -/
  funcMap : Std.HashMap String (Std.HashMap Nat Nat) := {}
  /-- Module name → (old GlobalId → new GlobalId) -/
  globalMap : Std.HashMap String (Std.HashMap Nat Nat) := {}
  deriving Inhabited

namespace IdRemap

def empty : IdRemap := {}

def addFuncMapping (r : IdRemap) (moduleName : String) (oldId newId : Nat) : IdRemap :=
  let moduleMap := r.funcMap.get? moduleName |>.getD {}
  { r with funcMap := r.funcMap.insert moduleName (moduleMap.insert oldId newId) }

def addGlobalMapping (r : IdRemap) (moduleName : String) (oldId newId : Nat) : IdRemap :=
  let moduleMap := r.globalMap.get? moduleName |>.getD {}
  { r with globalMap := r.globalMap.insert moduleName (moduleMap.insert oldId newId) }

def lookupFunc (r : IdRemap) (moduleName : String) (oldId : Nat) : Option Nat :=
  r.funcMap.get? moduleName |>.bind (·.get? oldId)

def lookupGlobal (r : IdRemap) (moduleName : String) (oldId : Nat) : Option Nat :=
  r.globalMap.get? moduleName |>.bind (·.get? oldId)

end IdRemap

/-- Rewrite FuncId references in an operand -/
def remapOperand (remap : IdRemap) (moduleName : String) (op : Operand) : Operand :=
  match op with
  | .func id =>
    match remap.lookupFunc moduleName id.id with
    | some newId => .func ⟨newId⟩
    | none => op
  | .global id =>
    match remap.lookupGlobal moduleName id.id with
    | some newId => .global ⟨newId⟩
    | none => op
  | _ => op

/-- Rewrite FuncId references in an instruction -/
def remapInst (remap : IdRemap) (moduleName : String) (inst : Inst) : Inst :=
  let remapOp := remapOperand remap moduleName
  let remapOps := fun ops => ops.map remapOp
  match inst with
  | .binOp op lhs rhs ty => .binOp op (remapOp lhs) (remapOp rhs) ty
  | .unOp op operand => .unOp op (remapOp operand)
  | .copy op => .copy (remapOp op)
  | .load ptr ty => .load (remapOp ptr) ty
  | .store ptr val => .store (remapOp ptr) (remapOp val)
  | .getFieldPtr base idx ty => .getFieldPtr (remapOp base) idx ty
  | .getElemPtr base idx ty => .getElemPtr (remapOp base) (remapOp idx) ty
  | .extractField val idx => .extractField (remapOp val) idx
  | .insertField val idx newVal => .insertField (remapOp val) idx (remapOp newVal)
  | .extractElem val idx => .extractElem (remapOp val) (remapOp idx)
  | .insertElem val idx newVal => .insertElem (remapOp val) (remapOp idx) (remapOp newVal)
  | .structLit fields ty => .structLit (remapOps fields) ty
  | .arrayLit elems ty => .arrayLit (remapOps elems) ty
  | .getTag val => .getTag (remapOp val)
  | .getPayload val variant field => .getPayload (remapOp val) variant field
  | .taggedLit tag payload ty => .taggedLit tag (remapOps payload) ty
  | .call funcId args retTy =>
    let newFuncId := match remap.lookupFunc moduleName funcId.id with
      | some newId => ⟨newId⟩
      | none => funcId
    .call newFuncId (remapOps args) retTy
  | .callPoly funcId typeArgs args retTy =>
    let newFuncId := match remap.lookupFunc moduleName funcId.id with
      | some newId => ⟨newId⟩
      | none => funcId
    .callPoly newFuncId typeArgs (remapOps args) retTy
  | .callIndirect ptr args retTy => .callIndirect (remapOp ptr) (remapOps args) retTy
  | .callClosure closure args retTy => .callClosure (remapOp closure) (remapOps args) retTy
  | .makeClosure funcId env =>
    let newFuncId := match remap.lookupFunc moduleName funcId.id with
      | some newId => ⟨newId⟩
      | none => funcId
    .makeClosure newFuncId (remapOp env)
  | .makeClosurePoly funcId typeArgs env =>
    let newFuncId := match remap.lookupFunc moduleName funcId.id with
      | some newId => ⟨newId⟩
      | none => funcId
    .makeClosurePoly newFuncId typeArgs (remapOp env)
  | .closureFunc closure => .closureFunc (remapOp closure)
  | .closureEnv closure => .closureEnv (remapOp closure)
  | .phi incoming ty =>
    .phi (incoming.map fun (op, blockId) => (remapOp op, blockId)) ty
  | .select cond thenVal elseVal =>
    .select (remapOp cond) (remapOp thenVal) (remapOp elseVal)
  | .memcpy dst src size => .memcpy (remapOp dst) (remapOp src) (remapOp size)
  | .memset dst val size => .memset (remapOp dst) (remapOp val) (remapOp size)
  | .clone src ty => .clone (remapOp src) ty
  | .erase val ty => .erase (remapOp val) ty
  | .intrinsic name args retTy => .intrinsic name (remapOps args) retTy
  | .malloc size => .malloc (remapOp size)
  | .free ptr => .free (remapOp ptr)
  | .alloca ty => inst
  | .panic msgIdx line => inst

/-- Rewrite FuncId references in a terminator -/
def remapTerminator (remap : IdRemap) (moduleName : String) (term : Terminator) : Terminator :=
  let remapOp := remapOperand remap moduleName
  match term with
  | .ret val => .ret (remapOp val)
  | .branch cond thenBlock elseBlock => .branch (remapOp cond) thenBlock elseBlock
  | .switch val cases default =>
    .switch (remapOp val) cases default
  | _ => term

/-- Rewrite FuncId references in a statement -/
def remapStmt (remap : IdRemap) (moduleName : String) (stmt : Stmt) : Stmt :=
  { stmt with inst := remapInst remap moduleName stmt.inst }

/-- Rewrite FuncId references in a block -/
def remapBlock (remap : IdRemap) (moduleName : String) (block : Block) : Block :=
  { block with
    stmts := block.stmts.map (remapStmt remap moduleName)
    terminator := remapTerminator remap moduleName block.terminator
  }

/-- Rewrite FuncId references in a CFG -/
def remapCFG (remap : IdRemap) (moduleName : String) (cfg : CFG) : CFG :=
  { cfg with
    blocks := cfg.blocks.fold (init := {}) fun acc id block =>
      acc.insert id (remapBlock remap moduleName block)
  }

/-- Rewrite FuncId references in a function -/
def remapFunc (remap : IdRemap) (moduleName : String) (func : Func) (newId : FuncId) (newName : String) : Func :=
  let newSig := { func.sig with name := newName }
  let newBody := func.body.map (remapCFG remap moduleName)
  let newSpecializedFrom := func.specializedFrom.bind fun oldId =>
    remap.lookupFunc moduleName oldId.id |>.map FuncId.mk
  { func with
    id := newId
    sig := newSig
    body := newBody
    specializedFrom := newSpecializedFrom
  }

/-- State for merging modules -/
structure MergeState where
  /-- The merged module being built -/
  result : Module
  /-- ID remapping for all modules -/
  remap : IdRemap
  /-- Next function ID -/
  nextFuncId : Nat := 0
  /-- Next global ID -/
  nextGlobalId : Nat := 0
  /-- Seen type definitions (by name) to avoid duplicates -/
  seenTypes : Std.HashMap String TypeDef := {}
  /-- Original function name → new qualified name (for finding main) -/
  funcNames : Std.HashMap String String := {}
  deriving Inhabited

namespace MergeState

def init (name : String) : MergeState :=
  { result := Module.empty name, remap := IdRemap.empty }

/-- Add a function to the merged module -/
def addFunc (s : MergeState) (moduleName : String) (func : Func) : MergeState :=
  let oldId := func.id.id
  let newId := s.nextFuncId
  let qualifiedName := s!"${moduleName}$${func.sig.name}"

  -- Update remap
  let remap' := s.remap.addFuncMapping moduleName oldId newId

  -- Will remap references after all functions are registered
  let newFunc : Func := { func with id := ⟨newId⟩, sig := { func.sig with name := qualifiedName } }

  { s with
    result := { s.result with
      funcs := s.result.funcs.push newFunc
      funcIndex := s.result.funcIndex.insert qualifiedName ⟨newId⟩
    }
    remap := remap'
    nextFuncId := newId + 1
    funcNames := s.funcNames.insert func.sig.name qualifiedName
  }

/-- Add a global to the merged module -/
def addGlobal (s : MergeState) (moduleName : String) (global : Global) : MergeState :=
  let oldId := global.id.id
  let newId := s.nextGlobalId
  let qualifiedName := s!"${moduleName}$${global.name}"

  let remap' := s.remap.addGlobalMapping moduleName oldId newId
  let newGlobal : Global := { global with id := ⟨newId⟩, name := qualifiedName }

  { s with
    result := { s.result with globals := s.result.globals.push newGlobal }
    remap := remap'
    nextGlobalId := newId + 1
  }

/-- Add a type definition (deduplicating by name) -/
def addTypeDef (s : MergeState) (td : TypeDef) : MergeState :=
  if s.seenTypes.contains td.name then s
  else
    { s with
      result := { s.result with types := s.result.types.push td }
      seenTypes := s.seenTypes.insert td.name td
    }

/-- Merge a string table entry, returning the new index -/
def internString (s : MergeState) (str : String) : Nat × MergeState :=
  let (idx, strings') := s.result.strings.intern str
  (idx, { s with result := { s.result with strings := strings' } })

end MergeState

/-- Register all functions and globals to build the ID remap -/
def registerModule (moduleName : String) (module : Module) (state : MergeState) : MergeState := Id.run do
  let mut s := state

  -- Register all functions
  for func in module.funcs do
    s := s.addFunc moduleName func

  -- Register all globals
  for global in module.globals do
    s := s.addGlobal moduleName global

  -- Register type definitions
  for td in module.types do
    s := s.addTypeDef td

  -- Merge string table
  for str in module.strings.strings do
    let (_, s') := s.internString str
    s := s'

  s

/-- Second pass: rewrite all references using the complete remap -/
def remapModule (moduleName : String) (state : MergeState) : MergeState := Id.run do
  let mut result := state.result

  let modulePrefix := s!"${moduleName}$$"

  -- Rewrite all functions that belong to this module
  let funcs := result.funcs.map fun func =>
    if func.sig.name.startsWith modulePrefix then
      remapFunc state.remap moduleName func func.id func.sig.name
    else
      func

  { state with result := { result with funcs := funcs } }

/-- Merge multiple Alloy modules into one -/
def merge (modules : Array (String × Module)) (outputName : String := "merged") : Module := Id.run do
  if modules.isEmpty then
    return Module.empty outputName

  if modules.size == 1 then
    -- Single module: just rename it
    let (_, m) := modules[0]!
    return { m with name := outputName }

  -- First pass: register everything
  let mut state := MergeState.init outputName
  for (name, module) in modules do
    state := registerModule name module state

  -- Second pass: rewrite references
  for (name, _) in modules do
    state := remapModule name state

  -- Set main function if any module has one
  let mut result := state.result
  for (name, module) in modules do
    if let some mainId := module.mainFunc then
      if let some newId := state.remap.lookupFunc name mainId.id then
        result := { result with mainFunc := some ⟨newId⟩ }
        break

  result

/-- Merge modules from a list -/
def mergeModules (modules : Array Module) (outputName : String := "merged") : Module :=
  let pairs := modules.map fun m => (m.name, m)
  merge pairs outputName

end Somac.Alloy.Merge
