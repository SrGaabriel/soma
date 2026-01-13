/-
  Alloy IR Monomorphization Pass

  This pass transforms a polymorphic Alloy IR module into a fully monomorphic one
  by specializing all polymorphic functions for their concrete type arguments.

  The algorithm works in three phases:

  1. **Discovery**: Traverse all call sites to find `callPoly` and `makeClosurePoly`
     instructions, collecting the required (FuncId, TypeArgs) specialization pairs.

  2. **Specialization**: For each unique specialization request:
     - Clone the polymorphic function
     - Substitute concrete types for type variables throughout
     - Generate a mangled name for the specialized version
     - Add to the module

  3. **Rewriting**: Replace all polymorphic calls with direct calls to the
     specialized versions, then remove unused polymorphic functions.

  After this pass, the module contains only monomorphic functions with no
  type variables, forall types, or polymorphic call instructions.
-/

import Soma.Alloy.Func
import Std.Data.HashMap
import Std.Data.HashSet

namespace Soma.Alloy.Monomorphize

open Soma.Alloy

/-! ## Type Hashing

We need to hash types for the specialization cache. Since `Ty` doesn't derive
`Hashable`, we implement a custom hash function.
-/

/-- Mix two hash values using a variant of the FNV technique -/
def mixHash (a b : UInt64) : UInt64 :=
  a ^^^ (b * 0x9e3779b97f4a7c15 + (a <<< (6 : UInt64)) + (a >>> (2 : UInt64)))

/-- Compute a hash for an Alloy type -/
partial def hashTy (ty : Ty) : UInt64 :=
  match ty with
  | .prim p => mixHash 1 (hash p)
  | .ptr t => mixHash 2 (hashTy t)
  | .rawPtr => 3
  | .funcPtr args ret =>
    let argsHash := args.foldl (init := (0 : UInt64)) fun acc t => mixHash acc (hashTy t)
    mixHash 4 (mixHash argsHash (hashTy ret))
  | .struct fields =>
    let fieldsHash := fields.foldl (init := (0 : UInt64)) fun acc (n, t) =>
      mixHash acc (mixHash (hash n) (hashTy t))
    mixHash 5 fieldsHash
  | .array elem size => mixHash 6 (mixHash (hashTy elem) (hash size))
  | .tagged tag variants =>
    let variantsHash := variants.foldl (init := (0 : UInt64)) fun acc (i, fields) =>
      let fieldsH := fields.foldl (init := hash i) fun a t => mixHash a (hashTy t)
      mixHash acc fieldsH
    mixHash 7 (mixHash (hashTy tag) variantsHash)
  | .closure args ret =>
    let argsHash := args.foldl (init := (0 : UInt64)) fun acc t => mixHash acc (hashTy t)
    mixHash 8 (mixHash argsHash (hashTy ret))
  | .tyVar id => mixHash 9 (hash id.idx)
  | .forall_ name body => mixHash 10 (mixHash (hash name) (hashTy body))
  | .tyApp func arg => mixHash 11 (mixHash (hashTy func) (hashTy arg))

/-- Compute a hash for an array of types -/
def hashTyArray (tys : Array Ty) : UInt64 :=
  tys.foldl (init := (0 : UInt64)) fun acc ty =>
    mixHash acc (hashTy ty)

/-- Key for the specialization cache: (original function ID, type arguments) -/
structure SpecKey where
  funcId : FuncId
  typeArgs : Array Ty
  deriving Inhabited

namespace SpecKey

def hash (k : SpecKey) : UInt64 :=
  let funcHash := Hashable.hash k.funcId.id
  let tyHash := hashTyArray k.typeArgs
  mixHash funcHash tyHash

def beq (a b : SpecKey) : Bool :=
  a.funcId == b.funcId && a.typeArgs == b.typeArgs

instance : BEq SpecKey := ⟨beq⟩
instance : Hashable SpecKey := ⟨hash⟩

def toString (k : SpecKey) : String :=
  let tyArgsStr := String.intercalate ", " (k.typeArgs.toList.map Ty.toStringAux)
  s!"{k.funcId}<{tyArgsStr}>"

instance : ToString SpecKey := ⟨toString⟩

end SpecKey

/-! ## Type Substitution

Apply a list of type arguments to substitute all type variables in types,
instructions, and functions.
-/

/-- Apply multiple type arguments to a type (for all forall-bound variables) -/
def applyTypeArgs (ty : Ty) (args : Array Ty) : Ty :=
  -- Type args are applied in order: first arg replaces tyVar 0, etc.
  -- But after each substitution, indices shift down.
  -- So we substitute from the innermost outward (reverse order).
  args.foldr (init := ty) fun arg acc => acc.substTyVar 0 arg

/-- Substitute type arguments into all types within an instruction -/
def substInstTypes (inst : Inst) (args : Array Ty) : Inst :=
  let subst := fun ty => applyTypeArgs ty args
  match inst with
  | .binOp op lhs rhs ty => .binOp op lhs rhs (subst ty)
  | .unOp op operand =>
    match op with
    | .trunc t => .unOp (.trunc t) operand
    | .zext t => .unOp (.zext t) operand
    | .sext t => .unOp (.sext t) operand
    | .itof t => .unOp (.itof t) operand
    | .ftoi t => .unOp (.ftoi t) operand
    | .bitcast t => .unOp (.bitcast (subst t)) operand
    | _ => inst
  | .copy src => .copy src
  | .alloca ty => .alloca (subst ty)
  | .malloc size => .malloc size
  | .free ptr => .free ptr
  | .load ptr ty => .load ptr (subst ty)
  | .store ptr val => .store ptr val
  | .getFieldPtr base idx structTy => .getFieldPtr base idx (subst structTy)
  | .getElemPtr base idx elemTy => .getElemPtr base idx (subst elemTy)
  | .extractField val idx => .extractField val idx
  | .insertField val idx newVal => .insertField val idx newVal
  | .extractElem val idx => .extractElem val idx
  | .insertElem val idx newVal => .insertElem val idx newVal
  | .structLit fields ty => .structLit fields (subst ty)
  | .arrayLit elems elemTy => .arrayLit elems (subst elemTy)
  | .getTag val => .getTag val
  | .getPayload val variant field => .getPayload val variant field
  | .taggedLit tag payload ty => .taggedLit tag payload (subst ty)
  | .call func callArgs retTy => .call func callArgs (subst retTy)
  | .callPoly func tyArgs callArgs retTy =>
    -- Substitute into the type args themselves, and into the return type
    .callPoly func (tyArgs.map subst) callArgs (subst retTy)
  | .callIndirect ptr callArgs retTy => .callIndirect ptr callArgs (subst retTy)
  | .callClosure closure callArgs retTy => .callClosure closure callArgs (subst retTy)
  | .makeClosurePoly func tyArgs env =>
    .makeClosurePoly func (tyArgs.map subst) env
  | .makeClosure func env => .makeClosure func env
  | .closureFunc closure => .closureFunc closure
  | .closureEnv closure => .closureEnv closure
  | .phi incoming ty => .phi incoming (subst ty)
  | .select cond thenVal elseVal => .select cond thenVal elseVal
  | .memcpy dst src size => .memcpy dst src size
  | .memset dst val size => .memset dst val size
  | .clone src ty => .clone src (subst ty)
  | .erase val ty => .erase val (subst ty)
  | .panic msgIdx line => .panic msgIdx line
  | .intrinsic name intrArgs retTy => .intrinsic name intrArgs (subst retTy)

/-- Substitute type arguments into a statement -/
def substStmtTypes (stmt : Stmt) (args : Array Ty) : Stmt :=
  { stmt with inst := substInstTypes stmt.inst args }

/-- Substitute type arguments into a block -/
def substBlockTypes (block : Block) (args : Array Ty) : Block :=
  let subst := fun ty => applyTypeArgs ty args
  { block with
    params := block.params.map fun (id, ty) => (id, subst ty)
    stmts := block.stmts.map fun s => substStmtTypes s args
  }

/-- Substitute type arguments into a CFG -/
def substCFGTypes (cfg : CFG) (args : Array Ty) : CFG :=
  let blocks' := cfg.blocks.fold (init := ({} : Std.HashMap Nat Block)) fun acc id block =>
    acc.insert id (substBlockTypes block args)
  { cfg with blocks := blocks' }

/-! ## Name Mangling

Generate unique names for specialized functions.
-/

/-- Mangle a type into a string suitable for function names -/
partial def mangleTy (ty : Ty) : String :=
  match ty with
  | .prim p =>
    match p with
    | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
    | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
    | .f32 => "f32" | .f64 => "f64" | .bool => "b" | .unit => "u"
  | .ptr t => s!"P{mangleTy t}"
  | .rawPtr => "Pv"
  | .funcPtr args ret =>
    let argsM := String.intercalate "" (args.toList.map mangleTy)
    s!"F{args.size}{argsM}{mangleTy ret}"
  | .struct fields =>
    let fieldsM := String.intercalate "" (fields.toList.map fun (_, t) => mangleTy t)
    s!"S{fields.size}{fieldsM}"
  | .array elem size => s!"A{size}{mangleTy elem}"
  | .tagged _ variants =>
    let count := variants.size
    s!"T{count}"
  | .closure args ret =>
    let argsM := String.intercalate "" (args.toList.map mangleTy)
    s!"C{args.size}{argsM}{mangleTy ret}"
  | .tyVar id => s!"V{id.idx}"
  | .forall_ _ body => s!"Q{mangleTy body}"
  | .tyApp func arg => s!"A{mangleTy func}{mangleTy arg}"

/-- Generate a mangled name for a specialized function -/
def mangleSpecName (baseName : String) (typeArgs : Array Ty) : String :=
  if typeArgs.isEmpty then baseName
  else
    let suffix := String.intercalate "_" (typeArgs.toList.map mangleTy)
    s!"{baseName}${suffix}"

/-! ## Discovery Phase

Find all polymorphic call sites and collect specialization requests.
-/

/-- A request to specialize a function with specific type arguments -/
structure SpecRequest where
  key : SpecKey
  /-- Source location for error reporting -/
  callSites : Array (FuncId × BlockId × Nat)  -- (function, block, stmt index)
  deriving Inhabited

/-- Extract specialization requests from an instruction -/
def collectInstRequests (inst : Inst) : Array SpecKey :=
  match inst with
  | .callPoly funcId typeArgs _ _ =>
    if typeArgs.all Ty.isMonomorphic then #[⟨funcId, typeArgs⟩] else #[]
  | .makeClosurePoly funcId typeArgs _ =>
    if typeArgs.all Ty.isMonomorphic then #[⟨funcId, typeArgs⟩] else #[]
  | _ => #[]

/-- Extract specialization requests from a block -/
def collectBlockRequests (block : Block) : Array SpecKey :=
  block.stmts.foldl (init := #[]) fun acc stmt =>
    acc ++ collectInstRequests stmt.inst

/-- Extract specialization requests from a function -/
def collectFuncRequests (func : Func) : Array SpecKey :=
  match func.body with
  | none => #[]
  | some cfg =>
    cfg.allBlocks.foldl (init := #[]) fun acc block =>
      acc ++ collectBlockRequests block

/-- Extract all specialization requests from a module -/
def collectModuleRequests (m : Module) : Array SpecKey :=
  m.funcs.foldl (init := #[]) fun acc func =>
    acc ++ collectFuncRequests func

/-! ## Specialization Phase

Clone and specialize polymorphic functions.
-/

/-- Specialize a function signature -/
def specializeSignature (sig : Signature) (typeArgs : Array Ty) : Signature :=
  let subst := fun ty => applyTypeArgs ty typeArgs
  { sig with
    name := mangleSpecName sig.name typeArgs
    typeParams := #[]  -- No longer polymorphic
    params := sig.params.map fun p => { p with ty := subst p.ty }
    retTy := subst sig.retTy
  }

/-- Specialize a function body -/
def specializeBody (cfg : CFG) (typeArgs : Array Ty) : CFG :=
  substCFGTypes cfg typeArgs

/-- Create a specialized version of a function -/
def specializeFunc (func : Func) (typeArgs : Array Ty) (newId : FuncId) : Func :=
  let newSig := specializeSignature func.sig typeArgs
  let newBody := func.body.map fun cfg => specializeBody cfg typeArgs
  let newLocalTypes := func.localTypes.fold
    (init := ({} : Std.HashMap Nat Ty)) fun acc id ty =>
      acc.insert id (applyTypeArgs ty typeArgs)
  { func with
    id := newId
    sig := newSig
    body := newBody
    specializedFrom := some func.id
    typeArgs := typeArgs
    localTypes := newLocalTypes
  }

/-! ## Rewriting Phase

Replace polymorphic calls with monomorphic ones.
-/

/-- Rewrite an instruction, replacing polymorphic calls with specialized versions -/
def rewriteInst (inst : Inst) (specMap : Std.HashMap SpecKey FuncId) : Inst :=
  match inst with
  | .callPoly funcId typeArgs args retTy =>
    let key : SpecKey := ⟨funcId, typeArgs⟩
    match specMap.get? key with
    | some newFuncId => .call newFuncId args retTy
    | none => inst  -- Keep as-is if not found (shouldn't happen for valid programs)
  | .makeClosurePoly funcId typeArgs env =>
    let key : SpecKey := ⟨funcId, typeArgs⟩
    match specMap.get? key with
    | some newFuncId => .makeClosure newFuncId env
    | none => inst
  | _ => inst

/-- Rewrite a statement -/
def rewriteStmt (stmt : Stmt) (specMap : Std.HashMap SpecKey FuncId) : Stmt :=
  { stmt with inst := rewriteInst stmt.inst specMap }

/-- Rewrite a block -/
def rewriteBlock (block : Block) (specMap : Std.HashMap SpecKey FuncId) : Block :=
  { block with stmts := block.stmts.map fun s => rewriteStmt s specMap }

/-- Rewrite a CFG -/
def rewriteCFG (cfg : CFG) (specMap : Std.HashMap SpecKey FuncId) : CFG :=
  let blocks' := cfg.blocks.fold (init := ({} : Std.HashMap Nat Block)) fun acc id block =>
    acc.insert id (rewriteBlock block specMap)
  { cfg with blocks := blocks' }

/-- Rewrite a function -/
def rewriteFunc (func : Func) (specMap : Std.HashMap SpecKey FuncId) : Func :=
  match func.body with
  | none => func
  | some cfg => { func with body := some (rewriteCFG cfg specMap) }

/-! ## Monomorphization State -/

/-- State for the monomorphization pass -/
structure MonoState where
  /-- The module being transformed -/
  module : Module
  /-- Map from specialization key to specialized function ID -/
  specMap : Std.HashMap SpecKey FuncId := {}
  /-- Set of keys we've already processed (to avoid duplicates) -/
  processed : Std.HashSet SpecKey := {}
  /-- Work list of pending specializations -/
  pending : Array SpecKey := #[]
  /-- Next available function ID -/
  nextFuncId : Nat
  deriving Inhabited

namespace MonoState

/-- Initialize state from a module -/
def init (m : Module) : MonoState :=
  { module := m
  , nextFuncId := m.funcs.size
  }

/-- Allocate a fresh function ID -/
def freshFuncId (s : MonoState) : FuncId × MonoState :=
  (⟨s.nextFuncId⟩, { s with nextFuncId := s.nextFuncId + 1 })

/-- Add a specialization request to the work list if not already processed -/
def addRequest (s : MonoState) (key : SpecKey) : MonoState :=
  if s.processed.contains key || s.specMap.contains key then s
  else { s with pending := s.pending.push key }

/-- Add multiple requests -/
def addRequests (s : MonoState) (keys : Array SpecKey) : MonoState :=
  keys.foldl (init := s) fun acc key => acc.addRequest key

/-- Mark a key as processed and record its specialized function ID -/
def recordSpecialization (s : MonoState) (key : SpecKey) (funcId : FuncId) : MonoState :=
  { s with
    specMap := s.specMap.insert key funcId
    processed := s.processed.insert key
  }

/-- Pop the next pending request -/
def popPending (s : MonoState) : Option (SpecKey × MonoState) :=
  if s.pending.isEmpty then none
  else
    let key := s.pending.back!
    some (key, { s with pending := s.pending.pop })

/-- Add a specialized function to the module -/
def addFunc (s : MonoState) (func : Func) : MonoState :=
  { s with module := s.module.addFunc func }

end MonoState

/-! ## Main Algorithm -/

/-- Process one specialization request -/
def processRequest (key : SpecKey) : StateM MonoState Unit := do
  let s ← get

  -- Look up the original function
  let some origFunc := s.module.getFunc key.funcId
    | return ()  -- Function not found, skip

  -- Only specialize if it's actually polymorphic
  if !origFunc.isPolymorphic then return ()

  -- Verify type args match the function's type parameters
  if key.typeArgs.size != origFunc.numTypeParams then return ()

  -- Allocate a new function ID
  let (newFuncId, s') := s.freshFuncId
  set s'

  -- Create the specialized function
  let specializedFunc := specializeFunc origFunc key.typeArgs newFuncId

  -- Record the specialization
  modify fun s => s.recordSpecialization key newFuncId

  -- Add the specialized function to the module
  modify fun s => s.addFunc specializedFunc

  -- The specialized function may itself contain polymorphic calls
  -- We need to collect and add those to the work list
  let newRequests := collectFuncRequests specializedFunc
  modify fun s => s.addRequests newRequests

/-- Process all pending specialization requests (fixed-point iteration) -/
partial def processAllRequests : StateM MonoState Unit := do
  let s ← get
  match s.popPending with
  | none => return ()  -- No more work
  | some (key, s') =>
    set s'
    processRequest key
    processAllRequests

/-- Rewrite all functions to use specialized versions -/
def rewriteAllFuncs : StateM MonoState Unit := do
  let s ← get
  let specMap := s.specMap
  let newFuncs := s.module.funcs.map fun f => rewriteFunc f specMap
  set { s with module := { s.module with funcs := newFuncs } }

/-- Check if a function is used (has any callers or is main) -/
def isUsed (m : Module) (funcId : FuncId) : Bool :=
  -- Main function is always used
  if m.mainFunc == some funcId then true
  else
    -- Check if any function calls this one
    m.funcs.any fun f =>
      match f.body with
      | none => false
      | some cfg =>
        cfg.allBlocks.any fun block =>
          block.stmts.any fun stmt =>
            match stmt.inst with
            | .call fid _ _ => fid == funcId
            | .makeClosure fid _ => fid == funcId
            | _ => false

/-- Remap function reference -/
def remapFuncRef (fid : FuncId) (idMap : Std.HashMap Nat Nat) : FuncId :=
  match idMap.get? fid.id with
  | some newId => ⟨newId⟩
  | none => fid

/-- Remap function references in an instruction -/
def remapInstRefs (inst : Inst) (idMap : Std.HashMap Nat Nat) : Inst :=
  match inst with
  | .call fid args retTy => .call (remapFuncRef fid idMap) args retTy
  | .callPoly fid tyArgs args retTy => .callPoly (remapFuncRef fid idMap) tyArgs args retTy
  | .makeClosure fid env => .makeClosure (remapFuncRef fid idMap) env
  | .makeClosurePoly fid tyArgs env => .makeClosurePoly (remapFuncRef fid idMap) tyArgs env
  | _ => inst

/-- Remap function references in a function -/
def remapFuncRefs (f : Func) (idMap : Std.HashMap Nat Nat) : Func :=
  match f.body with
  | none => f
  | some cfg =>
    let newBlocks := cfg.blocks.fold
      (init := ({} : Std.HashMap Nat Block)) fun acc id block =>
        let newStmts := block.stmts.map fun s =>
          { s with inst := remapInstRefs s.inst idMap }
        acc.insert id { block with stmts := newStmts }
    { f with
      body := some { cfg with blocks := newBlocks }
      specializedFrom := f.specializedFrom.bind fun fid =>
        idMap.get? fid.id |>.map FuncId.mk
    }

/-- Renumber functions and return the mapping -/
def renumberFuncs (funcs : Array Func) : Array Func × Std.HashMap Nat Nat :=
  let (arr, mapPair) := funcs.foldl (init := (#[], ({} : Std.HashMap Nat Nat), 0))
    fun (arr, map, idx) f =>
      let newF := { f with id := ⟨idx⟩ }
      (arr.push newF, map.insert f.id.id idx, idx + 1)
  (arr, mapPair.1)

/-- Remove polymorphic functions that have been fully specialized -/
def removeUnusedPolymorphic : StateM MonoState Unit := do
  let s ← get
  -- Keep functions that are:
  -- 1. Not polymorphic, OR
  -- 2. Still have polymorphic call sites (callPoly), OR
  -- 3. Are used (called directly or are main)
  let keepFunc := fun (f : Func) =>
    !f.isPolymorphic || isUsed s.module f.id

  let keptFuncs := s.module.funcs.filter keepFunc

  -- Renumber function IDs to be contiguous
  let (newFuncs, idMap) := renumberFuncs keptFuncs

  -- Update function index
  let newFuncIndex := newFuncs.foldl
    (init := ({} : Std.HashMap String FuncId)) fun acc f =>
      acc.insert f.sig.name f.id

  -- Update references in the kept functions
  let finalFuncs := newFuncs.map fun f => remapFuncRefs f idMap

  -- Update main function reference
  let newMain := s.module.mainFunc.bind fun oldId => idMap.get? oldId.id |>.map FuncId.mk

  set { s with module := {
    s.module with
    funcs := finalFuncs
    funcIndex := newFuncIndex
    mainFunc := newMain
  }}

/-! ## Entry Point -/

/-- Run the monomorphization pass on a module -/
def monomorphize (m : Module) : Module :=
  -- Initialize state
  let initState := MonoState.init m

  -- Collect initial specialization requests from the whole module
  let initialRequests := collectModuleRequests m

  -- Add all requests to the work list
  let stateWithRequests := initState.addRequests initialRequests

  -- Process all requests (fixed-point)
  let ((), stateAfterSpec) := Id.run (StateT.run processAllRequests stateWithRequests)

  -- Rewrite all functions to use specialized versions
  let ((), stateAfterRewrite) := Id.run (StateT.run rewriteAllFuncs stateAfterSpec)

  -- Remove unused polymorphic functions
  let ((), finalState) := Id.run (StateT.run removeUnusedPolymorphic stateAfterRewrite)

  finalState.module

/-! ## Verification -/

/-- Check if a module is fully monomorphic -/
def isFullyMonomorphic (m : Module) : Bool :=
  m.funcs.all fun f =>
    -- No type parameters
    f.sig.typeParams.isEmpty &&
    -- All types in signature are monomorphic
    f.sig.params.all (·.ty.isMonomorphic) &&
    f.sig.retTy.isMonomorphic &&
    -- No polymorphic calls in body
    match f.body with
    | none => true
    | some cfg =>
      cfg.allBlocks.all fun block =>
        block.stmts.all fun stmt =>
          match stmt.inst with
          | .callPoly _ _ _ _ => false
          | .makeClosurePoly _ _ _ => false
          | _ => true

/-- Report any remaining polymorphism (for debugging) -/
def reportPolymorphism (m : Module) : Array String :=
  m.funcs.foldl (init := #[]) fun acc f =>
    let funcIssues := Id.run do
      let mut issues : Array String := #[]

      if !f.sig.typeParams.isEmpty then
        issues := issues.push s!"Function {f.sig.name} has type parameters: {f.sig.typeParams}"

      for p in f.sig.params do
        if !p.ty.isMonomorphic then
          issues := issues.push s!"Function {f.sig.name} param {p.name} has polymorphic type: {p.ty}"

      if !f.sig.retTy.isMonomorphic then
        issues := issues.push s!"Function {f.sig.name} has polymorphic return type: {f.sig.retTy}"

      if let some cfg := f.body then
        for block in cfg.allBlocks do
          for stmt in block.stmts do
            match stmt.inst with
            | .callPoly funcId typeArgs _ _ =>
              issues := issues.push s!"Function {f.sig.name} has callPoly to {funcId} with {typeArgs}"
            | .makeClosurePoly funcId typeArgs _ =>
              issues := issues.push s!"Function {f.sig.name} has makeClosurePoly to {funcId} with {typeArgs}"
            | _ => pure ()

      pure issues

    acc ++ funcIssues

end Soma.Alloy.Monomorphize
