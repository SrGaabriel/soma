import Somac.Alloy.Func
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Alloy.Monomorphize

open Somac.Alloy

/-- Key for the specialization cache -/
structure SpecKey where
  funcId : FuncId
  typeArgs : Array ClosedTy
  deriving Inhabited

namespace SpecKey

def hash (k : SpecKey) : UInt64 :=
  let funcHash := Hashable.hash k.funcId.id
  let tyHash := hashClosedTyArray k.typeArgs
  mixHash funcHash tyHash

def beq (a b : SpecKey) : Bool :=
  a.funcId == b.funcId && a.typeArgs.size == b.typeArgs.size &&
  (List.zip a.typeArgs.toList b.typeArgs.toList).all fun (x, y) => Ty.beq x y

instance : BEq SpecKey := ⟨beq⟩
instance : Hashable SpecKey := ⟨hash⟩

def toString (k : SpecKey) : String :=
  let tyArgsStr := String.intercalate ", " (k.typeArgs.toList.map Ty.toString)
  s!"{k.funcId}<{tyArgsStr}>"

instance : ToString SpecKey := ⟨toString⟩

end SpecKey

/-- Mangle a closed type into a string suitable for function names -/
partial def mangleTy (ty : ClosedTy) : String :=
  match ty with
  | .prim p =>
      match p with
      | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
      | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
      | .f32 => "f32" | .f64 => "f64" | .bool => "b" | .unit => "u" | .world => "w"
  | .ptr t => s!"P{mangleTy t}"
  | .rawPtr => "Pv"
  | .funcPtr args ret =>
      let argsM := String.intercalate "" (args.toList.map mangleTy)
      s!"F{args.size}{argsM}{mangleTy ret}"
  | .struct fields =>
      let fieldsM := String.intercalate "" (fields.toList.map fun (_, t) => mangleTy t)
      s!"S{fields.size}{fieldsM}"
  | .array elem size => s!"A{size}{mangleTy elem}"
  | .tagged tagTy variants =>
      let variantsM := String.intercalate "" (variants.toList.map fun (idx, fields) =>
        let fieldsM := String.intercalate "" (fields.toList.map mangleTy)
        s!"{idx}_{fields.size}{fieldsM}")
      s!"T{mangleTy tagTy}{variants.size}{variantsM}"
  | .closure args ret =>
      let argsM := String.intercalate "" (args.toList.map mangleTy)
      s!"C{args.size}{argsM}{mangleTy ret}"
  | .var i => nomatch i -- impossible

/-- Generate a mangled name for a specialized function -/
def mangleSpecName (baseName : String) (typeArgs : Array ClosedTy) : String :=
  if typeArgs.isEmpty then baseName
  else
    let suffix := String.intercalate "_" (typeArgs.toList.map mangleTy)
    s!"{baseName}${suffix}"

/-! ## Discovery Phase

Find all polymorphic call sites and collect specialization requests.
-/

/-- Extract specialization keys from a closed instruction -/
def collectInstRequests : ClosedInst → Array SpecKey
  | .callPoly funcId typeArgs _ _ => #[⟨funcId, typeArgs⟩]
  | .callExternPoly _ _ _ _ =>
      #[]
  | .makeClosurePoly funcRef typeArgs _ =>
      match funcRef with
      | .local funcId => #[⟨funcId, typeArgs⟩]
      | _ => #[]
  | _ => #[]

/-- Extract specialization keys from a closed block -/
def collectBlockRequests (block : ClosedBlock) : Array SpecKey :=
  block.stmts.foldl (init := #[]) fun acc stmt =>
    acc ++ collectInstRequests stmt.inst

/-- Extract specialization keys from a closed function -/
def collectFuncRequests (func : ClosedFunc) : Array SpecKey :=
  match func.body with
  | none => #[]
  | some cfg =>
    cfg.allBlocks.foldl (init := #[]) fun acc block =>
      acc ++ collectBlockRequests block

/-- Extract all specialization keys from a module -/
def collectModuleRequests (m : Module) : Array SpecKey :=
  m.funcs.foldl (init := #[]) fun acc sf =>
    match sf.asMono? with
    | some f => acc ++ collectFuncRequests f
    | none => acc

/-- Rewrite a closed instruction, replacing polymorphic calls -/
def rewriteInst (inst : ClosedInst) (specMap : Std.HashMap SpecKey FuncId) : ClosedInst :=
  match inst with
  | .callPoly funcId typeArgs args retTy =>
      let key : SpecKey := ⟨funcId, typeArgs⟩
      match specMap.get? key with
      | some newFuncId => .call newFuncId args retTy
      | none => inst
  | .callExternPoly _ _ _ _ =>
      inst
  | .makeClosurePoly funcRef typeArgs env =>
      match funcRef with
      | .local funcId =>
        let key : SpecKey := ⟨funcId, typeArgs⟩
        match specMap.get? key with
        | some newFuncId => .makeClosure (.local newFuncId) env
        | none => inst
      | _ => inst
  | _ => inst

/-- Rewrite a statement -/
def rewriteStmt (stmt : ClosedStmt) (specMap : Std.HashMap SpecKey FuncId) : ClosedStmt :=
  { stmt with inst := rewriteInst stmt.inst specMap }

/-- Rewrite a block -/
def rewriteBlock (block : ClosedBlock) (specMap : Std.HashMap SpecKey FuncId) : ClosedBlock :=
  { block with stmts := block.stmts.map fun s => rewriteStmt s specMap }

/-- Rewrite a CFG -/
def rewriteCFG (cfg : ClosedCFG) (specMap : Std.HashMap SpecKey FuncId) : ClosedCFG :=
  let blocks' := cfg.blocks.fold
    (init := ({} : Std.HashMap Nat ClosedBlock)) fun acc id block =>
      acc.insert id (rewriteBlock block specMap)
  { cfg with blocks := blocks' }

/-- Rewrite a function -/
def rewriteFunc (func : ClosedFunc) (specMap : Std.HashMap SpecKey FuncId) : ClosedFunc :=
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

def addFunc (s : MonoState) (func : ClosedFunc) : MonoState :=
  { s with module := s.module.addMonoFunc func }

end MonoState

/-- Try to build a SpecRequest for a function with the given type arguments -/
def mkSpecRequest? (sf : SomeFunc) (typeArgs : Array ClosedTy) : Option SomeSpecRequest :=
  -- Check arity matches
  if h : sf.1 = typeArgs.size then
    let func : Func sf.1 := sf.2
    -- Build the type environment
    let env : Fin sf.1 → ClosedTy := fun i =>
      typeArgs[i.val]'(h ▸ i.isLt)
    some ⟨sf.1, { func := func, typeArgs := env }⟩
  else
    none

/-- Rewrite self-recursive calls from the template's FuncId to the specialized FuncId -/
private def fixSelfCalls (func : ClosedFunc) (templateId : FuncId) (selfId : FuncId) : ClosedFunc :=
  if templateId == selfId then func
  else match func.body with
  | none => func
  | some cfg =>
    let newBlocks := cfg.blocks.fold (init := ({} : Std.HashMap Nat ClosedBlock))
      fun acc bid block =>
        let newStmts := block.stmts.map fun stmt =>
          match stmt.inst with
          | .call fid args retTy =>
            if fid == templateId then { stmt with inst := .call selfId args retTy }
            else stmt
          | .callPoly fid _tyArgs args retTy =>
            if fid == templateId then { stmt with inst := .call selfId args retTy }
            else stmt
          | _ => stmt
        acc.insert bid { block with stmts := newStmts }
    { func with body := some { cfg with blocks := newBlocks } }

/-- Process one specialization request -/
def processRequest (key : SpecKey) : StateM MonoState Unit := do
  let s ← get

  -- Skip if already specialized
  if s.specMap.contains key then return ()

  -- Look up the original function
  let some origFunc := s.module.getFunc key.funcId | return ()

  -- Only specialize if it's actually polymorphic
  if !origFunc.isPolymorphic then return ()

  -- Try to create a type-safe specialization request
  let some ⟨_, req⟩ := mkSpecRequest? origFunc key.typeArgs | return ()

  -- Allocate a new function ID
  let (newFuncId, s') := s.freshFuncId
  set s'

  -- Generate the mangled name
  let newName := mangleSpecName origFunc.name key.typeArgs

  -- TOTAL SPECIALIZATION: req.specialize cannot fail
  let specializedFunc := req.specialize newFuncId newName

  -- Fix self-recursive `.call` instructions in the specialized body.
  let specializedFunc := fixSelfCalls specializedFunc key.funcId newFuncId

  -- Record the specialization
  modify fun s => s.recordSpecialization key newFuncId

  -- Add the specialized function to the module
  modify fun s => s.addFunc specializedFunc

  -- The specialized function may contain more polymorphic calls
  let newRequests := collectFuncRequests specializedFunc
  let filteredRequests := newRequests.filter fun r =>
    if r.funcId == key.funcId then
      let hasDegraded := r.typeArgs.any fun ty => match ty with
        | .rawPtr => !(key.typeArgs.any fun kty => match kty with | .rawPtr => true | _ => false)
        | _ => false
      !hasDegraded
    else true
  modify fun s => s.addRequests filteredRequests

/-- Process all pending specialization requests (fixed-point iteration) -/
partial def processAllRequests : StateM MonoState Unit := go
where
  go : StateM MonoState Unit := do
    let s ← get
    match s.popPending with
    | none => return ()
    | some (key, s') =>
      set s'
      processRequest key
      go

/-- Rewrite all functions to use specialized versions -/
def rewriteAllFuncs : StateM MonoState Unit := do
  let s ← get
  let specMap := s.specMap
  let newFuncs := s.module.funcs.map fun sf =>
    match sf.asMono? with
    | some f => SomeFunc.ofMono (rewriteFunc f specMap)
    | none => sf -- keep polymorphic (will be removed)
  set { s with module := { s.module with funcs := newFuncs } }


/-- Remap function reference -/
def remapFuncId (fid : FuncId) (idMap : Std.HashMap Nat Nat) : FuncId :=
  match idMap.get? fid.id with
  | some newId => ⟨newId⟩
  | none => fid

/-- Remap FuncRef -/
def remapFuncRefId (ref : FuncRef) (idMap : Std.HashMap Nat Nat) : FuncRef :=
  match ref with
  | .local fid => .local (remapFuncId fid idMap)
  | _ => ref

def remapInstRefs (inst : ClosedInst) (idMap : Std.HashMap Nat Nat) : ClosedInst :=
  match inst with
  | .call fid args retTy => .call (remapFuncId fid idMap) args retTy
  | .callPoly fid tyArgs args retTy => .callPoly (remapFuncId fid idMap) tyArgs args retTy
  | .callExternPoly _ _ _ _ => inst
  | .makeClosure ref env => .makeClosure (remapFuncRefId ref idMap) env
  | .makeClosurePoly ref tyArgs env => .makeClosurePoly (remapFuncRefId ref idMap) tyArgs env
  | .makeClosureDyn _ _ _ => inst
  | .stackClosure ref env => .stackClosure (remapFuncRefId ref idMap) env
  | .stackClosurePoly ref tyArgs env => .stackClosurePoly (remapFuncRefId ref idMap) tyArgs env
  | _ => inst

def remapFuncRefs (f : ClosedFunc) (idMap : Std.HashMap Nat Nat) : ClosedFunc :=
  match f.body with
  | none => f
  | some cfg =>
    let newBlocks := cfg.blocks.fold
      (init := ({} : Std.HashMap Nat ClosedBlock)) fun acc id block =>
        let newStmts := block.stmts.map fun s =>
          { s with inst := remapInstRefs s.inst idMap }
        acc.insert id { block with stmts := newStmts }
    { f with body := some { cfg with blocks := newBlocks } }

/-- Renumber functions and return the mapping -/
def renumberFuncs (funcs : Array ClosedFunc) : Array ClosedFunc × Std.HashMap Nat Nat :=
  let (arr, mapResult, _) := funcs.foldl (init := (#[], ({} : Std.HashMap Nat Nat), 0))
    fun (arr, map, idx) f =>
      let newF := { f with id := ⟨idx⟩ }
      (arr.push newF, map.insert f.id.id idx, idx + 1)
  (arr, mapResult)

/-- Collect all FuncId references from an instruction -/
private def collectFuncRefsInst (inst : Inst n) (acc : Array FuncId) : Array FuncId :=
  let fromOperand (op : Operand) (a : Array FuncId) : Array FuncId :=
    match op with
    | .func fid => a.push fid
    | _ => a
  let fromOperands (ops : Array Operand) (a : Array FuncId) : Array FuncId :=
    ops.foldl (fun a op => fromOperand op a) a
  let fromFuncRef (ref : FuncRef) (a : Array FuncId) : Array FuncId :=
    match ref with
    | .local fid => a.push fid
    | _ => a
  match inst with
  | .call fid args _ => fromOperands args (acc.push fid)
  | .callPoly fid _ args _ => fromOperands args (acc.push fid)
  | .callExternPoly _ _ args _ => fromOperands args acc
  | .makeClosure ref env => fromFuncRef ref (fromOperand env acc)
  | .makeClosurePoly ref _ env => fromFuncRef ref (fromOperand env acc)
  | .makeClosureDyn fnClo env _ => fromOperand env (fromOperand fnClo acc)
  | .stackClosure ref env => fromFuncRef ref (fromOperand env acc)
  | .stackClosurePoly ref _ env => fromFuncRef ref (fromOperand env acc)
  | .phi pairs _ => pairs.foldl (fun a (op, _) => fromOperand op a) acc
  | .select c t e => fromOperand e (fromOperand t (fromOperand c acc))
  | .callClosure clo args _ => fromOperands args (fromOperand clo acc)
  | .callIndirect fn args _ => fromOperands args (fromOperand fn acc)
  | _ => acc

/-- Collect all FuncId references from a function body -/
private def collectFuncRefsFromFunc (sf : SomeFunc) : Array FuncId :=
  let ⟨_, f⟩ := sf
  match f.body with
  | none => #[]
  | some cfg =>
    cfg.allBlocks.foldl (init := #[]) fun acc block =>
      block.stmts.foldl (init := acc) fun acc stmt =>
        collectFuncRefsInst stmt.inst acc

/-- Find all functions reachable from main via transitive call graph -/
partial def findReachableFuncs (m : Module) : Std.HashSet FuncId :=
  let funcById := m.funcs.foldl (init := ({} : Std.HashMap Nat SomeFunc))
    fun acc sf => acc.insert sf.id.id sf
  -- BFS from main
  let seeds : Array FuncId := match m.mainFunc with
    | some id => #[id]
    | none => #[]
  go funcById {} seeds
where
  go (funcById : Std.HashMap Nat SomeFunc) (visited : Std.HashSet FuncId)
     (worklist : Array FuncId) : Std.HashSet FuncId :=
    if h : worklist.size > 0 then
      let funcId := worklist[worklist.size - 1]
      let worklist := worklist.pop
      if visited.contains funcId then
        go funcById visited worklist
      else
        let visited := visited.insert funcId
        let refs := match funcById.get? funcId.id with
          | some sf => collectFuncRefsFromFunc sf
          | none => #[]
        let worklist := refs.foldl (init := worklist) fun wl ref =>
          if visited.contains ref then wl else wl.push ref
        go funcById visited worklist
    else visited

/-- Remove polymorphic functions and compact IDs -/
def removePolymorphicAndCompact : StateM MonoState Unit := do
  let s ← get

  -- Keep reachable monomorphic functions and auto-specialize reachable
  let reachable := findReachableFuncs s.module
  let monoFuncs := s.module.funcs.filterMap fun sf =>
    match sf.asMono? with
    | some f => if reachable.contains f.id then some f else none
    | none =>
      -- Polymorphic function: include if reachable, auto-specializing with rawPtr
      if reachable.contains sf.id then
        let ⟨n, f⟩ := sf
        let env : TyEnv n := fun _ => .rawPtr
        some (f.instantiate env f.id f.sig.name)
      else none

  -- Renumber
  let (newFuncs, idMap) := renumberFuncs monoFuncs

  -- Update index
  let newFuncIndex := newFuncs.foldl
    (init := ({} : Std.HashMap String FuncId)) fun acc f =>
      acc.insert f.sig.name f.id

  -- Remap references
  let finalFuncs := newFuncs.map fun f => remapFuncRefs f idMap

  -- Update main
  let newMain := s.module.mainFunc.bind fun oldId =>
    idMap.get? oldId.id |>.map FuncId.mk

  set { s with module := {
    s.module with
    funcs := finalFuncs.map SomeFunc.ofMono
    funcIndex := newFuncIndex
    mainFunc := newMain
  }}

/-! ## Entry Point -/

/-- Run the monomorphization pass on a module -/
def monomorphize (m : Module) : Module := Id.run do
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

  let ((), finalState) := Id.run (StateT.run removePolymorphicAndCompact stateAfterRewrite)
  return finalState.module

/-! ## Verification -/

/-- Check if a module is fully monomorphic -/
def isFullyMonomorphic (m : Module) : Bool :=
  m.funcs.all fun sf =>
    sf.isMono &&
    match sf.asMono? with
    | none => false
    | some f =>
      match f.body with
      | none => true
      | some cfg =>
        cfg.allBlocks.all fun block =>
          block.stmts.all fun stmt =>
            match stmt.inst with
            | .callPoly _ _ _ _ => false
            | .callExternPoly _ _ _ _ => false
            | .makeClosurePoly _ _ _ => false
            | .stackClosurePoly _ _ _ => false
            | _ => true

/-- Report remaining polymorphism -/
def reportPolymorphism (m : Module) : Array String :=
  m.funcs.foldl (init := #[]) fun acc sf =>
    if sf.isPolymorphic then
      acc.push s!"Function {sf.name} is polymorphic (arity {sf.arity})"
    else
      match sf.asMono? with
      | none => acc
      | some f =>
        let funcIssues := Id.run do
          let mut issues : Array String := #[]
          if let some cfg := f.body then
            for block in cfg.allBlocks do
              for stmt in block.stmts do
                match stmt.inst with
                | .callPoly funcId typeArgs _ _ =>
                    issues := issues.push s!"Function {f.sig.name} has callPoly to {funcId} with {typeArgs.size} type args"
                | .callExternPoly name typeArgs _ _ =>
                    issues := issues.push s!"Function {f.sig.name} has callExternPoly to \"{name}\" with {typeArgs.size} type args"
                | .makeClosurePoly funcRef typeArgs _ =>
                    issues := issues.push s!"Function {f.sig.name} has makeClosurePoly to {funcRef} with {typeArgs.size} type args"
                | .stackClosurePoly funcRef typeArgs _ =>
                    issues := issues.push s!"Function {f.sig.name} has stackClosurePoly to {funcRef} with {typeArgs.size} type args"
                | _ => pure ()
          pure issues
        acc ++ funcIssues

/-- Remove unreachable functions and compact IDs -/
def deadFunctionElimination (m : Module) : Module := Id.run do
  let reachable := findReachableFuncs m
  let liveFuncs := m.funcs.filterMap fun sf =>
    match sf.asMono? with
    | some f => if reachable.contains f.id then some f else none
    | none => none
  let (newFuncs, idMap) := renumberFuncs liveFuncs
  let finalFuncs := newFuncs.map fun f => remapFuncRefs f idMap
  let newFuncIndex := finalFuncs.foldl
    (init := ({} : Std.HashMap String FuncId)) fun acc f =>
      acc.insert f.sig.name f.id
  let newMain := m.mainFunc.bind fun oldId =>
    idMap.get? oldId.id |>.map FuncId.mk
  let result : Module := {
    m with
    funcs := finalFuncs.map SomeFunc.ofMono
    funcIndex := newFuncIndex
    mainFunc := newMain
  }
  return result.rebuildWiredFuncIndex

end Somac.Alloy.Monomorphize
