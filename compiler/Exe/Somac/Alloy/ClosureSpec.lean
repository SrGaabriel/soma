import Somac.Alloy.Func
import Somac.Alloy.Analysis
import Somac.Alloy.Monomorphize
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Alloy.ClosureSpec

open Somac.Alloy

/-- Get a monomorphic function by ID from the module -/
def getMonoFunc? (m : Module) (fid : FuncId) : Option ClosedFunc :=
  m.getFunc fid |>.bind SomeFunc.asMono?

/-- Get function parameter count from its signature -/
def getFuncParamCount (m : Module) (fid : FuncId) : Nat :=
  match getMonoFunc? m fid with
  | some f => f.sig.params.size
  | none => 0


/-- Remove element at index from an array -/
private def removeAt [Inhabited α] (arr : Array α) (idx : Nat) : Array α := Id.run do
  let mut result : Array α := #[]
  for i in [:arr.size] do
    if i != idx then result := result.push arr[i]!
  return result

/-- Insert an element at a given index, shifting subsequent elements right -/
private def insertAtIdx [Inhabited α] (arr : Array α) (idx : Nat) (val : α) : Array α := Id.run do
  let mut result : Array α := #[]
  for i in [:arr.size] do
    if i == idx then result := result.push val
    result := result.push arr[i]!
  if idx >= arr.size then result := result.push val
  return result

/-- Collect all LocalId.ids referenced as operands in statements + terminator -/
private def collectUsedLocals (stmts : Array ClosedStmt) (term : Terminator) : Std.HashSet Nat := Id.run do
  let mut used : Std.HashSet Nat := {}
  for stmt in stmts do
    for lid in stmt.inst.localUses do
      used := used.insert lid.id
  for lid in term.localUses do
    used := used.insert lid.id
  return used

/-- Check if an instruction is pure (safe to remove if result unused) -/
private def isPureInst : ClosedInst → Bool
  | .copy .. => true
  | .binOp .. => true
  | .unOp .. => true
  | .makeClosure .. => true
  | .makeClosurePoly .. => true
  | .structLit .. => true
  | .arrayLit .. => true
  | .extractField .. => true
  | .extractElem .. => true
  | .insertField .. => true
  | .insertElem .. => true
  | .getTag .. => true
  | .getPayload .. => true
  | .taggedLit .. => true
  | .getFieldPtr .. => true
  | .getElemPtr .. => true
  | .lazySup .. => true
  | .supProj0 .. => true
  | .supProj1 .. => true
  | .closureFunc .. => true
  | .closureEnv .. => true
  | .phi .. => true
  | .select .. => true
  | .alloca .. => true
  | .load .. => true
  | _ => false

/-- Remove dead instructions from a block (iterative fixpoint) -/
private def dceFixpoint : Array ClosedStmt → Terminator → Nat → Array ClosedStmt
  | stmts, _, 0 => stmts
  | stmts, term, fuel + 1 =>
    let used := collectUsedLocals stmts term
    let newStmts := stmts.filter fun stmt =>
      match stmt.result with
      | none => true
      | some rid => used.contains rid.id || !isPureInst stmt.inst
    if newStmts.size < stmts.size then dceFixpoint newStmts term fuel
    else newStmts

/-- Apply DCE across all blocks in a function using inter-block used-local analysis -/
def dceFunc (f : ClosedFunc) : ClosedFunc := Id.run do
  let some cfg := f.body | return f
  let mut allBlocks := cfg.blocks
  for _round in [:20] do
    let mut allUsed : Std.HashSet Nat := {}
    for (_, block) in allBlocks.toArray do
      for stmt in block.stmts do
        for lid in stmt.inst.localUses do
          allUsed := allUsed.insert lid.id
      for lid in block.terminator.localUses do
        allUsed := allUsed.insert lid.id
    let mut changed := false
    let mut newBlocks : Std.HashMap Nat ClosedBlock := {}
    for (blockId, block) in allBlocks.toArray do
      let newStmts := block.stmts.filter fun stmt =>
        match stmt.result with
        | none => true
        | some rid => allUsed.contains rid.id || !isPureInst stmt.inst
      if newStmts.size < block.stmts.size then changed := true
      newBlocks := newBlocks.insert blockId { block with stmts := newStmts }
    allBlocks := newBlocks
    if !changed then break
  return { f with body := some { cfg with blocks := allBlocks } }

/-- Count callClosure instructions in a module (for fixpoint convergence check) -/
private def countCallClosures (m : Module) : Nat := Id.run do
  let mut count := 0
  for sf in m.funcs do
    if let some f := sf.asMono? then
      if let some cfg := f.body then
        for (_, block) in cfg.blocks.toArray do
          for stmt in block.stmts do
            if let .callClosure .. := stmt.inst then
              count := count + 1
  return count

/-- Information about a function parameter used in callClosure -/
structure ClosureParamInfo where
  /-- Parameter index in the function signature -/
  paramIdx : Nat
  /-- The LocalId of the parameter -/
  localId : LocalId
  deriving Inhabited

/-- Build a map from derived LocalIds back to their source param LocalIds -/
private def buildDerivedParamMap (cfg : ClosedCFG) (paramIds : Std.HashSet Nat)
    : Std.HashMap Nat Nat := Id.run do
  let mut derivedFrom : Std.HashMap Nat Nat := {}
  for pid in paramIds do
    derivedFrom := derivedFrom.insert pid pid
  for _round in [:3] do
    for (_, block) in cfg.blocks.toArray do
      for stmt in block.stmts do
        if let some resultId := stmt.result then
          match stmt.inst with
          | .lazySup _ (.local srcId) _ =>
            if let some srcParam := derivedFrom.get? srcId.id then
              derivedFrom := derivedFrom.insert resultId.id srcParam
          | .supProj0 (.local srcId) _ =>
            if let some srcParam := derivedFrom.get? srcId.id then
              derivedFrom := derivedFrom.insert resultId.id srcParam
          | .supProj1 (.local srcId) _ =>
            if let some srcParam := derivedFrom.get? srcId.id then
              derivedFrom := derivedFrom.insert resultId.id srcParam
          | .copy (.local srcId) =>
            if let some srcParam := derivedFrom.get? srcId.id then
              derivedFrom := derivedFrom.insert resultId.id srcParam
          | .unOp _ (.local srcId) =>
            if let some srcParam := derivedFrom.get? srcId.id then
              derivedFrom := derivedFrom.insert resultId.id srcParam
          | .clone (.local srcId) _ _ =>
            if let some srcParam := derivedFrom.get? srcId.id then
              derivedFrom := derivedFrom.insert resultId.id srcParam
          | .closureFunc (.local srcId) =>
            if let some srcParam := derivedFrom.get? srcId.id then
              derivedFrom := derivedFrom.insert resultId.id srcParam
          | .closureEnv (.local srcId) =>
            if let some srcParam := derivedFrom.get? srcId.id then
              derivedFrom := derivedFrom.insert resultId.id srcParam
          | .callExtern _ args _
          | .callExternPoly _ _ args _ =>
            -- If any argument is derived from a param, the result is derived too
            -- (covers soma_clone_closure and similar runtime calls on closure params)
            for arg in args do
              if let .local srcId := arg then
                if let some srcParam := derivedFrom.get? srcId.id then
                  derivedFrom := derivedFrom.insert resultId.id srcParam
                  break
          | _ => pure ()
  return derivedFrom

/-- Scan a function body for parameters used in callClosure instructions -/
def findClosureParams (f : ClosedFunc) : Array ClosureParamInfo := Id.run do
  let some cfg := f.body | return #[]
  let paramIds : Std.HashSet Nat := f.sig.params.foldl (init := {})
    fun acc p => acc.insert p.id.id
  let derivedFrom := buildDerivedParamMap cfg paramIds
  let mut result : Array ClosureParamInfo := #[]
  let mut found : Std.HashSet Nat := {}
  for (_, block) in cfg.blocks.toArray do
    for stmt in block.stmts do
      match stmt.inst with
      | .callClosure (.local closureId) _ _ =>
        if let some srcParamId := derivedFrom.get? closureId.id then
          if !found.contains srcParamId then
            for i in [:f.sig.params.size] do
              if f.sig.params[i]!.id.id == srcParamId then
                result := result.push { paramIdx := i, localId := f.sig.params[i]!.id }
                found := found.insert srcParamId
      | _ => pure ()
  return result

/-- A specialization request -/
structure SpecRequest where
  hofFuncId : FuncId
  paramIdx : Nat
  targetFuncId : FuncId
  hasEnv : Bool
  envOperand : Option Operand
  deriving Inhabited

instance : BEq SpecRequest where
  beq a b := a.hofFuncId == b.hofFuncId && a.paramIdx == b.paramIdx &&
             a.targetFuncId == b.targetFuncId && a.hasEnv == b.hasEnv

instance : Hashable SpecRequest where
  hash r := mixHash (hash r.hofFuncId.id)
    (mixHash (hash r.paramIdx) (hash r.targetFuncId.id))

/-- wrapper(p) := makeClosure(inner, p); ret - -/
private def trampolineInner? (m : Module) (funcId : FuncId) : Option FuncId := do
  let f ← getMonoFunc? m funcId
  let cfg ← f.body
  guard (cfg.blocks.size == 1)
  let entry ← cfg.getBlock .entry
  guard (entry.stmts.size == 1)
  let stmt := entry.stmts[0]!
  -- Wrapper must be a 1-arg function whose body is `makeClosure(inner, p)`.
  guard (f.sig.params.size == 1)
  let paramId := f.sig.params[0]!.id
  match stmt.inst with
  | .makeClosure (.local innerId) _ (.local envId) =>
    guard (envId == paramId)
    match entry.terminator with
    | .ret (.local retId) =>
      match stmt.result with
      | some resId => guard (resId == retId); return innerId
      | none => failure
    | _ => failure
  | _ => failure

/-- Is this function a trampoline wrapper that we can't retarget -/
private def isUnretargetableWrapper (m : Module) (funcId : FuncId) : Bool := Id.run do
  let some f := getMonoFunc? m funcId | return false
  let some cfg := f.body | return false
  if cfg.blocks.size != 1 then return false
  let some entry := cfg.getBlock .entry | return false
  if entry.stmts.size != 1 then return false
  let stmt := entry.stmts[0]!
  match stmt.inst with
  | .makeClosure _ _ _ | .makeClosurePoly _ _ _ _ =>
    match entry.terminator with
    | .ret _ => (trampolineInner? m funcId).isNone
    | _ => false
  | _ => false

/-- Scan all functions for call sites that pass known closures to HOFs -/
def findSpecRequests (m : Module)
    (closureParamMap : Std.HashMap Nat (Array ClosureParamInfo))
    : Array SpecRequest := Id.run do
  let mut requests : Array SpecRequest := #[]
  let mut seen : Std.HashSet SpecRequest := {}
  for sf in m.funcs do
    let some f := sf.asMono? | continue
    let some cfg := f.body | continue
    for (_, block) in cfg.blocks.toArray do
      for stmt in block.stmts do
        match stmt.inst with
        | .call hofFuncId args _ =>
          let some closureParams := closureParamMap.get? hofFuncId.id | continue
          for cp in closureParams do
            if h : cp.paramIdx < args.size then
              match args[cp.paramIdx] with
              | .local makeClosureId =>
                match findMakeClosureInFunc cfg makeClosureId with
                | some (targetFuncId, captureCount, envOp) =>
                  let effectiveTargetFuncId :=
                    (trampolineInner? m targetFuncId).getD targetFuncId
                  if isUnretargetableWrapper m targetFuncId then continue
                  let hasEnv := captureCount > 0
                  let req : SpecRequest := {
                    hofFuncId, paramIdx := cp.paramIdx,
                    targetFuncId := effectiveTargetFuncId,
                    hasEnv, envOperand := some envOp
                  }
                  if !seen.contains req then
                    requests := requests.push req
                    seen := seen.insert req
                | none => pure ()
              | _ => pure ()
        | _ => pure ()
  return requests
where
  findMakeClosureInFunc (cfg : ClosedCFG) (lid : LocalId) : Option (FuncId × Nat × Operand) := do
    for (_, block) in cfg.blocks.toArray do
      for stmt in block.stmts do
        match stmt.result with
        | some resultId =>
          if resultId == lid then
            match stmt.inst with
            | .makeClosure (.local funcId) cc env => return (funcId, cc, env)
            | _ => failure
        | none => pure ()
    none

/-- Remap operands in an instruction, replacing one LocalId with another -/
private def remapLocalInOperand (op : Operand) (from_ to_ : LocalId) : Operand :=
  match op with
  | .local id => if id == from_ then .local to_ else op
  | _ => op

/-- Remap operands in an array -/
private def remapLocalsInOps (ops : Array Operand) (from_ to_ : LocalId) : Array Operand :=
  ops.map fun op => remapLocalInOperand op from_ to_

/-- Resolve the actual environment operand for a recursive call's closure argument -/
private def resolveRecursiveEnv (cfg : ClosedCFG) (closureArg : Operand)
    (targetFuncId : FuncId) (envLocalId : Option LocalId) : Operand :=
  match closureArg with
  | .local lid =>
    let found := cfg.blocks.toArray.findSome? fun (_, block) =>
      block.stmts.findSome? fun stmt =>
        match stmt.result with
        | some resultId =>
          if resultId == lid then
            match stmt.inst with
            | .makeClosure (.local funcId) _ env =>
              if funcId == targetFuncId then some env else none
            | .makeClosurePoly (.local funcId) _ _ env =>
              if funcId == targetFuncId then some env else none
            | _ => none
          else none
        | none => none
    match found with
    | some dynamicEnv => dynamicEnv
    | none =>
      match envLocalId with
      | some envId => .local envId
      | none => closureArg
  | _ =>
    match envLocalId with
    | some envId => .local envId
    | none => closureArg

/-- Rewrite a statement for the specialized function -/
private def rewriteStmtForSpec (stmt : ClosedStmt) (closureDerived : Std.HashSet Nat)
    (targetFuncId : FuncId) (origFuncId : FuncId) (specFuncId : FuncId)
    (paramIdx : Nat) (hasEnv : Bool) (envLocalId : Option LocalId)
    (cfg : ClosedCFG)
    (targetRetTy : Option ClosedTy := none)
    : Option ClosedStmt :=
  match stmt.inst with
  | .callClosure closureOp args retTy =>
    match closureOp with
    | .local cloId =>
      if closureDerived.contains cloId.id then
        let callArgs := if hasEnv then
          match envLocalId with
          | some envId => #[.local envId] ++ args
          | none => args
        else args
        let actualRetTy := if retTy != .rawPtr then retTy else targetRetTy.getD retTy
        some { stmt with inst := .call targetFuncId callArgs actualRetTy }
      else some stmt
    | _ => some stmt
  | .call funcId args retTy =>
    if funcId == origFuncId then
      let newArgs := removeAt args paramIdx
      let finalArgs := if hasEnv then
        let closureArg := if h : paramIdx < args.size then args[paramIdx] else .const .unit
        let dynamicEnv := resolveRecursiveEnv cfg closureArg targetFuncId envLocalId
        insertAtIdx newArgs paramIdx dynamicEnv
      else newArgs
      some { stmt with inst := .call specFuncId finalArgs retTy }
    else some stmt
  | .callPoly funcId _tyArgs args retTy =>
    if funcId == origFuncId then
      let newArgs := removeAt args paramIdx
      let finalArgs := if hasEnv then
        let closureArg := if h : paramIdx < args.size then args[paramIdx] else .const .unit
        let dynamicEnv := resolveRecursiveEnv cfg closureArg targetFuncId envLocalId
        insertAtIdx newArgs paramIdx dynamicEnv
      else newArgs
      some { stmt with inst := .call specFuncId finalArgs retTy }
    else some stmt
  | .erase (.local lid) _ =>
    -- Drop erase of closure-derived values since the caller owns the env lifetime
    if closureDerived.contains lid.id then none else some stmt
  | .clone (.local lid) _ _ =>
    -- Drop clone of closure-derived values because the closure no longer exists
    if closureDerived.contains lid.id then none else some stmt
  | _ =>
    match stmt.result with
    | some rid => if closureDerived.contains rid.id then none else some stmt
    | none => some stmt

/-- Rewrite a block for specialization -/
private def rewriteBlockForSpec (block : ClosedBlock) (closureDerived : Std.HashSet Nat)
    (targetFuncId : FuncId) (origFuncId : FuncId) (specFuncId : FuncId)
    (paramIdx : Nat) (hasEnv : Bool) (envLocalId : Option LocalId)
    (cfg : ClosedCFG)
    (targetRetTy : Option ClosedTy := none)
    : ClosedBlock :=
  let newStmts := block.stmts.filterMap fun stmt =>
    rewriteStmtForSpec stmt closureDerived
      targetFuncId origFuncId specFuncId paramIdx hasEnv envLocalId cfg targetRetTy
  { block with stmts := newStmts }

/-- Create a specialized version of a function with a known closure parameter -/
def specializeFunc (m : Module) (origFunc : ClosedFunc) (req : SpecRequest)
    (specFuncId : FuncId) : ClosedFunc := Id.run do
  let some cfg := origFunc.body | return { origFunc with id := specFuncId }

  let closureParam := origFunc.sig.params[req.paramIdx]!
  let closureParamId := closureParam.id

  let paramIds : Std.HashSet Nat := ({} : Std.HashSet Nat).insert closureParamId.id
  let derivedMap := buildDerivedParamMap cfg paramIds
  let closureDerived : Std.HashSet Nat := derivedMap.fold (init := {})
    fun acc lid srcId => if srcId == closureParamId.id then acc.insert lid else acc

  let mut newParams : Array (Param 0) := #[]
  let mut envLocalId : Option LocalId := none
  if req.hasEnv then
    let envParam : Param 0 := { id := closureParamId, name := "env", ty := .rawPtr }
    for i in [:origFunc.sig.params.size] do
      if i == req.paramIdx then
        newParams := newParams.push envParam
        envLocalId := some closureParamId
      else
        newParams := newParams.push origFunc.sig.params[i]!
  else
    for i in [:origFunc.sig.params.size] do
      if i != req.paramIdx then
        newParams := newParams.push origFunc.sig.params[i]!

  let targetRetTy : Option ClosedTy := Id.run do
    let mut retTy : Option ClosedTy := none
    for sf in m.funcs do
      if sf.id == req.targetFuncId then
        match sf.asMono? with
        | some f =>
          if f.sig.retTy != .rawPtr then
            return some f.sig.retTy
          else
            retTy := some f.sig.retTy
        | none => pure ()
    match retTy with
    | some .rawPtr =>
      if origFunc.sig.retTy != .rawPtr then
        return some origFunc.sig.retTy
      else return none
    | other => return other

  let newBlocks := cfg.blocks.fold (init := ({} : Std.HashMap Nat ClosedBlock))
    fun acc id block =>
      acc.insert id (rewriteBlockForSpec block closureDerived
        req.targetFuncId origFunc.id specFuncId req.paramIdx req.hasEnv envLocalId cfg targetRetTy)

  -- Update local types: remove closure-derived locals and fix return types for callClosure → direct call rewrites
  let mut cleanLocalTypes := origFunc.localTypes.fold (init := ({} : Std.HashMap Nat ClosedTy))
    fun acc lid ty =>
      if closureDerived.contains lid || lid == closureParamId.id then acc
      else acc.insert lid ty
  for (_, block) in cfg.blocks.toArray do
    for stmt in block.stmts do
      match stmt.inst, stmt.result with
      | .callClosure (.local cloId) _ cloRetTy, some rid =>
        if closureDerived.contains cloId.id then
          let bestRetTy := if cloRetTy != .rawPtr then cloRetTy
            else targetRetTy.getD cloRetTy
          cleanLocalTypes := cleanLocalTypes.insert rid.id bestRetTy
      | _, _ => pure ()

  let envTag := if req.hasEnv then "e" else "ne"
  let specName := s!"{origFunc.sig.name}$cs_{req.targetFuncId.id}_{envTag}"
  return {
    id := specFuncId
    sig := { origFunc.sig with name := specName, params := newParams }
    body := some { cfg with blocks := newBlocks }
    attrs := origFunc.attrs
    nextLocalId := origFunc.nextLocalId
    localTypes := cleanLocalTypes
  }

/-- Check if a type is pointer-like -/
private def isPtrLikeTy : ClosedTy → Bool
  | .rawPtr => true
  | .ptr _ => true
  | .closure _ _ => true
  | _ => false

/-- Extract PrimTy from a type if it's a primitive -/
private def asPrimTy : ClosedTy → Option PrimTy
  | .prim p => some p
  | _ => none

/-- Get the type of an operand from the local type map -/
private def getOperandTy (op : Operand) (localTypes : Std.HashMap Nat ClosedTy) : Option ClosedTy :=
  match op with
  | .local lid => localTypes.get? lid.id
  | .func _ => some .rawPtr
  | _ => none

/-- Check if a function is eligible for inlining -/
private def isTinyInlinable? (m : Module) (fid : FuncId) : Option ClosedFunc := do
  let f ← getMonoFunc? m fid
  let cfg ← f.body
  guard (cfg.blocks.size == 1)
  let entryBlock ← cfg.getBlock .entry
  match entryBlock.terminator with
  | .ret _ => pure ()
  | _ => failure
  let mut realInstCount := 0
  let mut selfRecursive := false
  for stmt in entryBlock.stmts do
    match stmt.inst with
    | .copy _ => pure ()
    | .call callFid _ _ => do
      if callFid == fid then selfRecursive := true
      realInstCount := realInstCount + 1
    | _ => realInstCount := realInstCount + 1
  guard (!selfRecursive)
  guard (realInstCount ≤ 8)
  return f

/-- Inline a single call to a tiny function, returning the replacement statements -/
private def inlineCall (callee : ClosedFunc) (callArgs : Array Operand)
    (callResult : Option LocalId) (nextLocalId : Nat)
    (callerLocalTypes : Std.HashMap Nat ClosedTy) (expectedRetTy : ClosedTy)
    : Array ClosedStmt × Nat × Std.HashMap Nat ClosedTy := Id.run do
  let some cfg := callee.body | return (#[], nextLocalId, {})
  let some entryBlock := cfg.getBlock .entry | return (#[], nextLocalId, {})

  let mut freshId := nextLocalId
  let mut freshTypes : Std.HashMap Nat ClosedTy := {}
  let mut conversionStmts : Array ClosedStmt := #[]

  -- Build parameter substitution: param LocalId → call argument Operand
  -- Insert type conversions when arg types don't match param types
  let mut paramSubst : Std.HashMap Nat Operand := {}
  for i in [:callee.sig.params.size] do
    if h : i < callArgs.size then
      let paramTy := callee.sig.params[i]!.ty
      let argOp := callArgs[i]
      let argTy := getOperandTy argOp callerLocalTypes
      -- Check if we need a type conversion
      let needsConv := match argTy with
        | some aTy => aTy != paramTy && (isPtrLikeTy aTy || isPtrLikeTy paramTy)
        | none => false
      if needsConv then
        let convId : LocalId := ⟨freshId⟩
        freshId := freshId + 1
        freshTypes := freshTypes.insert convId.id paramTy
        -- Determine conversion direction
        let isAggregate := fun (t : ClosedTy) => match t with | .struct _ | .tagged _ _ => true | _ => false
        let argIsAggregate := match argTy with | some t => isAggregate t | none => false
        let convInst : ClosedInst :=
          if argIsAggregate && !isAggregate paramTy then
            .copy argOp
          else if isPtrLikeTy (argTy.getD .rawPtr) then
            match asPrimTy paramTy with
            | some primTy => .unOp (.ptrtoint primTy) argOp
            | none => .unOp (.bitcast paramTy) argOp
          else if isPtrLikeTy paramTy then
            .unOp .inttoptr argOp
          else
            .unOp (.bitcast paramTy) argOp
        conversionStmts := conversionStmts.push
          { result := some convId, inst := convInst }
        paramSubst := paramSubst.insert callee.sig.params[i]!.id.id (.local convId)
      else
        paramSubst := paramSubst.insert callee.sig.params[i]!.id.id argOp

  -- Allocate fresh LocalIds for all non-parameter locals (instruction results)
  let mut localRemap : Std.HashMap Nat LocalId := {}
  for stmt in entryBlock.stmts do
    if let some resultId := stmt.result then
      if !paramSubst.contains resultId.id then
        let newId : LocalId := ⟨freshId⟩
        localRemap := localRemap.insert resultId.id newId
        if let some ty := callee.localTypes.get? resultId.id then
          freshTypes := freshTypes.insert freshId ty
        freshId := freshId + 1

  -- Operand remapping function
  let remapOp (op : Operand) : Operand :=
    match op with
    | .local lid =>
      match paramSubst.get? lid.id with
      | some argOp => argOp
      | none =>
        match localRemap.get? lid.id with
        | some freshLid => .local freshLid
        | none => op
    | _ => op

  -- Start with conversion stmts, then copy instructions with remapped operands
  let mut inlinedStmts := conversionStmts
  for stmt in entryBlock.stmts do
    let newResult := stmt.result.bind fun rid =>
      if paramSubst.contains rid.id then none
      else localRemap.get? rid.id
    let newInst := stmt.inst.mapOperands remapOp
    inlinedStmts := inlinedStmts.push { result := newResult, inst := newInst }

  -- Link return value to call result, inserting type coercion if needed
  match entryBlock.terminator with
  | .ret retOp =>
    let remappedRet := remapOp retOp
    if let some cResult := callResult then
      let calleeRetTy := callee.sig.retTy
      let needsRetConv := calleeRetTy != expectedRetTy &&
        (isPtrLikeTy calleeRetTy || isPtrLikeTy expectedRetTy)
      if needsRetConv then
        -- Allocate intermediate local for the raw return value
        let rawRetId : LocalId := ⟨freshId⟩
        freshId := freshId + 1
        freshTypes := freshTypes.insert rawRetId.id calleeRetTy
        inlinedStmts := inlinedStmts.push
          { result := some rawRetId, inst := .copy remappedRet }
        -- Insert conversion from callee return type to expected return type
        let isAggregate := fun (t : ClosedTy) => match t with | .struct _ | .tagged _ _ => true | _ => false
        let structScalarMismatch := isAggregate calleeRetTy && !isAggregate expectedRetTy
        let (convInst, resultTy) :=
          if structScalarMismatch then
            (.copy (.local rawRetId), calleeRetTy)
          else if isPtrLikeTy calleeRetTy then
            let inst := match asPrimTy expectedRetTy with
              | some primTy => .unOp (.ptrtoint primTy) (.local rawRetId)
              | none => .unOp (.bitcast expectedRetTy) (.local rawRetId)
            (inst, expectedRetTy)
          else if isPtrLikeTy expectedRetTy then
            (.unOp .inttoptr (.local rawRetId), expectedRetTy)
          else
            (.unOp (.bitcast expectedRetTy) (.local rawRetId), expectedRetTy)
        freshTypes := freshTypes.insert cResult.id resultTy
        inlinedStmts := inlinedStmts.push
          { result := some cResult, inst := convInst }
      else
        inlinedStmts := inlinedStmts.push
          { result := some cResult, inst := .copy remappedRet }
  | _ => pure ()

  return (inlinedStmts, freshId, freshTypes)

/-- Inline all calls to tiny functions within a single block -/
private def inlineCallsInBlock (m : Module) (block : ClosedBlock) (nextLocalId : Nat)
    (localTypes : Std.HashMap Nat ClosedTy) (selfFuncId : FuncId)
    : ClosedBlock × Nat × Std.HashMap Nat ClosedTy := Id.run do
  let mut newStmts : Array ClosedStmt := #[]
  let mut nextId := nextLocalId
  let mut types := localTypes
  for stmt in block.stmts do
    match stmt.inst with
    | .call funcId callArgs retTy =>
      if funcId == selfFuncId then
        newStmts := newStmts.push stmt
      else
        match isTinyInlinable? m funcId with
        | some callee =>
          if callArgs.size == callee.sig.params.size then
            let (inlinedStmts, newNextId, freshTypes) :=
              inlineCall callee callArgs stmt.result nextId types retTy
            newStmts := newStmts ++ inlinedStmts
            nextId := newNextId
            for (tid, ty) in freshTypes.toArray do
              types := types.insert tid ty
          else
            newStmts := newStmts.push stmt
        | none => newStmts := newStmts.push stmt
    | _ => newStmts := newStmts.push stmt
  return ({ block with stmts := newStmts }, nextId, types)

/-- Inline tiny function calls in all blocks of a function -/
def inlineTinyFuncsInFunc (m : Module) (f : ClosedFunc) : ClosedFunc := Id.run do
  let some cfg := f.body | return f
  let mut newBlocks : Std.HashMap Nat ClosedBlock := {}
  let mut nextId := f.nextLocalId
  let mut types := f.localTypes
  for (blockId, block) in cfg.blocks.toArray do
    let (newBlock, newNextId, newTypes) :=
      inlineCallsInBlock m block nextId types f.id
    newBlocks := newBlocks.insert blockId newBlock
    nextId := newNextId
    types := newTypes
  return { f with
    body := some { cfg with blocks := newBlocks }
    nextLocalId := nextId
    localTypes := types
  }

/-- Abstract closure value for the forward dataflow analysis -/
inductive ClosureVal where
  | unreached
  | known (funcId : FuncId) (arity : Nat) (accArgs : Array Operand)
          (hasEnv : Bool) (envOp : Option Operand)
  | varied
  deriving Inhabited

namespace ClosureVal

/-- Check structural equality of two known closures (ignoring operand identity -/
def structEq : ClosureVal → ClosureVal → Bool
  | .unreached, .unreached => true
  | .varied, .varied => true
  | .known f1 a1 args1 e1 _, .known f2 a2 args2 e2 _ =>
    f1 == f2 && a1 == a2 && args1.size == args2.size && e1 == e2
  | _, _ => false

end ClosureVal

/-- The closure tracking abstract domain -/
private def closureDomain : Analysis.Domain ClosureVal where
  bot := .unreached
  join := fun a b => match a, b with
    | .unreached, x | x, .unreached => x
    | .varied, _ | _, .varied => .varied
    | .known f1 a1 args1 e1 env1, .known f2 a2 _ e2 _ =>
      if f1 == f2 && a1 == a2 && e1 == e2 then .known f1 a1 args1 e1 env1
      else .varied
  eq := ClosureVal.structEq

/-- Build the transfer function for closure tracking -/
private def closureTransfer (m : Module)
    (state : Analysis.AbsState ClosureVal) (stmt : ClosedStmt)
    : Analysis.AbsState ClosureVal :=
  match stmt.inst, stmt.result with
  | .makeClosure (.local funcId) captureCount env, some rid =>
    let arity := getFuncParamCount m funcId
    let hasEnv := captureCount > 0
    let envOp := if hasEnv then some env else none
    let accArgs : Array Operand := if hasEnv then #[env] else #[]
    state.set rid.id (.known funcId arity accArgs hasEnv envOp)
  | .copy (.local srcId), some rid =>
    -- Propagate known closure through copies
    state.set rid.id (state.get closureDomain srcId.id)
  | .unOp _ (.local srcId), some rid =>
    -- Propagate through unary ops (bitcast, ptrtoint, inttoptr)
    state.set rid.id (state.get closureDomain srcId.id)
  | .callClosure (.local cloId) args _, some rid =>
    -- Under-saturated callClosure: result is a known closure with more accumulated args
    match state.get closureDomain cloId.id with
    | .known funcId arity accArgs hasEnv envOp =>
      let totalArgs := accArgs ++ args
      if totalArgs.size < arity then
        state.set rid.id (.known funcId arity totalArgs hasEnv envOp)
      else
        -- Saturated/over-saturated: result is the call's return value (unknown closure)
        state
    | _ => state
  | _, _ => state

/-- Resolve an operand to its abstract closure value in a given state -/
private def closureResolveOp (state : Analysis.AbsState ClosureVal) (op : Operand)
    : ClosureVal :=
  match op with
  | .local lid => state.get closureDomain lid.id
  | _ => .unreached

/-- Build the closure tracking analysis specification -/
private def closureAnalysisSpec (m : Module) : Analysis.ForwardSpec ClosureVal where
  domain := closureDomain
  transfer := closureTransfer m
  resolveOp := closureResolveOp

/-- Rewrite a block's callClosure instructions using analysis results -/
private def rewriteBlockWithAnalysis (m : Module)
    (block : ClosedBlock) (entryState : Analysis.AbsState ClosureVal) (nextLocalId : Nat)
    : ClosedBlock × Nat × Std.HashMap Nat ClosedTy := Id.run do
  let spec := closureAnalysisSpec m
  let mut state := entryState
  let mut newStmts : Array ClosedStmt := #[]
  let mut freshId := nextLocalId
  let mut typeUpdates : Std.HashMap Nat ClosedTy := {}
  for stmt in block.stmts do
    match stmt.inst with
    | .phi _ _ =>
      -- Phi nodes: re-apply transfer to maintain state consistency
      state := spec.transfer state stmt
      newStmts := newStmts.push stmt
    | .callClosure closureOp args retTy =>
      match closureOp with
      | .local closureId =>
        match state.get closureDomain closureId.id with
        | .known funcId arity accArgs _ _ =>
          let totalArgs := accArgs ++ args
          if totalArgs.size >= arity && arity > 0 then
            let callArgs := totalArgs[:arity].toArray
            let extraArgs := if totalArgs.size > arity then totalArgs[arity:].toArray else #[]
            if extraArgs.isEmpty then
              let sigRetTy := match m.getFunc funcId with
                | some sf => match sf.asMono? with
                  | some f => if f.sig.retTy != .rawPtr then f.sig.retTy else retTy
                  | none => retTy
                | none => retTy
              newStmts := newStmts.push { stmt with inst := .call funcId callArgs sigRetTy }
              if let some rid := stmt.result then
                if sigRetTy != retTy then
                  typeUpdates := typeUpdates.insert rid.id sigRetTy
            else
              -- Over-saturated: direct call returns a closure, then apply remaining args
              let mut curId : LocalId := ⟨freshId⟩
              freshId := freshId + 1
              newStmts := newStmts.push
                { result := some curId, inst := .call funcId callArgs .rawPtr }
              for i in [:extraArgs.size] do
                let isLast := i == extraArgs.size - 1
                let resultId := if isLast then stmt.result else some ⟨freshId⟩
                if !isLast then freshId := freshId + 1
                let callRetTy := if isLast then retTy else .rawPtr
                newStmts := newStmts.push
                  { result := resultId
                  , inst := .callClosure (.local curId) #[extraArgs[i]!] callRetTy }
                if let some rid := resultId then
                  curId := rid
          else
            -- Under-saturated: keep the callClosure, update state
            state := spec.transfer state stmt
            newStmts := newStmts.push stmt
        | _ =>
          state := spec.transfer state stmt
          newStmts := newStmts.push stmt
      | _ =>
        state := spec.transfer state stmt
        newStmts := newStmts.push stmt
    | _ =>
      state := spec.transfer state stmt
      newStmts := newStmts.push stmt
  return ({ block with stmts := newStmts }, freshId, typeUpdates)

/-- Flatten makeClosure → callClosure chains across all blocks in a function -/
def flattenClosureChains (m : Module) (f : ClosedFunc) : ClosedFunc := Id.run do
  let some cfg := f.body | return f
  let spec := closureAnalysisSpec m

  -- Build initial state: function parameters are unknown closures
  let initState : Analysis.AbsState ClosureVal := {}

  -- Run the forward dataflow analysis
  let result := Analysis.forwardAnalysis spec cfg initState

  -- Rewrite blocks using the analysis results
  let predMap := Analysis.buildPredMap cfg
  let rpo := cfg.reversePostorder
  let mut newBlocks := cfg.blocks
  let mut freshId := f.nextLocalId
  let mut updatedLocalTypes := f.localTypes
  for bid in rpo do
    let some block := cfg.getBlock bid | continue
    let entryState := result.blockEntryState closureDomain predMap bid cfg.entry initState
    let (newBlock, newFreshId, typeUpdates) := rewriteBlockWithAnalysis m block entryState freshId
    newBlocks := newBlocks.insert bid.id newBlock
    freshId := newFreshId
    for (lid, ty) in typeUpdates.toArray do
      updatedLocalTypes := updatedLocalTypes.insert lid ty
  return { f with
    body := some { cfg with blocks := newBlocks }
    nextLocalId := freshId
    localTypes := updatedLocalTypes
  }

/-- Find the makeClosure instruction that produces a given local, checking expected target -/
private def findMakeClosureForLocal (cfg : ClosedCFG) (op : Operand) (expectedTarget : FuncId)
    : Option Operand :=
  match op with
  | .local lid =>
    cfg.blocks.toArray.findSome? fun (_, block) =>
      block.stmts.findSome? fun stmt =>
        match stmt.result with
        | some resultId =>
          if resultId == lid then
            match stmt.inst with
            | .makeClosure (.local funcId) _ env =>
              if funcId == expectedTarget then some env else none
            | _ => none
          else none
        | none => none
  | _ => none

/-- Try to rewrite a single call instruction using specialization map -/
private def tryRewriteCallInst (cfg : ClosedCFG) (inst : ClosedInst)
    (specMap : Std.HashMap SpecRequest FuncId) : ClosedInst :=
  match inst with
  | .call funcId args retTy =>
    let specEntries := specMap.toArray
    Id.run do
      for (req, specFuncId) in specEntries do
        if funcId == req.hofFuncId then
          if h : req.paramIdx < args.size then
            match args[req.paramIdx]'h with
            | .local _ =>
              match findMakeClosureForLocal cfg (args[req.paramIdx]'h) req.targetFuncId with
              | some envOp =>
                if req.hasEnv then
                  let newArgs := args.set (Fin.mk req.paramIdx h) envOp
                  return .call specFuncId newArgs retTy
                else
                  let newArgs := removeAt args req.paramIdx
                  return .call specFuncId newArgs retTy
              | none => pure ()
            | _ => pure ()
      return inst
  | _ => inst

/-- Rewrite all call sites in the module to use specialized versions -/
def rewriteCallSites (m : Module) (specMap : Std.HashMap SpecRequest FuncId)
    : Module := Id.run do
  let mut newFuncs : Array SomeFunc := #[]
  for sf in m.funcs do
    match sf.asMono? with
    | some f =>
      let f' := rewriteFuncCallSites f specMap
      newFuncs := newFuncs.push (SomeFunc.ofMono f')
    | none => newFuncs := newFuncs.push sf
  return { m with funcs := newFuncs }
where
  rewriteFuncCallSites (f : ClosedFunc) (specMap : Std.HashMap SpecRequest FuncId)
      : ClosedFunc := Id.run do
    let some cfg := f.body | return f
    let mut newBlocks : Std.HashMap Nat ClosedBlock := {}
    for (blockId, block) in cfg.blocks.toArray do
      let newStmts := block.stmts.map fun stmt =>
        { stmt with inst := tryRewriteCallInst cfg stmt.inst specMap }
      newBlocks := newBlocks.insert blockId { block with stmts := newStmts }
    return { f with body := some { cfg with blocks := newBlocks } }

/-- Run the closure specialization pass on a monomorphized module. Applies:
    1. Cross-function specialization (clone HOFs with known closures)
    2. Tiny function inlining (expose hidden closure chains)
    3. Closure chain flattening (replace saturated chains with direct calls)
    4. Call site rewriting (redirect callers to specialized versions)
    5. Dead code elimination (remove dead makeClosure/callClosure instructions) -/
def closureSpec (m : Module) : Module := Id.run do
  let mut module := m
  for _round in [:3] do
    let closureCountBefore := countCallClosures module

    let mut closureParamMap : Std.HashMap Nat (Array ClosureParamInfo) := {}
    for sf in module.funcs do
      if let some f := sf.asMono? then
        let cps := findClosureParams f
        if !cps.isEmpty then
          pure ()
          closureParamMap := closureParamMap.insert f.id.id cps

    let requests := findSpecRequests module closureParamMap

    let mut specMap : Std.HashMap SpecRequest FuncId := {}
    if !requests.isEmpty then
      let mut nextFuncId := module.funcs.size
      let mut newFuncs := module.funcs
      for req in requests do
        let some origFunc := getMonoFunc? module req.hofFuncId | continue
        let specFuncId := FuncId.mk nextFuncId
        nextFuncId := nextFuncId + 1
        let specFunc := specializeFunc module origFunc req specFuncId
        newFuncs := newFuncs.push (SomeFunc.ofMono specFunc)
        specMap := specMap.insert req specFuncId
      module := { module with funcs := newFuncs }

    if !specMap.isEmpty then
      module := rewriteCallSites module specMap

    let inlinedFuncs := module.funcs.map fun sf =>
      match sf.asMono? with
      | some f => SomeFunc.ofMono (inlineTinyFuncsInFunc module f)
      | none => sf
    module := { module with funcs := inlinedFuncs }

    let flattenedFuncs := module.funcs.map fun sf =>
      match sf.asMono? with
      | some f => SomeFunc.ofMono (flattenClosureChains module f)
      | none => sf
    module := { module with funcs := flattenedFuncs }

    let dceFuncs := module.funcs.map fun sf =>
      match sf.asMono? with
      | some f => SomeFunc.ofMono (dceFunc f)
      | none => sf
    module := { module with funcs := dceFuncs }

    let closureCountAfter := countCallClosures module
    if closureCountAfter >= closureCountBefore then
      break

  module := Somac.Alloy.Monomorphize.deadFunctionElimination module
  return module

end Somac.Alloy.ClosureSpec
