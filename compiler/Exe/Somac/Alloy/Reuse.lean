import Somac.Alloy.Func

namespace Somac.Alloy.Reuse

open Somac.Alloy

/-- Runtime pool size classes -/
inductive SizeClass where
  | pool48   -- ≤ 48 bytes
  | pool112  -- ≤ 112 bytes
  | large    -- > 112 bytes (malloc)
  deriving BEq, Repr, Inhabited

/-- Compute the pool size class for a tagged payload with `fieldCount` fields -/
def payloadSizeClass (fieldCount : Nat) : SizeClass :=
  let bytes := 16 + fieldCount * 8
  if bytes ≤ 48 then .pool48
  else if bytes ≤ 112 then .pool112
  else .large

/-- A reuse token represents a dead payload buffer available for in-place reuse -/
structure ReuseToken where
  /-- The local holding the payload pointer (extracted from the tagged struct) -/
  payloadLocal : LocalId
  /-- The statement index of the erase instruction (for suppression) -/
  eraseStmtIdx : Nat
  /-- The statement index of the extractField that produced the payload pointer -/
  extractStmtIdx : Nat
  /-- Number of fields in the original payload -/
  fieldCount : Nat
  /-- Pool size class -/
  sizeClass : SizeClass
  deriving Repr, Inhabited

/-- Check if an operand references a given local -/
private def opRefsLocal (op : Operand) (lid : LocalId) : Bool :=
  match op with
  | .local id => id == lid
  | _ => false

/-- Check if an instruction uses a local (as any operand) -/
private def instUsesLocal (inst : ClosedInst) (lid : LocalId) : Bool :=
  match inst with
  | .binOp _ l r _ => opRefsLocal l lid || opRefsLocal r lid
  | .unOp _ o => opRefsLocal o lid
  | .copy o => opRefsLocal o lid
  | .load o _ => opRefsLocal o lid
  | .store v p => opRefsLocal v lid || opRefsLocal p lid
  | .getFieldPtr o _ _ => opRefsLocal o lid
  | .getElemPtr o i _ => opRefsLocal o lid || opRefsLocal i lid
  | .extractField o _ => opRefsLocal o lid
  | .insertField o _ v => opRefsLocal o lid || opRefsLocal v lid
  | .call _ args _ => args.any (opRefsLocal · lid)
  | .callPoly _ _ args _ => args.any (opRefsLocal · lid)
  | .callIndirect f args _ => opRefsLocal f lid || args.any (opRefsLocal · lid)
  | .callClosure f args _ => opRefsLocal f lid || args.any (opRefsLocal · lid)
  | .callExtern _ args _ => args.any (opRefsLocal · lid)
  | .callIntrinsic _ args _ => args.any (opRefsLocal · lid)
  | .makeClosure _ env => opRefsLocal env lid
  | .makeClosurePoly _ _ env => opRefsLocal env lid
  | .makeClosureDyn f env _ => opRefsLocal f lid || opRefsLocal env lid
  | .taggedLit _ fields _ => fields.any (opRefsLocal · lid)
  | .reuseTaggedLit _ fields r _ => opRefsLocal r lid || fields.any (opRefsLocal · lid)
  | .structLit fields _ => fields.any (opRefsLocal · lid)
  | .arrayLit elems _ => elems.any (opRefsLocal · lid)
  | .getTag o => opRefsLocal o lid
  | .getPayload o _ _ _ => opRefsLocal o lid
  | .erase o _ => opRefsLocal o lid
  | .closureFunc o => opRefsLocal o lid
  | .closureEnv o => opRefsLocal o lid
  | .phi incoming _ => incoming.any fun (o, _) => opRefsLocal o lid
  | .select c t e => opRefsLocal c lid || opRefsLocal t lid || opRefsLocal e lid
  | .memcpy d s sz => opRefsLocal d lid || opRefsLocal s lid || opRefsLocal sz lid
  | .memset d v sz => opRefsLocal d lid || opRefsLocal v lid || opRefsLocal sz lid
  | .lazySup _ o _ => opRefsLocal o lid
  | .supProj0 o _ => opRefsLocal o lid
  | .supProj1 o _ => opRefsLocal o lid
  | _ => false

/-- Extract the field count from a tagged type's variant list for a given tag -/
private def taggedFieldCount (ty : ClosedTy) : Nat :=
  match ty with
  | .tagged _ variants =>
    variants.foldl (fun acc (_, fields) => max acc fields.size) 0
  | _ => 0

/-- Find a compatible reuse token: same pool size class, new fields fit in old buffer -/
private def findCompatibleToken (tokens : Array ReuseToken) (allocSizeClass : SizeClass)
    (newFieldCount : Nat) : Option Nat :=
  tokens.findIdx? fun tok => tok.sizeClass == allocSizeClass && newFieldCount ≤ tok.fieldCount

/-- Remove element at index from an array of ReuseTokens -/
private def removeTokenAt (tokens : Array ReuseToken) (idx : Nat) : Array ReuseToken := Id.run do
  let mut result : Array ReuseToken := #[]
  for h : i in [:tokens.size] do
    if i != idx then
      result := result.push tokens[i]
  return result

/-- Scan a single basic block for reuse opportunities -/
def scanBlock (block : ClosedBlock) (localTypes : Std.HashMap Nat ClosedTy)
    : ClosedBlock × Nat := Id.run do
  let mut availableTokens : Array ReuseToken := #[]
  let mut suppressedErases : Std.HashSet Nat := {}
  let mut rewriteMap : Std.HashMap Nat (Nat × LocalId) := {}
  let mut reuseCount : Nat := 0

  let mut payloadExtractMap : Std.HashMap Nat (Nat × LocalId) := {}
  for i in [:block.stmts.size] do
    let stmt := block.stmts[i]!
    match stmt.inst, stmt.result with
    | .extractField (.local scrutinee) 1, some resultId =>
      match localTypes.get? scrutinee.id with
      | some (.tagged _ _) =>
        payloadExtractMap := payloadExtractMap.insert resultId.id (i, scrutinee)
      | _ => pure ()
    | _, _ => pure ()

  for i in [:block.stmts.size] do
    let stmt := block.stmts[i]!
    match stmt.inst with
    | .erase (.local erasedLocal) (.tagged _ variants) =>
      let fieldCount := variants.foldl (fun acc (_, fields) => max acc fields.size) 0
      let mut foundPayload : Option (LocalId × Nat) := none
      for j in [:i] do
        let prevStmt := block.stmts[j]!
        match prevStmt.inst, prevStmt.result with
        | .extractField (.local src) 1, some rid =>
          if src == erasedLocal then
            foundPayload := some (rid, j)
        | _, _ => pure ()
      match foundPayload with
      | some (payloadLocal, extractIdx) =>
        availableTokens := availableTokens.push {
          payloadLocal
          eraseStmtIdx := i
          extractStmtIdx := extractIdx
          fieldCount
          sizeClass := payloadSizeClass fieldCount
        }
      | none => pure ()
    | _ =>
      -- Invalidate any token whose payload pointer is used by this instruction
      availableTokens := availableTokens.filter fun token =>
        -- Don't invalidate if this instruction is the erase or extract we already recorded
        i != token.eraseStmtIdx && i != token.extractStmtIdx &&
        !instUsesLocal stmt.inst token.payloadLocal

  -- Reset available tokens and rescan to get correct ordering
  availableTokens := #[]
  for i in [:block.stmts.size] do
    let stmt := block.stmts[i]!
    match stmt.inst with
    | .erase (.local erasedLocal) (.tagged _ variants) =>
      let fieldCount := variants.foldl (fun acc (_, fields) => max acc fields.size) 0
      let mut foundPayload : Option (LocalId × Nat) := none
      for j in [:i] do
        let prevStmt := block.stmts[j]!
        match prevStmt.inst, prevStmt.result with
        | .extractField (.local src) 1, some rid =>
          if src == erasedLocal then
            foundPayload := some (rid, j)
        | _, _ => pure ()
      match foundPayload with
      | some (payloadLocal, extractIdx) =>
        availableTokens := availableTokens.push {
          payloadLocal
          eraseStmtIdx := i
          extractStmtIdx := extractIdx
          fieldCount
          sizeClass := payloadSizeClass fieldCount
        }
      | none => pure ()
    | .taggedLit _tag fields (.tagged _ _) =>
      -- Look for a compatible reuse token
      let allocSizeClass := payloadSizeClass fields.size
      match findCompatibleToken availableTokens allocSizeClass fields.size with
      | some tokenIdx =>
        let tokens := availableTokens
        let tok : ReuseToken := tokens[tokenIdx]!
        let eraseIdx := tok.eraseStmtIdx
        let payloadLid := tok.payloadLocal
        -- Record the rewrite: suppress the erase, replace taggedLit with reuseTaggedLit
        suppressedErases := suppressedErases.insert eraseIdx
        rewriteMap := rewriteMap.insert i (eraseIdx, payloadLid)
        availableTokens := removeTokenAt availableTokens tokenIdx
        reuseCount := reuseCount + 1
      | none => pure ()
    | _ =>
      -- Invalidate tokens whose payload is used
      availableTokens := availableTokens.filter fun token =>
        i != token.eraseStmtIdx && i != token.extractStmtIdx &&
        !instUsesLocal stmt.inst token.payloadLocal

  if reuseCount == 0 then
    return (block, 0)

  let mut newStmts : Array ClosedStmt := #[]
  for i in [:block.stmts.size] do
    let stmt := block.stmts[i]!
    if suppressedErases.contains i then
      continue
    else if let some (_, payloadLocal) := rewriteMap.get? i then
      -- Replace taggedLit with reuseTaggedLit
      match stmt.inst with
      | .taggedLit tag fields ty =>
        newStmts := newStmts.push { stmt with
          inst := .reuseTaggedLit tag fields (.local payloadLocal) ty
        }
      | _ => newStmts := newStmts.push stmt
    else
      newStmts := newStmts.push stmt

  return ({ block with stmts := newStmts }, reuseCount)

/-- Apply reuse analysis to a single function -/
def reuseFunc (f : ClosedFunc) : ClosedFunc × Nat := Id.run do
  let some cfg := f.body | return (f, 0)
  let mut totalReuses : Nat := 0
  let mut newBlocks : Std.HashMap Nat ClosedBlock := {}

  for (blockId, block) in cfg.blocks.toArray do
    let (newBlock, reuses) := scanBlock block f.localTypes
    newBlocks := newBlocks.insert blockId newBlock
    totalReuses := totalReuses + reuses

  if totalReuses == 0 then
    return (f, 0)

  return ({ f with body := some { cfg with blocks := newBlocks } }, totalReuses)

/-- Apply reuse analysis to all functions in a module -/
def reuseModule (m : Module) : Module × Nat := Id.run do
  let mut totalReuses : Nat := 0
  let mut newFuncs : Array SomeFunc := #[]

  for sf in m.funcs do
    match sf.asMono? with
    | some f =>
      let (newFunc, reuses) := reuseFunc f
      newFuncs := newFuncs.push (SomeFunc.ofMono newFunc)
      totalReuses := totalReuses + reuses
    | none => newFuncs := newFuncs.push sf

  return ({ m with funcs := newFuncs }, totalReuses)

end Somac.Alloy.Reuse
