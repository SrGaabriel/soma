import Somac.Alloy.Func
import Somac.Alloy.Analysis
import Somac.Alloy.DefUse
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Alloy.Reuse

open Somac.Alloy
open Somac.Alloy.Analysis

/-- Runtime pool size classes -/
inductive SizeClass where
  | pool48   -- ≤ 48 bytes
  | pool112  -- ≤ 112 bytes
  | large    -- > 112 bytes (malloc)
  deriving BEq, Repr, Inhabited

/-- Compute the pool size class for a tagged payload with `fieldCount` fields -/
def payloadSizeClass (fieldCount : Nat) (ptrBytes : Nat) : SizeClass :=
  let bytes := ptrBytes * 2 + fieldCount * ptrBytes
  if bytes ≤ 48 then .pool48
  else if bytes ≤ 112 then .pool112
  else .large

/-- A reuse token represents a dead payload buffer available for in-place reuse -/
structure ReuseToken where
  /-- The LocalId holding the payload pointer (from `extractField scrutinee 1`) -/
  payloadLocal : LocalId
  /-- The LocalId of the tagged value being erased (the scrutinee) -/
  erasedLocal : LocalId
  /-- Maximum field count of the original payload (determines buffer size) -/
  fieldCount : Nat
  /-- Pool size class of the original payload -/
  sizeClass : SizeClass
  deriving Repr, Inhabited, BEq

instance : Hashable ReuseToken where
  hash t := mixHash (hash t.payloadLocal.id) (hash t.erasedLocal.id)

/-- The abstract state for reuse analysis: a set of available reuse tokens -/
structure TokenSet where
  tokens : Std.HashMap Nat ReuseToken := {}
  deriving Inhabited

namespace TokenSet

def empty : TokenSet := {}

def insert (s : TokenSet) (t : ReuseToken) : TokenSet :=
  { tokens := s.tokens.insert t.payloadLocal.id t }

def remove (s : TokenSet) (payloadId : Nat) : TokenSet :=
  { tokens := s.tokens.erase payloadId }

def contains (s : TokenSet) (payloadId : Nat) : Bool :=
  s.tokens.contains payloadId

/-- Intersection: keep only tokens present in both sets (with matching fields) -/
def intersect (a b : TokenSet) : TokenSet :=
  let merged := a.tokens.fold (init := ({} : Std.HashMap Nat ReuseToken)) fun acc k tokA =>
    match b.tokens.get? k with
    | some tokB =>
      -- Both paths provide this token; keep it if they agree on the buffer
      if tokA.payloadLocal == tokB.payloadLocal &&
         tokA.fieldCount == tokB.fieldCount &&
         tokA.sizeClass == tokB.sizeClass then
        acc.insert k tokA
      else acc
    | none => acc
  { tokens := merged }

def beq (a b : TokenSet) : Bool :=
  a.tokens.size == b.tokens.size &&
  a.tokens.fold (init := true) fun eq k tokA =>
    eq && match b.tokens.get? k with
    | some tokB => tokA == tokB
    | none => false

end TokenSet

/-- Collect all LocalIds referenced by an instruction's operands -/
private def instOperandLocals (inst : ClosedInst) : Array LocalId :=
  inst.localUses

/-- Check if an instruction uses a specific local (as any operand) -/
private def instUsesLocal (inst : ClosedInst) (lid : LocalId) : Bool :=
  (instOperandLocals inst).any (· == lid)

/-- Information about an erase site within a block -/
structure EraseSite where
  /-- Statement index of the erase instruction -/
  stmtIdx : Nat
  /-- The local being erased -/
  erasedLocal : LocalId
  /-- The payload pointer local -/
  payloadLocal : LocalId
  /-- Statement index of the extractField that produced the payload pointer -/
  extractStmtIdx : Nat
  /-- Maximum field count across all variants -/
  fieldCount : Nat
  /-- Pool size class -/
  sizeClass : SizeClass
  deriving Repr, Inhabited

/-- Information about a taggedLit allocation site within a block -/
structure AllocSite where
  /-- Statement index of the taggedLit instruction -/
  stmtIdx : Nat
  /-- Number of fields in the new allocation -/
  fieldCount : Nat
  /-- Pool size class needed -/
  sizeClass : SizeClass
  deriving Repr, Inhabited

/-- Pre-scan a block to identify erase sites and their associated payload extractions -/
def preAnalyzeBlock (block : ClosedBlock) (localTypes : Std.HashMap Nat ClosedTy)
    (ptrBytes : Nat) : Array EraseSite := Id.run do
  let mut payloadExtractMap : Std.HashMap Nat (Nat × LocalId) := {}
  for h : i in [:block.stmts.size] do
    let stmt := block.stmts[i]
    match stmt.inst, stmt.result with
    | .extractField (.local scrutinee) 1, some resultId =>
      match localTypes.get? scrutinee.id with
      | some (.tagged _ _) =>
        payloadExtractMap := payloadExtractMap.insert resultId.id (i, scrutinee)
      | _ => pure ()
    | _, _ => pure ()

  let mut eraseSites : Array EraseSite := #[]
  for h : i in [:block.stmts.size] do
    let stmt := block.stmts[i]
    match stmt.inst with
    | .erase (.local erasedLocal) (.tagged _ variants) =>
      let fieldCount := variants.foldl (fun acc (_, fields) => max acc fields.size) 0
      -- Search for the extractField that gave us the payload pointer for this scrutinee
      -- Look backward: extractField %erasedLocal 1 → %payloadLocal
      let mut foundPayload : Option (LocalId × Nat) := none
      for j in [:i] do
        if h2 : j < block.stmts.size then
          let prevStmt := block.stmts[j]
          match prevStmt.inst, prevStmt.result with
          | .extractField (.local src) 1, some rid =>
            if src == erasedLocal then
              foundPayload := some (rid, j)
          | _, _ => pure ()
      match foundPayload with
      | some (payloadLocal, extractIdx) =>
        eraseSites := eraseSites.push {
          stmtIdx := i
          erasedLocal
          payloadLocal
          extractStmtIdx := extractIdx
          fieldCount
          sizeClass := payloadSizeClass fieldCount ptrBytes
        }
      | none => pure ()
    | _ => pure ()

  return eraseSites
private def _tokenSetKey : Nat := 0

/-- Check if a reuse token is compatible with an allocation request -/
private def isCompatible (token : ReuseToken) (allocSizeClass : SizeClass)
    (allocFieldCount : Nat) : Bool :=
  token.sizeClass == allocSizeClass && allocFieldCount ≤ token.fieldCount

/-- Find the best compatible token for an allocation -/
private def findBestToken (tokens : TokenSet) (allocSizeClass : SizeClass)
    (allocFieldCount : Nat) : Option ReuseToken := Id.run do
  let mut best : Option ReuseToken := none
  let mut bestWaste : Nat := Nat.succ 0
  let _ := bestWaste
  for entry in tokens.tokens.toArray do
    let tok := entry.2
    if isCompatible tok allocSizeClass allocFieldCount then
      let waste := tok.fieldCount - allocFieldCount
      match best with
      | none =>
        best := some tok
        bestWaste := waste
      | some _ =>
        if waste < bestWaste then
          best := some tok
          bestWaste := waste
  return best

/-- A matched reuse pair: an erase site whose payload buffer will be reused -/
structure ReusePair where
  /-- Block containing the erase -/
  eraseBlockId : Nat
  /-- Statement index of the erase within its block -/
  eraseStmtIdx : Nat
  /-- Block containing the taggedLit -/
  allocBlockId : Nat
  /-- Statement index of the taggedLit within its block -/
  allocStmtIdx : Nat
  /-- The payload pointer local to reuse -/
  payloadLocal : LocalId
  deriving Repr

/-- Run reuse analysis on a single function
    The algorithm:
    1. Pre-analyze each block to find erase sites and their payload extractions
    2. Forward-scan each block: erase → produce token, taggedLit → consume token,
       other use of payload → kill token. Tokens flow across blocks via
       intersection at merge points (computed by fixpoint iteration).
    3. Collect matched pairs and rewrite the function. -/
def reuseFunc (f : ClosedFunc) (ptrBytes : Nat) : ClosedFunc × Nat := Id.run do
  let some cfg := f.body | return (f, 0)

  -- Pre-analyze all blocks to find erase sites
  let mut blockEraseSites : Std.HashMap Nat (Array EraseSite) := {}
  for entry in cfg.blocks.toArray do
    let blockId := entry.1
    let block := entry.2
    let sites := preAnalyzeBlock block f.localTypes ptrBytes
    if !sites.isEmpty then
      blockEraseSites := blockEraseSites.insert blockId sites

  -- Early exit if no erase sites exist
  if blockEraseSites.isEmpty then
    return (f, 0)

  -- Step 2: Forward dataflow analysis using custom iteration
  let rpo := cfg.reversePostorder
  let predMap := Analysis.buildPredMap cfg

  let mut exitTokens : Std.HashMap Nat TokenSet := {}
  let mut reusePairs : Array ReusePair := #[]
  let maxIters := 30

  for _iter in [:maxIters] do
    let mut changed := false
    reusePairs := #[]

    for bid in rpo do
      let mut entryTokens : TokenSet := TokenSet.empty
      if bid != cfg.entry then
        let preds := predMap.getD bid.id #[]
        if !preds.isEmpty then
          let mut first := true
          for predId in preds do
            match exitTokens.get? predId.id with
            | some predExit =>
              if first then
                entryTokens := predExit
                first := false
              else
                entryTokens := TokenSet.intersect entryTokens predExit
            | none =>
              entryTokens := TokenSet.empty
              first := false

      let some block := cfg.getBlock bid | continue

      let mut tokens := entryTokens

      for h : i in [:block.stmts.size] do
        let stmt := block.stmts[i]
        match stmt.inst with
        | .erase (.local erasedLocal) (.tagged _ variants) =>
          -- Check if this erase site has a known payload extraction
          let sites := blockEraseSites.getD bid.id #[]
          for site in sites do
            if site.stmtIdx == i && site.erasedLocal == erasedLocal then
              tokens := tokens.insert {
                payloadLocal := site.payloadLocal
                erasedLocal := site.erasedLocal
                fieldCount := site.fieldCount
                sizeClass := site.sizeClass
              }

        | .taggedLit _tag fields (.tagged _ _) =>
          -- Try to consume a compatible token
          let allocSizeClass := payloadSizeClass fields.size ptrBytes
          match findBestToken tokens allocSizeClass fields.size with
          | some tok =>
            reusePairs := reusePairs.push {
              eraseBlockId := bid.id
              eraseStmtIdx := 0
              allocBlockId := bid.id
              allocStmtIdx := i
              payloadLocal := tok.payloadLocal
            }
            -- Consume the token
            tokens := tokens.remove tok.payloadLocal.id
          | none => pure ()

        | _ =>
          let usedLocals := instOperandLocals stmt.inst
          for lid in usedLocals do
            if tokens.contains lid.id then
              tokens := tokens.remove lid.id

      -- Check convergence
      let prevExit := exitTokens.getD bid.id TokenSet.empty
      if !TokenSet.beq tokens prevExit then
        changed := true
        exitTokens := exitTokens.insert bid.id tokens

    if !changed then break

  -- Rewrite the function
  if reusePairs.isEmpty then
    return (f, 0)

  -- Build a map: payloadLocal.id → (eraseBlockId, eraseStmtIdx)
  let mut eraseLocationMap : Std.HashMap Nat (Nat × Nat) := {}
  for entry in cfg.blocks.toArray do
    let blockId := entry.1
    let sites := blockEraseSites.getD blockId #[]
    for site in sites do
      eraseLocationMap := eraseLocationMap.insert site.payloadLocal.id (blockId, site.stmtIdx)

  -- Now resolve each reuse pair to its actual erase location
  let mut suppressedErases : Std.HashSet (Nat × Nat) := {}  -- (blockId, stmtIdx)
  let mut reuseRewrites : Std.HashMap (Nat × Nat) LocalId := {}  -- (blockId, stmtIdx) → payloadLocal

  for pair in reusePairs do
    match eraseLocationMap.get? pair.payloadLocal.id with
    | some (eraseBlock, eraseIdx) =>
      suppressedErases := suppressedErases.insert (eraseBlock, eraseIdx)
      reuseRewrites := reuseRewrites.insert (pair.allocBlockId, pair.allocStmtIdx) pair.payloadLocal
    | none => pure ()  -- shouldn't happen

  let reuseCount := reuseRewrites.size

  if reuseCount == 0 then
    return (f, 0)

  -- Rewrite blocks
  let mut newBlocks : Std.HashMap Nat ClosedBlock := {}
  for entry in cfg.blocks.toArray do
    let blockId := entry.1
    let block := entry.2
    let mut newStmts : Array ClosedStmt := #[]
    for h : i in [:block.stmts.size] do
      let stmt := block.stmts[i]
      if suppressedErases.contains (blockId, i) then
        continue
      else if let some payloadLocal := reuseRewrites.get? (blockId, i) then
        -- Replace taggedLit with reuseTaggedLit
        match stmt.inst with
        | .taggedLit tag fields ty =>
          newStmts := newStmts.push { stmt with
            inst := .reuseTaggedLit tag fields (.local payloadLocal) ty
          }
        | _ => newStmts := newStmts.push stmt
      else
        newStmts := newStmts.push stmt
    newBlocks := newBlocks.insert blockId { block with stmts := newStmts }

  let newCfg := { cfg with blocks := newBlocks }
  return ({ f with body := some newCfg }, reuseCount)

/-- Apply reuse analysis to all monomorphic functions in a module -/
def reuseModule (m : Module) (ptrBytes : Nat) : Module × Nat := Id.run do
  let mut totalReuses : Nat := 0
  let mut newFuncs : Array SomeFunc := #[]

  for sf in m.funcs do
    match sf.asMono? with
    | some f =>
      let (newFunc, reuses) := reuseFunc f ptrBytes
      newFuncs := newFuncs.push (SomeFunc.ofMono newFunc)
      totalReuses := totalReuses + reuses
    | none => newFuncs := newFuncs.push sf

  return ({ m with funcs := newFuncs }, totalReuses)

end Somac.Alloy.Reuse
