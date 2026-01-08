/-
  Alloy IR Basic Blocks

  A basic block is a sequence of instructions with:
  - A single entry point (the block label)
  - A single exit point (the terminator)
  - No internal control flow

  Instructions within a block execute sequentially. Control flow
  between blocks is explicit via terminators.
-/

import Soma.Alloy.Inst
import Std.Data.HashMap
import Std.Data.HashSet

namespace Soma.Alloy

/-! ## Statements -/

/-- A statement binds an instruction result to a local -/
structure Stmt where
  /-- The local receiving the result (none for void instructions) -/
  result : Option LocalId
  /-- The instruction -/
  inst : Inst
  deriving Repr, Inhabited

namespace Stmt

/-- Create a statement with a result -/
def withResult (result : LocalId) (inst : Inst) : Stmt :=
  ⟨some result, inst⟩

/-- Create a void statement (no result) -/
def void (inst : Inst) : Stmt :=
  ⟨none, inst⟩

instance : ToString Stmt where
  toString s :=
    match s.result with
    | some r => s!"{r} = {s.inst}"
    | none => ToString.toString s.inst

end Stmt

/-! ## Basic Blocks -/

/-- A basic block: a sequence of statements ending with a terminator -/
structure Block where
  /-- Block identifier -/
  id : BlockId
  /-- Optional label for debugging -/
  label : Option String := none
  /-- Block parameters (for phi-like semantics) -/
  params : Array (LocalId × Ty) := #[]
  /-- Statements in execution order -/
  stmts : Array Stmt := #[]
  /-- Block terminator -/
  terminator : Terminator
  deriving Repr, Inhabited

namespace Block

/-- Create an entry block -/
def entry (terminator : Terminator) : Block :=
  { id := .entry, terminator }

/-- Create a block with a label -/
def labeled (id : BlockId) (label : String) (terminator : Terminator) : Block :=
  { id, label := some label, terminator }

/-- Add a statement to a block -/
def addStmt (b : Block) (s : Stmt) : Block :=
  { b with stmts := b.stmts.push s }

/-- Add multiple statements -/
def addStmts (b : Block) (ss : Array Stmt) : Block :=
  { b with stmts := b.stmts ++ ss }

/-- Set the terminator -/
def withTerminator (b : Block) (t : Terminator) : Block :=
  { b with terminator := t }

/-- Add a parameter -/
def addParam (b : Block) (p : LocalId) (ty : Ty) : Block :=
  { b with params := b.params.push (p, ty) }

/-- Get all successor block IDs -/
def successors (b : Block) : Array BlockId :=
  b.terminator.successors

/-- Get all locals defined in this block -/
def definedLocals (b : Block) : Array LocalId :=
  let paramLocals := b.params.map (·.1)
  let stmtLocals := b.stmts.filterMap (·.result)
  paramLocals ++ stmtLocals

/-- Get all locals used in this block -/
def usedLocals (b : Block) : Array LocalId :=
  let fromStmts := b.stmts.foldl (fun acc s => acc ++ extractLocals s.inst) #[]
  let fromTerm := extractTermLocals b.terminator
  fromStmts ++ fromTerm
where
  extractOperandLocal : Operand → Option LocalId
    | .local id => some id
    | _ => none

  extractLocals (inst : Inst) : Array LocalId :=
    match inst with
    | .binOp _ lhs rhs _ => #[lhs, rhs].filterMap extractOperandLocal
    | .unOp _ op => #[op].filterMap extractOperandLocal
    | .copy src => #[src].filterMap extractOperandLocal
    | .alloca _ => #[]
    | .malloc size => #[size].filterMap extractOperandLocal
    | .free ptr => #[ptr].filterMap extractOperandLocal
    | .load ptr _ => #[ptr].filterMap extractOperandLocal
    | .store ptr val => #[ptr, val].filterMap extractOperandLocal
    | .getFieldPtr base _ _ => #[base].filterMap extractOperandLocal
    | .getElemPtr base idx _ => #[base, idx].filterMap extractOperandLocal
    | .extractField val _ => #[val].filterMap extractOperandLocal
    | .insertField val _ newVal => #[val, newVal].filterMap extractOperandLocal
    | .extractElem val idx => #[val, idx].filterMap extractOperandLocal
    | .insertElem val idx newVal => #[val, idx, newVal].filterMap extractOperandLocal
    | .structLit fields _ => fields.filterMap extractOperandLocal
    | .arrayLit elems _ => elems.filterMap extractOperandLocal
    | .getTag val => #[val].filterMap extractOperandLocal
    | .getPayload val _ _ => #[val].filterMap extractOperandLocal
    | .taggedLit _ payload _ => payload.filterMap extractOperandLocal
    | .call _ args _ => args.filterMap extractOperandLocal
    | .callIndirect ptr args _ => (#[ptr] ++ args).filterMap extractOperandLocal
    | .callClosure closure args _ => (#[closure] ++ args).filterMap extractOperandLocal
    | .makeClosure _ env => #[env].filterMap extractOperandLocal
    | .closureFunc closure => #[closure].filterMap extractOperandLocal
    | .closureEnv closure => #[closure].filterMap extractOperandLocal
    | .phi incoming _ => incoming.map (·.1) |>.filterMap extractOperandLocal
    | .select cond t e => #[cond, t, e].filterMap extractOperandLocal
    | .memcpy dst src size => #[dst, src, size].filterMap extractOperandLocal
    | .memset dst val size => #[dst, val, size].filterMap extractOperandLocal
    | .clone src _ => #[src].filterMap extractOperandLocal
    | .erase val _ => #[val].filterMap extractOperandLocal
    | .panic _ _ => #[]
    | .intrinsic _ args _ => args.filterMap extractOperandLocal

  extractTermLocals : Terminator → Array LocalId
    | .jump _ => #[]
    | .branch cond _ _ => #[cond].filterMap extractOperandLocal
    | .switch val _ _ => #[val].filterMap extractOperandLocal
    | .ret val => #[val].filterMap extractOperandLocal
    | .retUnit | .unreachable => #[]

instance : ToString Block where
  toString b :=
    let labelStr := match b.label with
      | some l => s!" ; {l}"
      | none => ""
    let paramsStr := if b.params.isEmpty then ""
      else
        let ps := String.intercalate ", " (b.params.toList.map fun (p, t) => s!"{p}: {t}")
        s!"({ps})"
    let stmtsStr := String.intercalate "\n  " (b.stmts.toList.map ToString.toString)
    let header := s!"{b.id}{paramsStr}:{labelStr}"
    if b.stmts.isEmpty then
      s!"{header}\n  {b.terminator}"
    else
      s!"{header}\n  {stmtsStr}\n  {b.terminator}"

end Block

/-! ## Control Flow Graph -/

/-- A control flow graph is a collection of basic blocks -/
structure CFG where
  /-- All blocks, indexed by BlockId -/
  blocks : Std.HashMap Nat Block := {}
  /-- Entry block ID -/
  entry : BlockId := .entry
  /-- Next available block ID -/
  nextBlockId : Nat := 1
  deriving Inhabited

namespace CFG

/-- Create an empty CFG -/
def empty : CFG := {}

/-- Create a CFG with just an entry block -/
def withEntry (entryBlock : Block) : CFG :=
  { blocks := ({} : Std.HashMap Nat Block).insert 0 entryBlock
  , entry := .entry
  , nextBlockId := 1
  }

/-- Allocate a fresh block ID -/
def freshBlockId (cfg : CFG) : BlockId × CFG :=
  (⟨cfg.nextBlockId⟩, { cfg with nextBlockId := cfg.nextBlockId + 1 })

/-- Add a block to the CFG -/
def addBlock (cfg : CFG) (b : Block) : CFG :=
  let nextId := max cfg.nextBlockId (b.id.id + 1)
  { cfg with
    blocks := cfg.blocks.insert b.id.id b
    nextBlockId := nextId
  }

/-- Get a block by ID -/
def getBlock (cfg : CFG) (id : BlockId) : Option Block :=
  cfg.blocks.get? id.id

/-- Update a block -/
def updateBlock (cfg : CFG) (id : BlockId) (f : Block → Block) : CFG :=
  match cfg.blocks.get? id.id with
  | some b => { cfg with blocks := cfg.blocks.insert id.id (f b) }
  | none => cfg

/-- Get all blocks in order -/
def allBlocks (cfg : CFG) : Array Block :=
  cfg.blocks.toArray
    |>.qsort (fun a b => a.1 < b.1)
    |>.map (·.2)

/-- Get the entry block -/
def entryBlock (cfg : CFG) : Option Block :=
  cfg.getBlock cfg.entry

/-- Count blocks -/
def blockCount (cfg : CFG) : Nat :=
  cfg.blocks.size

/-- Get predecessors of a block -/
def predecessors (cfg : CFG) (id : BlockId) : Array BlockId :=
  cfg.allBlocks.foldl (fun acc b =>
    if b.successors.contains id then acc.push b.id else acc
  ) #[]

/-- Check if CFG is well-formed (all successors exist) -/
def isWellFormed (cfg : CFG) : Bool :=
  cfg.allBlocks.all fun b =>
    b.successors.all fun succ => cfg.blocks.contains succ.id

/-- Compute reverse postorder (for dataflow analysis) -/
partial def reversePostorder (cfg : CFG) : Array BlockId :=
  let rec dfs (visited : Std.HashSet Nat) (order : Array BlockId) (id : BlockId)
      : Std.HashSet Nat × Array BlockId :=
    if visited.contains id.id then (visited, order)
    else
      let visited' := visited.insert id.id
      match cfg.getBlock id with
      | none => (visited', order)
      | some b =>
        let (visited'', order') := b.successors.foldl
          (fun (v, o) succ => dfs v o succ) (visited', order)
        (visited'', order'.push id)
  let (_, order) := dfs {} #[] cfg.entry
  order.reverse

instance : ToString CFG where
  toString cfg :=
    let blocksStr := String.intercalate "\n\n" (cfg.allBlocks.toList.map ToString.toString)
    s!"CFG (entry: {cfg.entry}, {cfg.blockCount} blocks):\n{blocksStr}"

end CFG

end Soma.Alloy
