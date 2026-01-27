import Somac.Alloy.Inst
import Std.Data.HashMap
import Std.Data.HashSet
import Kenosis

namespace Somac.Alloy

/-- A statement binds an instruction result to a local -/
structure Stmt (n : Nat) where
  result : Option LocalId
  inst : Inst n

instance : Inhabited (Stmt n) where
  default := ⟨none, .copy (.const .unit)⟩

namespace Stmt

def withResult (result : LocalId) (inst : Inst n) : Stmt n :=
  ⟨some result, inst⟩

def void (inst : Inst n) : Stmt n :=
  ⟨none, inst⟩

/-- Instantiate all types in a statement -/
def instantiate (s : Stmt n) (env : TyEnv n) : Stmt 0 :=
  ⟨s.result, s.inst.instantiate env⟩

private def toStringAux : Stmt n → String
  | ⟨some r, inst⟩ => s!"{r} = {inst}"
  | ⟨none, inst⟩ => ToString.toString inst

instance : ToString (Stmt n) where
  toString := toStringAux

end Stmt

/-- Monomorphic statement -/
abbrev ClosedStmt := Stmt 0

/-- A basic block indexed by type variable count -/
structure Block (n : Nat) where
  id : BlockId
  label : Option String := none
  params : Array (LocalId × Ty n) := #[]
  stmts : Array (Stmt n) := #[]
  terminator : Terminator
  deriving Inhabited

namespace Block

def entry (terminator : Terminator) : Block n :=
  { id := .entry, terminator }

def labeled (id : BlockId) (label : String) (terminator : Terminator) : Block n :=
  { id, label := some label, terminator }

def addStmt (b : Block n) (s : Stmt n) : Block n :=
  { b with stmts := b.stmts.push s }

def addStmts (b : Block n) (ss : Array (Stmt n)) : Block n :=
  { b with stmts := b.stmts ++ ss }

def withTerminator (b : Block n) (t : Terminator) : Block n :=
  { b with terminator := t }

def addParam (b : Block n) (p : LocalId) (ty : Ty n) : Block n :=
  { b with params := b.params.push (p, ty) }

def successors (b : Block n) : Array BlockId :=
  b.terminator.successors

def definedLocals (b : Block n) : Array LocalId :=
  let paramLocals := b.params.map (·.1)
  let stmtLocals := b.stmts.filterMap (·.result)
  paramLocals ++ stmtLocals

/-- Instantiate all types in a block -/
def instantiate (b : Block n) (env : TyEnv n) : Block 0 :=
  { id := b.id
  , label := b.label
  , params := b.params.map fun (id, ty) => (id, Somac.Alloy.instantiate ty env)
  , stmts := b.stmts.map (·.instantiate env)
  , terminator := b.terminator
  }

private def toStringAux : Block n → String
  | b =>
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

instance : ToString (Block n) where
  toString := toStringAux

end Block

/-- Monomorphic block -/
abbrev ClosedBlock := Block 0

/-- A control flow graph indexed by type variable count -/
structure CFG (n : Nat) where
  blocks : Std.HashMap Nat (Block n) := {}
  entry : BlockId := .entry
  nextBlockId : Nat := 1
  deriving Inhabited

namespace CFG

def empty : CFG n := {}

def withEntry (entryBlock : Block n) : CFG n :=
  { blocks := ({} : Std.HashMap Nat (Block n)).insert 0 entryBlock
  , entry := .entry
  , nextBlockId := 1
  }

def freshBlockId (cfg : CFG n) : BlockId × CFG n :=
  (⟨cfg.nextBlockId⟩, { cfg with nextBlockId := cfg.nextBlockId + 1 })

def addBlock (cfg : CFG n) (b : Block n) : CFG n :=
  let nextId := max cfg.nextBlockId (b.id.id + 1)
  { cfg with
    blocks := cfg.blocks.insert b.id.id b
    nextBlockId := nextId
  }

def getBlock (cfg : CFG n) (id : BlockId) : Option (Block n) :=
  cfg.blocks.get? id.id

def updateBlock (cfg : CFG n) (id : BlockId) (f : Block n → Block n) : CFG n :=
  match cfg.blocks.get? id.id with
  | some b => { cfg with blocks := cfg.blocks.insert id.id (f b) }
  | none => cfg

def allBlocks (cfg : CFG n) : Array (Block n) :=
  cfg.blocks.toArray
    |>.qsort (fun a b => a.1 < b.1)
    |>.map (·.2)

def entryBlock (cfg : CFG n) : Option (Block n) :=
  cfg.getBlock cfg.entry

def blockCount (cfg : CFG n) : Nat :=
  cfg.blocks.size

def predecessors (cfg : CFG n) (id : BlockId) : Array BlockId :=
  cfg.allBlocks.foldl (fun acc b =>
    if b.successors.contains id then acc.push b.id else acc
  ) #[]

def isWellFormed (cfg : CFG n) : Bool :=
  cfg.allBlocks.all fun b =>
    b.successors.all fun succ => cfg.blocks.contains succ.id

/-- Instantiate all types in a CFG -/
def instantiate (cfg : CFG n) (env : TyEnv n) : CFG 0 :=
  let blocks' := cfg.blocks.fold
    (init := ({} : Std.HashMap Nat (Block 0))) fun acc id block =>
      acc.insert id (block.instantiate env)
  { blocks := blocks'
  , entry := cfg.entry
  , nextBlockId := cfg.nextBlockId
  }

partial def reversePostorder (cfg : CFG n) : Array BlockId :=
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

private def toStringAux : CFG n → String
  | cfg =>
    let blocksStr := String.intercalate "\n\n" (cfg.allBlocks.toList.map ToString.toString)
    s!"CFG (entry: {cfg.entry}, {cfg.blockCount} blocks):\n{blocksStr}"

instance : ToString (CFG n) where
  toString := toStringAux

end CFG

/-- Monomorphic CFG -/
abbrev ClosedCFG := CFG 0

end Somac.Alloy
