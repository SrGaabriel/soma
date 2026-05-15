import Soma.Core.Value
import Soma.Core.Eval
import Soma.Core.Quote
import Soma.Dependent.Monad
import Soma.Dependent.Unify.Core

namespace Soma.Dependent

open Soma.Core

/-- A partial renaming maps de Bruijn levels in the RHS to de Bruijn levels in the output -/
structure PartialRenaming where
  /-- Maps input de Bruijn levels to output de Bruijn levels -/
  mapping : Std.HashMap Nat Nat
  /-- Output context size (de Bruijn depth in the solution expression) -/
  cod : Nat
  /-- Input context size (next available fresh level for opening closures) -/
  dom : Nat
  /-- Meta being solved (for inline occurs check) -/
  targetMeta : MetaId

namespace PartialRenaming

/-- Create a partial renaming from spine levels -/
def fromSpine (spineLevels : List DeBruijnLvl) (m : MetaId) : PartialRenaming :=
  let n := spineLevels.length
  let maxLvl := spineLevels.foldl (fun acc l => max acc l.lvl) 0
  let mapping := Id.run do
    let mut map : Std.HashMap Nat Nat := {}
    let mut i := 0
    for l in spineLevels do
      map := map.insert l.lvl i
      i := i + 1
    return map
  { mapping, cod := n, dom := maxLvl + 1, targetMeta := m }

/-- Look up an input level and convert to an output de Bruijn index -/
def lookupIdx (ren : PartialRenaming) (lvl : Nat) : Option Nat :=
  match ren.mapping.get? lvl with
  | some outLvl => some (ren.cod - outLvl - 1)
  | none => none

/-- Extend the renaming when entering a binder -/
def lift (ren : PartialRenaming) : PartialRenaming :=
  { ren with
    mapping := ren.mapping.insert ren.dom ren.cod
    cod := ren.cod + 1
    dom := ren.dom + 1 }

/-- Extend the renaming by `n` newly-bound pattern variables -/
def liftN (ren : PartialRenaming) : Nat → PartialRenaming
  | 0 => ren
  | n + 1 => (ren.liftN n).lift

end PartialRenaming

/-- Why a rename failed -/
inductive RenameFailure where
  | occursCheck
  | escapeCheck
  deriving Inhabited, BEq

/-- Result of applying a partial renaming to a value -/
abbrev RenameResult := Except RenameFailure Soma.Core.Expr

private def freshPatternRenameArg (ren : PartialRenaming) (idx : Nat) : Value :=
  Value.vNeutral .type0 (.nVar ⟨s!"_case_arg_{idx}", ⟨ren.dom + idx⟩⟩)

private def freshPatternRenameArgs (ren : PartialRenaming) (patterns : Array Soma.Core.Pattern)
    : Array Value :=
  let arity := patterns.foldl (fun acc p => acc + p.bindingCount) 0
  Array.ofFn (n := arity) fun i => freshPatternRenameArg ren i.val

/-- Open an arm closure with one fresh value per pattern binding -/
private def applyArmClosureForRename (clos : Closure) (args : Array Value) : Value :=
  match clos with
  | .const _ value => value
  | .term _ env body =>
    let env' := args.foldl (fun acc arg => acc.extend "_" arg) env
    evalCoreExpr { EvalCtx.empty with env := env' } body

mutual

/-- Apply a partial renaming to a value, producing an Expr for the solution body -/
partial def rename (ren : PartialRenaming) (v : Value) : RenameResult :=
  match v with
  | .vType level => .ok (.sort level)

  | .vPi qty binder name dom cod => do
    let domE ← rename ren dom
    let argVal := Value.vNeutral dom (.nVar ⟨name, ⟨ren.dom⟩⟩)
    let codVal := Closure.applyPure cod argVal
    let codE ← rename ren.lift codVal
    .ok (.pi qty binder name domE codE)

  | .vLam name body => do
    let argVal := Value.vNeutral .type0 (.nVar ⟨name, ⟨ren.dom⟩⟩)
    let bodyVal := Closure.applyPure body argVal
    let bodyE ← rename ren.lift bodyVal
    .ok (.lam .explicit name (.sort Level.zero) bodyE)

  | .vNeutral _ neu => renameNeutral ren neu
  | .vIntLit n => .ok (.lit (.int n))
  | .vFloatLit f => .ok (.lit (.float f))
  | .vStringLit s => .ok (.lit (.string s))
  | .vRowEmpty => .ok .rowEmpty

  | .vRowExtend label ty tail => do
    let labelE ← rename ren label
    let tyE ← rename ren ty
    let tailE ← rename ren tail
    .ok (.rowExtend labelE tyE tailE)

  | .vRecord row => do
    let rowE ← rename ren row
    .ok (.recordTy rowE)

  | .vVariant row => do
    let rowE ← rename ren row
    .ok (.variantTy rowE)

  | .vLabelLit name => .ok (.labelLit name)
  | .vRowSort => .ok .rowSort
  | .vLabelSort => .ok .labelSort

  | .vRecordVal fields => do
    let fieldExprs ← fields.mapM fun (name, v) => do
      let e ← rename ren v
      pure (name, e)
    .ok (.record fieldExprs.toArray)

  | .vDataType id params => do
    let paramExprs ← params.mapM (rename ren)
    .ok (.dataTy id paramExprs.toArray)

  | .vConstructor name tag args rty => do
    let argExprs ← args.mapM (rename ren)
    let rtyE ← rename ren rty
    .ok (.construct name tag argExprs.toArray rtyE)


partial def renameHead (ren : PartialRenaming) : Head → RenameResult
  | .hVar v =>
    match ren.lookupIdx v.level.lvl with
    | some idx => .ok (.bvar idx)
    | none => .error .escapeCheck
  | .hMeta id =>
    if id == ren.targetMeta then .error .occursCheck
    else .ok (.mvar id)
  | .hConst name constTy => .ok (.const name (quoteExpr0 constTy))
  | .hErrored => .ok (.panic "{errored}")
  | .hCase scrutinees motive arms => do
    let scrutExprs ← scrutinees.mapM (rename ren)
    let motiveE ← rename ren motive
    let armExprs ← arms.mapM fun arm => do
      let args := freshPatternRenameArgs ren arm.patterns
      let bodyVal := applyArmClosureForRename arm.closure args
      let bodyE ← rename (ren.liftN args.size) bodyVal
      pure (Soma.Core.Arm.mk arm.patterns bodyE)
    .ok (.«case» scrutExprs motiveE armExprs.toArray)

partial def renameElim (ren : PartialRenaming) (acc : Soma.Core.Expr) : Elim → RenameResult
  | .eApp arg => do
    let argE ← rename ren arg
    .ok (.app acc argE)
  | .eField name => .ok (.fieldAccess acc name 0)

partial def renameNeutral (ren : PartialRenaming) (n : Neutral) : RenameResult := do
  let mut acc ← renameHead ren n.head
  for e in n.spine do
    acc ← renameElim ren acc e
  .ok acc

end

/-- Build nested lambdas from the spine -/
def buildLambdaSolution (binders : List (DeBruijnLvl × Soma.Core.Expr))
    (body : Soma.Core.Expr) : Soma.Core.Expr :=
  binders.foldr (fun (lvl, dom) acc =>
    Soma.Core.Expr.lam .explicit s!"x{lvl.lvl}" dom acc) body

/-- Evaluate a solution Expr to a Value -/
def evalSolutionTerm (t : Soma.Core.Expr) : TCM Value := do
  let ctx ← TCM.getCtx
  let state ← TCM.getState
  let evalCtx : EvalCtx := {
    env := ctx.env
    globals := ctx.globals.toGlobalEnvWithClasses ctx.instanceEnv
    metas := state.metas
  }
  return evalCoreExpr evalCtx t

/-- Build and install a meta solution from a partial renaming result -/
def installSolution (m : MetaId) (spineLevels : List DeBruijnLvl) (body : Soma.Core.Expr) : TCM Unit := do
  let ctx ← TCM.getCtx
  let binders : List (DeBruijnLvl × Soma.Core.Expr) := spineLevels.map fun lvl =>
    let domExpr : Soma.Core.Expr := match ctx.lookupLevel lvl with
      | some entry => Soma.Core.quoteExpr ⟨0⟩ entry.type
      | none => .sort Level.zero
    (lvl, domExpr)
  let solution := buildLambdaSolution binders body
  let solutionVal ← evalSolutionTerm solution
  TCM.solveMeta m solutionVal (callerTag := "Pattern.installSolution")

end Soma.Dependent
