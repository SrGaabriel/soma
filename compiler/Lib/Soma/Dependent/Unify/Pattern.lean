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

end PartialRenaming

/-- Why a rename failed -/
inductive RenameFailure where
  | occursCheck
  | escapeCheck
  deriving Inhabited, BEq

/-- Result of applying a partial renaming to a value -/
abbrev RenameResult := Except RenameFailure Soma.Core.Expr

mutual

/-- Apply a partial renaming to a value, producing an Expr for the solution body -/
partial def rename (ren : PartialRenaming) (v : Value) : RenameResult :=
  match v with
  | .vType level => .ok (.sort level)

  | .vPi qty binder name dom cod => do
    let domE ← rename ren dom
    let argVal := Value.vNeutral dom (.nVar ⟨name, ⟨ren.dom⟩⟩)
    let codVal := applyClosurePure cod argVal
    let codE ← rename ren.lift codVal
    .ok (.pi qty binder name domE codE)

  | .vLam name body => do
    let argVal := Value.vNeutral .type0 (.nVar ⟨name, ⟨ren.dom⟩⟩)
    let bodyVal := applyClosurePure body argVal
    let bodyE ← rename ren.lift bodyVal
    .ok (.lam .explicit name (.sort Level.zero) bodyE)

  | .vSigma qty name fst snd => do
    let fstE ← rename ren fst
    let argVal := Value.vNeutral fst (.nVar ⟨name, ⟨ren.dom⟩⟩)
    let sndVal := applyClosurePure snd argVal
    let sndE ← rename ren.lift sndVal
    .ok (.sigma qty .explicit name fstE sndE)

  | .vPair a b => do
    let aE ← rename ren a
    let bE ← rename ren b
    .ok (.pair aE bE)

  | .vNeutral _ neu => renameNeutral ren neu
  | .vPrimTy p => .ok (.primTy p)
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
    let baseExpr := Soma.Core.Expr.const ⟨⟨id.id, id.module, id.original⟩⟩ (.sort .zero)
    .ok (paramExprs.foldl (fun acc p => .app acc p) baseExpr)

  | .vConstructor name tag args rty => do
    let argExprs ← args.mapM (rename ren)
    let rtyE ← rename ren rty
    .ok (.construct name tag argExprs.toArray rtyE)

  | .vEq tyLevel ty lhs rhs => do
    let tyE ← rename ren ty
    let lhsE ← rename ren lhs
    let rhsE ← rename ren rhs
    .ok (.eqTy tyLevel tyE lhsE rhsE)

  | .vRefl ty x => do
    let tyE ← rename ren ty
    let xE ← rename ren x
    .ok (.refl tyE xE)

  | .vTransport tyLevel ty motive lhs rhs eq body => do
    let tyE ← rename ren ty
    let motiveE ← rename ren motive
    let lhsE ← rename ren lhs
    let rhsE ← rename ren rhs
    let eqE ← rename ren eq
    let bodyE ← rename ren body
    .ok (.transport tyLevel tyE motiveE lhsE rhsE eqE bodyE)

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
  | .hCase scrutinees arms rty => do
    let scrutExprs ← scrutinees.mapM (rename ren)
    let armExprs ← arms.mapM fun arm => do
      let argVal := Value.vNeutral .type0 (.nVar ⟨arm.pattern, ⟨ren.dom⟩⟩)
      let bodyVal := applyClosurePure arm.closure argVal
      let bodyE ← rename ren.lift bodyVal
      pure (Soma.Core.Arm.mk #[Soma.Core.Pattern.wildcard] bodyE)
    let rtyE ← rename ren rty
    .ok (.«case» scrutExprs armExprs.toArray rtyE)

partial def renameElim (ren : PartialRenaming) (acc : Soma.Core.Expr) : Elim → RenameResult
  | .eApp arg => do
    let argE ← rename ren arg
    .ok (.app acc argE)
  | .eFst => .ok (.projFst acc)
  | .eSnd => .ok (.projSnd acc)
  | .eField name => .ok (.fieldAccess acc name 0)

partial def renameNeutral (ren : PartialRenaming) (n : Neutral) : RenameResult := do
  let mut acc ← renameHead ren n.head
  for e in n.spine do
    acc ← renameElim ren acc e
  .ok acc

end

/-- Build nested lambdas from the spine -/
def buildLambdaSolution (spineLevels : List DeBruijnLvl) (body : Soma.Core.Expr) : Soma.Core.Expr :=
  spineLevels.foldr (fun lvl acc =>
    Soma.Core.Expr.lam .explicit s!"x{lvl.lvl}" (.sort Level.zero) acc) body

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
  let solution := buildLambdaSolution spineLevels body
  let solutionVal ← evalSolutionTerm solution
  TCM.solveMeta m solutionVal (callerTag := "Pattern.installSolution")

end Soma.Dependent
