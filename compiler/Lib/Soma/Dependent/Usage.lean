import Soma.Core.Quantity
import Soma.Core.Value
import Soma.Dependent.Monad
import Soma.Dependent.Error
import Soma.Syntax.Source

namespace Soma.Dependent

open Soma (Unique)
open Soma.Core
open Soma.Syntax (Span)

/-- A snapshot of variable usage counts at a point in the program -/
structure UsageSnapshot where
  usages : Std.HashMap Unique Nat
  deriving Inhabited

namespace UsageSnapshot

def empty : UsageSnapshot := ⟨{}⟩

def get (snap : UsageSnapshot) (bindingId : Unique) : Nat :=
  snap.usages.getD bindingId 0

def set (snap : UsageSnapshot) (bindingId : Unique) (count : Nat) : UsageSnapshot :=
  ⟨snap.usages.insert bindingId count⟩

/-- Merge two usage snapshots by adding counts -/
def merge (s1 s2 : UsageSnapshot) : UsageSnapshot :=
  let merged := s1.usages.fold (init := s2.usages) fun acc bindingId count1 =>
    let count2 := acc.getD bindingId 0
    acc.insert bindingId (count1 + count2)
  ⟨merged⟩

/-- Take the maximum of two usage snapshots (for branching) -/
def join (s1 s2 : UsageSnapshot) : UsageSnapshot :=
  let joined := s1.usages.fold (init := s2.usages) fun acc bindingId count1 =>
    let count2 := acc.getD bindingId 0
    -- For branches, we take the max usage count
    acc.insert bindingId (max count1 count2)
  ⟨joined⟩

end UsageSnapshot

/-- Check that actual usage is compatible with declared quantity -/
def usageCompatible (declared actual : Quantity) : Bool :=
  actual.le declared

/-- Check all variables in scope for correct usage.
    This should be called at the end of checking a function body. -/
def checkAllUsages : TCM Unit := do
  let ctx ← TCM.getCtx
  for entry in ctx.locals do
    let count ← TCM.getUsage entry.bindingId
    let actual := TCM.countToQuantity count
    -- Check that actual usage is compatible with declared quantity
    if !usageCompatible entry.qty actual then
      -- Special case for linear variables
      if entry.qty == .one then
        if count == 0 then
          TCM.addError (.linearNotUsed entry.name entry.span)
        else
          TCM.addError (.quantityMismatch entry.qty actual entry.name entry.span)
      else
        TCM.addError (.quantityMismatch entry.qty actual entry.name entry.span)

/-- Check that a linear variable is used exactly once.
    This is a stricter check than checkAllUsages for linear bindings. -/
def checkLinearBinding (bindingId : Unique) (declSpan : Span) : TCM Unit := do
  let count ← TCM.getUsage bindingId
  if count == 0 then
    TCM.addError (.linearNotUsed bindingId.original declSpan)
  else if count != 1 then
    let actual := TCM.countToQuantity count
    TCM.addError (.quantityMismatch .one actual bindingId.original declSpan)

/-- Check that an erased variable is not used at runtime.
    This should be called when we detect a use of a variable. -/
def checkNotErased (bindingId : Unique) (useSpan : Span) : TCM Unit := do
  let ctx ← TCM.getCtx
  match ctx.lookupLocal bindingId.original with
  | some entry =>
    if entry.qty == .zero && !ctx.inErased then
      -- Using an erased variable in non-erased context
      TCM.throw (.erasedUsedAtRuntime bindingId.original useSpan none)
  | none => pure ()

/-- Record usage of a variable with proper erased context checking -/
def useVarChecked (bindingId : Unique) (span : Span) (count : Nat := 1) : TCM Unit := do
  -- First check if we're trying to use an erased variable
  checkNotErased bindingId span
  -- Then record the usage
  TCM.useVar bindingId count

/-! ## Branch Usage Tracking -/

/-- Run an action and capture its usage, returning both the result and usages -/
def captureUsages (action : TCM α) : TCM (α × UsageSnapshot) := do
  let state ← TCM.getState
  let savedUsages := state.saveUsages
  TCM.modifyState (·.clearUsages)
  let result ← action
  let state' ← TCM.getState
  let newUsages : UsageSnapshot := ⟨state'.usages⟩
  TCM.modifyState (·.restoreUsages savedUsages)
  return (result, newUsages)

/-- Apply a usage snapshot to the current state -/
def applyUsages (snap : UsageSnapshot) : TCM Unit := do
  for (bindingId, count) in snap.usages.toList do
    TCM.modifyState (·.useVar bindingId count)

/-- Check two branches have compatible usage (for if/case).
    For linear variables, both branches must use them. -/
def checkBranchUsages (branch1 branch2 : UsageSnapshot) (span : Span) : TCM UsageSnapshot := do
  let ctx ← TCM.getCtx
  -- Check linear variables are used in both branches
  for entry in ctx.locals do
    if entry.qty == .one then
      let use1 := branch1.get entry.bindingId
      let use2 := branch2.get entry.bindingId
      -- Both branches must use the linear variable, or neither
      if (use1 == 0) != (use2 == 0) then
        let combined := TCM.countToQuantity (use1 + use2)
        TCM.addError (.quantityMismatch .one combined entry.name span)
  -- Return the joined usage (max of both branches)
  return branch1.join branch2

/-- Run an action with usage checking for a binder.
    After the action, checks that the bound variable was used correctly. -/
def withCheckedBinding (name : String) (bindingId : Unique) (ty : Value)
    (qty : Quantity) (binder : BinderInfo) (span : Span) (action : TCM α) : TCM α := do
  -- Run the action under the binding
  let result ← TCM.withBinding name bindingId ty qty binder span action
  -- Check usage of the bound variable
  if qty == .one then
    checkLinearBinding bindingId span
  return result

/-- Run an action in erased context (quantity 0).
    All usages in this context don't count toward runtime usage. -/
def inErasedScope (action : TCM α) : TCM α :=
  TCM.inErasedContext action

/-- Record that pattern bindings are introduced (TODO: review) -/
def introducePatternBindings (bindings : List (Unique × Quantity × Span)) : TCM Unit := do
  -- Pattern bindings start with zero usage
  for (_, _, _) in bindings do
    -- Initialize usage to zero (already the default)
    pure ()

/-- Check pattern bindings were used correctly after checking a body -/
def checkPatternBindings (bindings : List (Unique × Quantity × Span)) : TCM Unit := do
  for (bindingId, qty, span) in bindings do
    if qty == .one then
      checkLinearBinding bindingId span

/-- Check a complete function body for correct usage -/
def checkFunctionUsage (params : List (Unique × Quantity × Span)) : TCM Unit := do
  for (bindingId, qty, span) in params do
    let count ← TCM.getUsage bindingId
    if qty == .one then
      if count == 0 then
        TCM.addError (.linearNotUsed bindingId.original span)
      else if count != 1 then
        let actual := TCM.countToQuantity count
        TCM.addError (.quantityMismatch .one actual bindingId.original span)
    else if qty == .zero then
      -- Erased parameters shouldn't have any runtime usage
      -- (but this is already enforced by checkNotErased)
      pure ()
    -- For omega, any usage is fine

/-- Wrapper that runs an action and then checks function usage -/
def withFunctionUsageCheck (params : List (Unique × Quantity × Span))
    (action : TCM α) : TCM α := do
  let result ← action
  checkFunctionUsage params
  return result

end Soma.Dependent
