import Soma.Metal.Lower.Monad
import Soma.Metal.Lower.Type
import Soma.Metal.Expr
import Soma.Metal.Pattern
import Soma.Syntax.Ast

namespace Soma.Metal.Lower

open Soma.Typing
open Soma.Metal
open Soma.Syntax (Span Literal MatchArm)

-- Inhabited instances needed for partial definitions
instance : Inhabited (ParamList α) := ⟨.nil⟩
instance : Inhabited (PatternList α) := ⟨.nil⟩
instance : Inhabited (ExprList α scope) := ⟨.nil⟩
instance : Inhabited (ArmList α scope) := ⟨.nil⟩

instance [Inhabited α] : Inhabited (Expr α scope) :=
  ⟨.panic "uninhabited" default default⟩
instance [Inhabited α] : Inhabited (Arm α scope) :=
  ⟨.mk .nil (.panic "uninhabited" default default) default⟩

/-- Lower a Syntax.Literal to Metal.Literal -/
def lowerLiteral : Soma.Syntax.Literal → Metal.Literal
  | .int n _ => .int n
  | .string s _ => .string s
  | .bool b _ => .bool b

/-- Lower a pattern, generating fresh binding IDs -/
partial def lowerPattern (pat : Soma.Syntax.Pattern) : LowerM (Pattern Unit) := do
  match pat with
  | .var name =>
    let bindingId ← LowerM.freshPatternVarId name.value
    pure (.var bindingId name.value () name.span)

  | .wildcard span =>
    pure (.wildcard () span)

  | .lit lit =>
    pure (.lit (lowerLiteral lit) lit.span)

  | .con name args span =>
    let ctorInfo? ← LowerM.lookupConstructor name.value
    -- Always lower args so their bindings are captured (even if constructor is unknown)
    let args' ← args.mapM lowerPattern
    match ctorInfo? with
    | some info =>
      pure (.ctor info.name args' () span)
    | none =>
      LowerM.reportError (.unknownConstructor name.value span)
      -- Create a fake constructor pattern to preserve the arg bindings
      let fakeUnique ← LowerM.freshUnique "_unknown"
      let fakeName := Name.ctor fakeUnique name.value 0
      pure (.ctor fakeName args' () span)

  | .tuple elems span =>
    let elems' ← elems.mapM lowerPattern
    pure (.tuple elems' () span)

  | .list elems span =>
    let elems' ← elems.mapM lowerPattern
    pure (.array elems' () span)

  | .cons head tail span =>
    let head' ← lowerPattern head
    let tail' ← lowerPattern tail
    pure (.cons head' tail' () span)

  | .parens inner _ =>
    lowerPattern inner

  | .typed pat _ _ =>
    lowerPattern pat

/-- Build a ParamList from a list of (BindingId, name) pairs -/
def buildParamList : List (BindingId × String) → ParamList Unit
  | [] => .nil
  | (b, n) :: rest => .cons b n () (buildParamList rest)

/-- Theorem: buildParamList preserves binding IDs -/
theorem buildParamList_bindingIds (bindings : List (BindingId × String)) :
    (buildParamList bindings).bindingIds = bindings.map Prod.fst := by
  induction bindings with
  | nil => rfl
  | cons hd tl ih => simp only [buildParamList, ParamList.bindingIds, List.map, ih]

/-- Extend environment for a ParamList -/
def extendEnvWithParams {scope : Scope} (env : LocalEnv scope) (params : ParamList Unit)
    : LocalEnv (params.bindingIds ++ scope) :=
  match params with
  | .nil => env
  | .cons b name _ rest =>
    let env' := extendEnvWithParams env rest
    env'.extend b name

/-- Theorem: Pattern.bindingsWithNames.map fst = Pattern.bindings

    This theorem states that extracting just the BindingIds from bindingsWithNames
    gives the same result as calling bindings directly.
-/
theorem pattern_bindingsWithNames_fst (pat : Pattern α) :
    (pat.bindingsWithNames.toList.map Prod.fst) = pat.bindings.toList :=
  Pattern.bindingsWithNames_fst pat

/-- Extend environment with a list of (BindingId, name) pairs -/
def extendEnvWithBindingPairs {scope : Scope} (env : LocalEnv scope)
    : (bindings : List (BindingId × String)) → LocalEnv (bindings.map Prod.fst ++ scope)
  | [] => env
  | (b, name) :: rest =>
    let env' := extendEnvWithBindingPairs env rest
    env'.extend b name

/-- Extend environment with a single pattern's bindings -/
def extendEnvWithSinglePatternAux {scope : Scope} (env : LocalEnv scope) (pat : Pattern Unit)
    : LocalEnv (pat.bindingsWithNames.toList.map Prod.fst ++ scope) :=
  extendEnvWithBindingPairs env pat.bindingsWithNames.toList

/-- Cast LocalEnv using scope equality -/
def castLocalEnv (h : s1 = s2) (env : LocalEnv s1) : LocalEnv s2 := h ▸ env

/-- Extend environment with a single pattern, producing the correct scope type -/
def extendEnvWithSinglePattern {scope : Scope} (env : LocalEnv scope) (pat : Pattern Unit)
    : LocalEnv (pat.bindings.toList ++ scope) :=
  let env' := extendEnvWithSinglePatternAux env pat
  castLocalEnv (by rw [pattern_bindingsWithNames_fst]) env'

/-- Extend environment with a PatternList's bindings -/
def extendEnvWithPatternList {scope : Scope} (env : LocalEnv scope) (pats : PatternList Unit)
    : LocalEnv (pats.bindingIds ++ scope) :=
  match pats with
  | .nil => env
  | .cons pat rest =>
    -- First extend with rest to get LocalEnv (rest.bindingIds ++ scope)
    let env' := extendEnvWithPatternList env rest
    -- Then extend with pat's bindings to get LocalEnv (pat.bindings.toList ++ rest.bindingIds ++ scope)
    let env'' := extendEnvWithSinglePattern env' pat
    -- Cast using associativity
    castLocalEnv (by simp only [PatternList.bindingIds]; rw [List.append_assoc]) env''

mutual
  /-- Lower a Syntax.Expr to Metal.Expr -/
  partial def lowerExpr (localEnv : LocalEnv scope) (expr : Soma.Syntax.Expr)
      : LowerM (Expr Unit scope) := do
    match expr with
    | .var name =>
      let result? ← LowerM.lookupVar localEnv name.value
      match result? with
      | some (.inl scopedVar) =>
        pure (.var scopedVar () name.span)
      | some (.inr globalInfo) =>
        pure (.global globalInfo.name () name.span)
      | none =>
        LowerM.reportError (.unboundVariable name.value name.span)
        pure (.panic s!"unresolved: {name.value}" () name.span)

    | .lit lit =>
      pure (.lit (lowerLiteral lit) lit.span)

    | .app fn arg span =>
      let fn' ← lowerExpr localEnv fn
      let arg' ← lowerExpr localEnv arg
      pure (.call fn' (.cons arg' .nil) () span)

    | .infix op left right span =>
      let result? ← LowerM.lookupVar localEnv op.value
      match result? with
      | some (.inl scopedVar) =>
        let left' ← lowerExpr localEnv left
        let right' ← lowerExpr localEnv right
        let opExpr : Expr Unit scope := .var scopedVar () op.span
        pure (.call opExpr (.cons left' (.cons right' .nil)) () span)
      | some (.inr globalInfo) =>
        let left' ← lowerExpr localEnv left
        let right' ← lowerExpr localEnv right
        let opExpr : Expr Unit scope := .global globalInfo.name () op.span
        pure (.call opExpr (.cons left' (.cons right' .nil)) () span)
      | none =>
        LowerM.reportError (.unboundVariable op.value op.span)
        pure (.panic s!"unresolved operator: {op.value}" () span)

    | .lambda params body span =>
      lowerLambda localEnv params.toList body span

    | .let_ name _ value body span =>
      let value' ← lowerExpr localEnv value
      let bindingId ← LowerM.freshPatternVarId name.value
      let localEnv' := localEnv.extend bindingId name.value
      let body' ← lowerExpr localEnv' body
      pure (.let_ bindingId name.value value' body' () span)

    | .if_ cond then_ else_ span =>
      let cond' ← lowerExpr localEnv cond
      let then' ← lowerExpr localEnv then_
      let else' ← lowerExpr localEnv else_
      pure (.if_ cond' then' else' () span)

    | .case scrutinees arms span =>
      let scrutineeList ← scrutinees.toList.mapM (lowerExpr localEnv)
      let scrutinees' := ExprList.fromList scrutineeList
      let armList ← arms.toList.mapM (lowerArm localEnv)
      let arms' := ArmList.fromList armList
      pure (.case scrutinees' arms' () span)

    | .tuple elems span =>
      let elemList ← elems.toList.mapM (lowerExpr localEnv)
      let elems' := ExprList.fromList elemList
      pure (.tuple elems' () span)

    | .list elems span =>
      let elemList ← elems.toList.mapM (lowerExpr localEnv)
      let elems' := ExprList.fromList elemList
      pure (.array elems' () span)

    | .record _fields span =>
      pure (.tuple .nil () span)

    | .fieldAccess expr _field span =>
      let expr' ← lowerExpr localEnv expr
      pure (.fieldAccess expr' 0 () span)

    | .parens inner _ =>
      lowerExpr localEnv inner

    | .typeAnnot expr _ _ =>
      lowerExpr localEnv expr

    | .compose body _ =>
      lowerExpr localEnv body

    | .bind body _ =>
      lowerExpr localEnv body

  /-- Lower a lambda expression -/
  partial def lowerLambda (localEnv : LocalEnv scope)
      (params : List (Soma.Syntax.Name × Option Soma.Syntax.TypeExpr))
      (body : Soma.Syntax.Expr) (span : Span) : LowerM (Expr Unit scope) := do
    -- Generate binding IDs for all params
    let paramBindingPairs ← params.mapM fun (name, _) => do
      let id ← LowerM.freshParamId name.value
      pure (id, name.value)

    -- Build the ParamList
    let paramList := buildParamList paramBindingPairs

    -- Extend environment with params in the correct order
    let localEnv' := extendEnvWithParams localEnv paramList

    -- Lower body in extended environment
    let body' ← lowerExpr localEnv' body

    pure (.lam paramList body' () span)

  /-- Lower a match arm -/
  partial def lowerArm (localEnv : LocalEnv scope) (arm : MatchArm)
      : LowerM (Arm Unit scope) := do
    let patterns ← arm.patterns.toList.mapM lowerPattern
    let patternList := PatternList.fromList patterns

    -- Extend environment with pattern bindings
    let localEnv' := extendEnvWithPatternList localEnv patternList

    -- Lower body
    let body' ← lowerExpr localEnv' arm.body

    pure (.mk patternList body' arm.span)
end

end Soma.Metal.Lower
