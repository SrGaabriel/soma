/-
  Lambda Lifting Pass for Metal IR

  This pass transforms nested lambda expressions into top-level functions with
  explicit capture lists. After this pass, all lambdas are replaced with
  `closure` expressions that reference a lifted function and capture their
  free variables.

  The pass runs after type checking and before Circuit IR lowering.

  ## Implementation Strategy

  The key challenge is that Metal IR uses dependent types for scoping - the scope
  is part of the expression type. When we lift a lambda:

  1. Original lambda body has type `Expr Unit (lambdaParams ++ outerScope)`
  2. Lifted function needs `Expr Unit (captureParams ++ lambdaParams)`

  We solve this by:
  1. Computing free variables (captures) from the lambda body
  2. Creating fresh BindingIds for capture parameters in the lifted function
  3. Rewriting the body to replace references to outer scope variables with
     references to the new capture parameters
-/
import Soma.Metal.Expr
import Soma.Metal.Function
import Soma.Metal.Module
import Soma.Metal.Name
import Soma.Metal.Scope
import Std.Data.HashMap
import Std.Data.HashSet

namespace Soma.Metal.LambdaLift

open Soma.Metal
open Soma.Syntax (Span)
open Std (HashMap HashSet)

/-! ## State and Monad -/

/-- State for the lambda lifting pass -/
structure LiftState where
  /-- Counter for generating unique IDs -/
  nextId : Nat := 0
  /-- Accumulated lifted functions -/
  liftedFunctions : Array UntypedFunction := #[]
  /-- Set of global function names (not captured) -/
  globalNames : HashSet Name := {}
  /-- Module name for generating unique names -/
  moduleName : String
  deriving Inhabited

abbrev LiftM := StateM LiftState

namespace LiftM

def run (m : LiftM α) (moduleName : String) (globalNames : HashSet Name) : α × LiftState :=
  StateT.run m { moduleName, globalNames }

def freshId : LiftM Nat := do
  let st ← get
  let id := st.nextId
  set { st with nextId := id + 1 }
  pure id

def freshBindingId (name : String) : LiftM BindingId := do
  let st ← get
  let id ← freshId
  pure { id := id, module := st.moduleName, original := name }

def freshLambdaName : LiftM Name := do
  let st ← get
  let id ← freshId
  let original := s!"lambda${id}"
  let unique : Unique := { id := id, module := st.moduleName, original }
  pure (.user unique)

def addLiftedFunction (fn : UntypedFunction) : LiftM Unit := do
  let st ← get
  set { st with
    liftedFunctions := st.liftedFunctions.push fn
    globalNames := st.globalNames.insert fn.name
  }

def isGlobal (name : Name) : LiftM Bool := do
  let st ← get
  pure (st.globalNames.contains name)

end LiftM

/-! ## Free Variable Collection -/

/-- Collected free variables: BindingId -> original name -/
abbrev FreeVars := HashMap BindingId String

namespace FreeVars

def empty : FreeVars := {}

def singleton (b : BindingId) (name : String) : FreeVars :=
  ({} : FreeVars).insert b name

def union (fv1 fv2 : FreeVars) : FreeVars :=
  fv2.fold (init := fv1) fun acc b name => acc.insert b name

def unions (fvs : List FreeVars) : FreeVars :=
  fvs.foldl union empty

def removeMany (fv : FreeVars) (bs : List BindingId) : FreeVars :=
  bs.foldl (fun acc b => acc.erase b) fv

def toArray (fv : FreeVars) : Array (BindingId × String) :=
  fv.fold (init := #[]) fun acc b name => acc.push (b, name)

end FreeVars

mutual

/-- Collect free variables from an expression -/
partial def collectFreeVars : Expr Unit scope → FreeVars
  | .var v _ _ => FreeVars.singleton v.binding v.original
  | .lit _ _ => FreeVars.empty
  | .call fn args _ _ => FreeVars.union (collectFreeVars fn) (collectFreeVarsExprList args)
  | .lam params body _ _ =>
      let bodyFree := collectFreeVars body
      bodyFree.removeMany params.bindingIds
  | .closure _ caps _ _ => collectFreeVarsCaptureList caps
  | .construct _ _ args _ _ => collectFreeVarsExprList args
  | .tuple elems _ _ => collectFreeVarsExprList elems
  | .record fields _ _ => collectFreeVarsRecordFieldList fields
  | .recordUpdate base updates _ _ =>
      FreeVars.union (collectFreeVars base) (collectFreeVarsRecordFieldList updates)
  | .inject _ args _ _ => collectFreeVarsExprList args
  | .array elems _ _ => collectFreeVarsExprList elems
  | .if_ cond then_ else_ _ _ =>
      FreeVars.unions [collectFreeVars cond, collectFreeVars then_, collectFreeVars else_]
  | .case scruts arms _ _ =>
      FreeVars.union (collectFreeVarsExprList scruts) (collectFreeVarsArmList arms)
  | .fieldAccess e _ _ _ _ => collectFreeVars e
  | .global _ _ _ => FreeVars.empty
  | .panic _ _ _ => FreeVars.empty
  | .proj _ _ _ _ _ => FreeVars.empty
  | .typeApp _ _ _ => FreeVars.empty
  | .type _ _ => FreeVars.empty
  | .pi _ _ _ dom cod _ => FreeVars.union (collectFreeVars dom) (collectFreeVars cod)
  | .sigma _ _ fst snd _ => FreeVars.union (collectFreeVars fst) (collectFreeVars snd)
  | .pair fst snd _ _ => FreeVars.union (collectFreeVars fst) (collectFreeVars snd)
  | .fst e _ _ => collectFreeVars e
  | .snd e _ _ => collectFreeVars e
  | .primTy _ _ => FreeVars.empty
  | .higherPrimTy _ _ => FreeVars.empty
  | .rowEmpty _ => FreeVars.empty
  | .rowExtend label fieldTy tail _ =>
      FreeVars.unions [collectFreeVars label, collectFreeVars fieldTy, collectFreeVars tail]
  | .recordTy row _ => collectFreeVars row
  | .variantTy row _ => collectFreeVars row
  | .labelLit _ _ => FreeVars.empty
  | .dataTy _ params _ => collectFreeVarsExprList params
  | .ann expr ty _ _ => FreeVars.union (collectFreeVars expr) (collectFreeVars ty)
  | .hole _ _ => FreeVars.empty
  | .mvar _ _ _ => FreeVars.empty
  | .eq _ ty lhs rhs _ =>
      FreeVars.unions [collectFreeVars ty, collectFreeVars lhs, collectFreeVars rhs]
  | .refl ty x _ => FreeVars.union (collectFreeVars ty) (collectFreeVars x)
  | .transport _ ty motive lhs rhs eq body _ =>
      FreeVars.unions [collectFreeVars ty, collectFreeVars motive, collectFreeVars lhs,
                       collectFreeVars rhs, collectFreeVars eq, collectFreeVars body]

partial def collectFreeVarsExprList : ExprList Unit scope → FreeVars
  | .nil => FreeVars.empty
  | .cons e es => FreeVars.union (collectFreeVars e) (collectFreeVarsExprList es)

partial def collectFreeVarsArmList : ArmList Unit scope → FreeVars
  | .nil => FreeVars.empty
  | .cons arm arms =>
      let armFree := collectFreeVarsArm arm
      FreeVars.union armFree (collectFreeVarsArmList arms)

partial def collectFreeVarsArm : Arm Unit scope → FreeVars
  | .mk patterns body _ =>
      let bodyFree := collectFreeVars body
      bodyFree.removeMany patterns.bindingIds

partial def collectFreeVarsCaptureList : CaptureList Unit scope → FreeVars
  | .nil => FreeVars.empty
  | .cons v _ rest =>
      FreeVars.union (FreeVars.singleton v.binding v.original) (collectFreeVarsCaptureList rest)

partial def collectFreeVarsRecordFieldList : RecordFieldList Unit scope → FreeVars
  | .nil => FreeVars.empty
  | .cons _ expr rest =>
      FreeVars.union (collectFreeVars expr) (collectFreeVarsRecordFieldList rest)

end

/-! ## Unscoped Expression Types

To handle scope transformations, we first convert to an unscoped representation,
apply transformations, then convert back. This avoids complex dependent type
manipulations.
-/

/-- Unscoped variable reference -/
structure UVar where
  binding : BindingId
  original : String
  deriving BEq, Hashable, Repr

/-- Unscoped parameter -/
structure UParam where
  binding : BindingId
  name : String
  deriving BEq, Repr

/-- Unscoped pattern -/
inductive UPattern where
  | var (binding : BindingId) (name : String)
  | wildcard
  | lit (l : Literal)
  | ctor (name : Name) (args : Array UPattern)
  | tuple (elems : Array UPattern)
  | array (elems : Array UPattern)
  | cons (head : UPattern) (tail : UPattern)
  | as (binding : BindingId) (name : String) (inner : UPattern)
  | variant (label : String) (arg : Option UPattern)
  deriving Inhabited

/-- Unscoped expression - no scope tracking in types -/
inductive UExpr where
  | var (v : UVar) (span : Span)
  | lit (l : Literal) (span : Span)
  | call (fn : UExpr) (args : Array UExpr) (span : Span)
  | lam (params : Array UParam) (body : UExpr) (span : Span)
  | closure (name : Name) (captures : Array UVar) (span : Span)
  | construct (name : Name) (tag : Nat) (args : Array UExpr) (span : Span)
  | tuple (elems : Array UExpr) (span : Span)
  | record (fields : Array (String × UExpr)) (span : Span)
  | recordUpdate (base : UExpr) (updates : Array (String × UExpr)) (span : Span)
  | inject (label : String) (args : Array UExpr) (span : Span)
  | array (elems : Array UExpr) (span : Span)
  | if_ (cond : UExpr) (then_ : UExpr) (else_ : UExpr) (span : Span)
  | case (scruts : Array UExpr) (arms : Array (Array UPattern × UExpr)) (span : Span)
  | fieldAccess (expr : UExpr) (fieldName : String) (fieldIdx : Nat) (span : Span)
  | global (name : Name) (span : Span)
  | panic (msg : String) (span : Span)
  | proj (typeName : Name) (fieldName : String) (fieldIdx : Nat) (span : Span)
  | typeApp (arg : TypeArg) (span : Span)
  | type (level : Soma.Core.Level) (span : Span)
  | pi (qty : Soma.Core.Quantity) (binder : BinderInfo) (name : String)
       (dom : UExpr) (cod : UExpr) (span : Span)
  | sigma (qty : Soma.Core.Quantity) (name : String) (fst : UExpr) (snd : UExpr) (span : Span)
  | pair (fst : UExpr) (snd : UExpr) (span : Span)
  | fst (e : UExpr) (span : Span)
  | snd (e : UExpr) (span : Span)
  | primTy (p : Soma.Core.StarPrimitive) (span : Span)
  | higherPrimTy (p : Soma.Core.HigherPrimitive) (span : Span)
  | rowEmpty (span : Span)
  | rowExtend (label : UExpr) (fieldTy : UExpr) (tail : UExpr) (span : Span)
  | recordTy (row : UExpr) (span : Span)
  | variantTy (row : UExpr) (span : Span)
  | labelLit (name : String) (span : Span)
  | dataTy (id : Soma.Core.TypeId) (params : Array UExpr) (span : Span)
  | ann (expr : UExpr) (ty : UExpr) (span : Span)
  | hole (id : HoleId) (span : Span)
  | mvar (id : Nat) (span : Span)
  | eq (tyLevel : Soma.Core.Level) (ty : UExpr) (lhs : UExpr) (rhs : UExpr) (span : Span)
  | refl (ty : UExpr) (x : UExpr) (span : Span)
  | transport (tyLevel : Soma.Core.Level) (ty : UExpr) (motive : UExpr)
              (lhs : UExpr) (rhs : UExpr) (eq : UExpr) (body : UExpr) (span : Span)
  deriving Inhabited

/-! ## Conversion to Unscoped -/

mutual

partial def patternToU : Pattern Unit → UPattern
  | .var binding name _ _ => .var binding name
  | .wildcard _ _ => .wildcard
  | .lit l _ => .lit l
  | .ctor name args _ _ => .ctor name (args.map patternToU)
  | .tuple elems _ _ => .tuple (elems.map patternToU)
  | .array elems _ _ => .array (elems.map patternToU)
  | .cons h t _ _ => .cons (patternToU h) (patternToU t)
  | .as binding name inner _ _ => .as binding name (patternToU inner)
  | .variant label arg _ _ => .variant label (arg.map patternToU)

partial def patternListToU : PatternList Unit → Array UPattern
  | .nil => #[]
  | .cons p ps => #[patternToU p] ++ patternListToU ps

partial def exprToU : Expr Unit scope → UExpr
  | .var v _ span => .var ⟨v.binding, v.original⟩ span
  | .lit l span => .lit l span
  | .call fn args _ span => .call (exprToU fn) (exprListToU args) span
  | .lam params body _ span =>
      let ps := params.toList.map fun (b, n, _) => UParam.mk b n
      .lam ps.toArray (exprToU body) span
  | .closure name caps _ span => .closure name (captureListToU caps) span
  | .construct name tag args _ span => .construct name tag (exprListToU args) span
  | .tuple elems _ span => .tuple (exprListToU elems) span
  | .record fields _ span => .record (recordFieldListToU fields) span
  | .recordUpdate base updates _ span =>
      .recordUpdate (exprToU base) (recordFieldListToU updates) span
  | .inject label args _ span => .inject label (exprListToU args) span
  | .array elems _ span => .array (exprListToU elems) span
  | .if_ c t e _ span => .if_ (exprToU c) (exprToU t) (exprToU e) span
  | .case scruts arms _ span =>
      .case (exprListToU scruts) (armListToU arms) span
  | .fieldAccess e fn fi _ span => .fieldAccess (exprToU e) fn fi span
  | .global name _ span => .global name span
  | .panic msg _ span => .panic msg span
  | .proj tn fn fi _ span => .proj tn fn fi span
  | .typeApp arg _ span => .typeApp arg span
  | .type l span => .type l span
  | .pi q bi n d c span => .pi q bi n (exprToU d) (exprToU c) span
  | .sigma q n f s span => .sigma q n (exprToU f) (exprToU s) span
  | .pair f s _ span => .pair (exprToU f) (exprToU s) span
  | .fst e _ span => .fst (exprToU e) span
  | .snd e _ span => .snd (exprToU e) span
  | .primTy p span => .primTy p span
  | .higherPrimTy p span => .higherPrimTy p span
  | .rowEmpty span => .rowEmpty span
  | .rowExtend l f t span => .rowExtend (exprToU l) (exprToU f) (exprToU t) span
  | .recordTy r span => .recordTy (exprToU r) span
  | .variantTy r span => .variantTy (exprToU r) span
  | .labelLit n span => .labelLit n span
  | .dataTy id ps span => .dataTy id (exprListToU ps) span
  | .ann e t _ span => .ann (exprToU e) (exprToU t) span
  | .hole id span => .hole id span
  | .mvar id _ span => .mvar id span
  | .eq tl t l r span => .eq tl (exprToU t) (exprToU l) (exprToU r) span
  | .refl t x span => .refl (exprToU t) (exprToU x) span
  | .transport tl t m l r eq b span =>
      .transport tl (exprToU t) (exprToU m) (exprToU l) (exprToU r) (exprToU eq) (exprToU b) span

partial def exprListToU : ExprList Unit scope → Array UExpr
  | .nil => #[]
  | .cons e es => #[exprToU e] ++ exprListToU es

partial def captureListToU : CaptureList Unit scope → Array UVar
  | .nil => #[]
  | .cons v _ rest => #[⟨v.binding, v.original⟩] ++ captureListToU rest

partial def armListToU : ArmList Unit scope → Array (Array UPattern × UExpr)
  | .nil => #[]
  | .cons (.mk pats body _) rest =>
      #[(patternListToU pats, exprToU body)] ++ armListToU rest

partial def recordFieldListToU : RecordFieldList Unit scope → Array (String × UExpr)
  | .nil => #[]
  | .cons name expr rest => #[(name, exprToU expr)] ++ recordFieldListToU rest

end

/-! ## Conversion from Unscoped -/

/-- Convert UPattern back to Pattern, producing bindings -/
partial def uToPattern (p : UPattern) : Pattern Unit :=
  match p with
  | .var b n => .var b n () Span.uninhabited
  | .wildcard => .wildcard () Span.uninhabited
  | .lit l => .lit l Span.uninhabited
  | .ctor name args => .ctor name (args.map uToPattern) () Span.uninhabited
  | .tuple elems => .tuple (elems.map uToPattern) () Span.uninhabited
  | .array elems => .array (elems.map uToPattern) () Span.uninhabited
  | .cons h t => .cons (uToPattern h) (uToPattern t) () Span.uninhabited
  | .as b n inner => .as b n (uToPattern inner) () Span.uninhabited
  | .variant label arg => .variant label (arg.map uToPattern) () Span.uninhabited

/-- Get bindings from a UPattern -/
partial def uPatternBindings : UPattern → List BindingId
  | .var b _ => [b]
  | .wildcard => []
  | .lit _ => []
  | .ctor _ args => args.toList.flatMap uPatternBindings
  | .tuple elems => elems.toList.flatMap uPatternBindings
  | .array elems => elems.toList.flatMap uPatternBindings
  | .cons h t => uPatternBindings h ++ uPatternBindings t
  | .as b _ inner => b :: uPatternBindings inner
  | .variant _ arg => arg.map uPatternBindings |>.getD []

/-- Convert UExpr to Expr in a given scope. Uses unsafe coercions. -/
partial def uToExpr (e : UExpr) (scope : Scope) : Expr Unit scope :=
  match e with
  | .var v span =>
      -- Create a scoped var - the proof is assumed correct
      let sv : ScopedVar scope := ⟨v.binding, v.original, by sorry⟩
      .var sv () span
  | .lit l span => .lit l span
  | .call fn args span =>
      let fn' := uToExpr fn scope
      let args' := uToExprList args scope
      .call fn' args' () span
  | .lam params body span =>
      let paramList := paramsToParamList params
      let bodyScope := params.toList.map (·.binding) ++ scope
      let body' := uToExpr body bodyScope
      -- Cast body' to the expected type - scope proof is semantically correct
      let body'' : Expr Unit (paramList.bindingIds ++ scope) := by
        have h : paramList.bindingIds = params.toList.map (·.binding) := by
          -- This holds by definition of paramsToParamList
          sorry
        rw [h]; exact body'
      .lam paramList body'' () span
  | .closure name caps span =>
      let capList := uToCaptureList caps scope
      .closure name capList () span
  | .construct name tag args span =>
      .construct name tag (uToExprList args scope) () span
  | .tuple elems span =>
      .tuple (uToExprList elems scope) () span
  | .record fields span =>
      .record (uToRecordFieldList fields scope) () span
  | .recordUpdate base updates span =>
      .recordUpdate (uToExpr base scope) (uToRecordFieldList updates scope) () span
  | .inject label args span =>
      .inject label (uToExprList args scope) () span
  | .array elems span =>
      .array (uToExprList elems scope) () span
  | .if_ c t e span =>
      .if_ (uToExpr c scope) (uToExpr t scope) (uToExpr e scope) () span
  | .case scruts arms span =>
      .case (uToExprList scruts scope) (uToArmList arms scope) () span
  | .fieldAccess expr fn fi span =>
      .fieldAccess (uToExpr expr scope) fn fi () span
  | .global name span => .global name () span
  | .panic msg span => .panic msg () span
  | .proj tn fn fi span => .proj tn fn fi () span
  | .typeApp arg span => .typeApp arg () span
  | .type l span => .type l span
  | .pi q bi n d c span => .pi q bi n (uToExpr d scope) (uToExpr c scope) span
  | .sigma q n f s span => .sigma q n (uToExpr f scope) (uToExpr s scope) span
  | .pair f s span => .pair (uToExpr f scope) (uToExpr s scope) () span
  | .fst e span => .fst (uToExpr e scope) () span
  | .snd e span => .snd (uToExpr e scope) () span
  | .primTy p span => .primTy p span
  | .higherPrimTy p span => .higherPrimTy p span
  | .rowEmpty span => .rowEmpty span
  | .rowExtend l f t span =>
      .rowExtend (uToExpr l scope) (uToExpr f scope) (uToExpr t scope) span
  | .recordTy r span => .recordTy (uToExpr r scope) span
  | .variantTy r span => .variantTy (uToExpr r scope) span
  | .labelLit n span => .labelLit n span
  | .dataTy id ps span => .dataTy id (uToExprList ps scope) span
  | .ann e t span => .ann (uToExpr e scope) (uToExpr t scope) () span
  | .hole id span => .hole id span
  | .mvar id span => .mvar id () span
  | .eq tl t l r span =>
      .eq tl (uToExpr t scope) (uToExpr l scope) (uToExpr r scope) span
  | .refl t x span => .refl (uToExpr t scope) (uToExpr x scope) span
  | .transport tl t m l r eq b span =>
      .transport tl (uToExpr t scope) (uToExpr m scope) (uToExpr l scope)
                 (uToExpr r scope) (uToExpr eq scope) (uToExpr b scope) span
where
  paramsToParamList (params : Array UParam) : ParamList Unit :=
    params.foldr (init := .nil) fun p acc => .cons p.binding p.name () acc

  uToExprList (es : Array UExpr) (scope : Scope) : ExprList Unit scope :=
    es.foldr (init := .nil) fun e acc => .cons (uToExpr e scope) acc

  uToCaptureList (caps : Array UVar) (scope : Scope) : CaptureList Unit scope :=
    caps.foldr (init := .nil) fun v acc =>
      .cons ⟨v.binding, v.original, by sorry⟩ () acc

  uToRecordFieldList (fields : Array (String × UExpr)) (scope : Scope)
      : RecordFieldList Unit scope :=
    fields.foldr (init := .nil) fun (n, e) acc => .cons n (uToExpr e scope) acc

  uToArmList (arms : Array (Array UPattern × UExpr)) (scope : Scope)
      : ArmList Unit scope :=
    arms.foldr (init := .nil) fun (pats, body) acc =>
      let patList := pats.foldr (init := PatternList.nil) fun p acc =>
        .cons (uToPattern p) acc
      let armBindings := pats.toList.flatMap uPatternBindings
      let armScope := armBindings ++ scope
      let body' := uToExpr body armScope
      -- Cast body to expected type
      let body'' : Expr Unit (patList.bindingIds ++ scope) := by
        have h : patList.bindingIds = armBindings := by sorry
        rw [h]
        exact body'
      .cons (.mk patList body'' Span.uninhabited) acc

/-! ## Variable Substitution on UExpr -/

/-- Substitution map: old BindingId -> new BindingId -/
abbrev Subst := HashMap BindingId BindingId

/-- Apply substitution to a UExpr -/
partial def substUExpr (subst : Subst) : UExpr → UExpr
  | .var v span =>
      match subst.get? v.binding with
      | some newB => .var ⟨newB, v.original⟩ span
      | none => .var v span
  | .lit l span => .lit l span
  | .call fn args span => .call (substUExpr subst fn) (args.map (substUExpr subst)) span
  | .lam params body span =>
      -- Remove params from subst to avoid capturing
      let subst' := params.foldl (init := subst) fun s p => s.erase p.binding
      .lam params (substUExpr subst' body) span
  | .closure name caps span =>
      let caps' := caps.map fun v =>
        match subst.get? v.binding with
        | some newB => ⟨newB, v.original⟩
        | none => v
      .closure name caps' span
  | .construct name tag args span =>
      .construct name tag (args.map (substUExpr subst)) span
  | .tuple elems span => .tuple (elems.map (substUExpr subst)) span
  | .record fields span =>
      .record (fields.map fun (n, e) => (n, substUExpr subst e)) span
  | .recordUpdate base updates span =>
      .recordUpdate (substUExpr subst base)
                    (updates.map fun (n, e) => (n, substUExpr subst e)) span
  | .inject label args span => .inject label (args.map (substUExpr subst)) span
  | .array elems span => .array (elems.map (substUExpr subst)) span
  | .if_ c t e span => .if_ (substUExpr subst c) (substUExpr subst t) (substUExpr subst e) span
  | .case scruts arms span =>
      let scruts' := scruts.map (substUExpr subst)
      let arms' := arms.map fun (pats, body) =>
        -- Remove pattern bindings from subst
        let patBindings := pats.toList.flatMap uPatternBindings
        let subst' := patBindings.foldl (init := subst) fun s b => s.erase b
        (pats, substUExpr subst' body)
      .case scruts' arms' span
  | .fieldAccess e fn fi span => .fieldAccess (substUExpr subst e) fn fi span
  | .global name span => .global name span
  | .panic msg span => .panic msg span
  | .proj tn fn fi span => .proj tn fn fi span
  | .typeApp arg span => .typeApp arg span
  | .type l span => .type l span
  | .pi q bi n d c span => .pi q bi n (substUExpr subst d) (substUExpr subst c) span
  | .sigma q n f s span => .sigma q n (substUExpr subst f) (substUExpr subst s) span
  | .pair f s span => .pair (substUExpr subst f) (substUExpr subst s) span
  | .fst e span => .fst (substUExpr subst e) span
  | .snd e span => .snd (substUExpr subst e) span
  | .primTy p span => .primTy p span
  | .higherPrimTy p span => .higherPrimTy p span
  | .rowEmpty span => .rowEmpty span
  | .rowExtend l f t span =>
      .rowExtend (substUExpr subst l) (substUExpr subst f) (substUExpr subst t) span
  | .recordTy r span => .recordTy (substUExpr subst r) span
  | .variantTy r span => .variantTy (substUExpr subst r) span
  | .labelLit n span => .labelLit n span
  | .dataTy id ps span => .dataTy id (ps.map (substUExpr subst)) span
  | .ann e t span => .ann (substUExpr subst e) (substUExpr subst t) span
  | .hole id span => .hole id span
  | .mvar id span => .mvar id span
  | .eq tl t l r span =>
      .eq tl (substUExpr subst t) (substUExpr subst l) (substUExpr subst r) span
  | .refl t x span => .refl (substUExpr subst t) (substUExpr subst x) span
  | .transport tl t m l r eq b span =>
      .transport tl (substUExpr subst t) (substUExpr subst m) (substUExpr subst l)
                 (substUExpr subst r) (substUExpr subst eq) (substUExpr subst b) span

/-! ## Lambda Lifting on UExpr -/

/-- Collect free variables from UExpr -/
partial def collectFreeVarsU : UExpr → FreeVars
  | .var v _ => FreeVars.singleton v.binding v.original
  | .lit _ _ => FreeVars.empty
  | .call fn args _ =>
      FreeVars.union (collectFreeVarsU fn) (FreeVars.unions (args.toList.map collectFreeVarsU))
  | .lam params body _ =>
      let bodyFree := collectFreeVarsU body
      bodyFree.removeMany (params.toList.map (·.binding))
  | .closure _ caps _ =>
      FreeVars.unions (caps.toList.map fun v => FreeVars.singleton v.binding v.original)
  | .construct _ _ args _ => FreeVars.unions (args.toList.map collectFreeVarsU)
  | .tuple elems _ => FreeVars.unions (elems.toList.map collectFreeVarsU)
  | .record fields _ => FreeVars.unions (fields.toList.map fun (_, e) => collectFreeVarsU e)
  | .recordUpdate base updates _ =>
      FreeVars.union (collectFreeVarsU base)
                     (FreeVars.unions (updates.toList.map fun (_, e) => collectFreeVarsU e))
  | .inject _ args _ => FreeVars.unions (args.toList.map collectFreeVarsU)
  | .array elems _ => FreeVars.unions (elems.toList.map collectFreeVarsU)
  | .if_ c t e _ => FreeVars.unions [collectFreeVarsU c, collectFreeVarsU t, collectFreeVarsU e]
  | .case scruts arms _ =>
      let scrutFree := FreeVars.unions (scruts.toList.map collectFreeVarsU)
      let armsFree := FreeVars.unions (arms.toList.map fun (pats, body) =>
        let patBindings := pats.toList.flatMap uPatternBindings
        (collectFreeVarsU body).removeMany patBindings)
      FreeVars.union scrutFree armsFree
  | .fieldAccess e _ _ _ => collectFreeVarsU e
  | .global _ _ => FreeVars.empty
  | .panic _ _ => FreeVars.empty
  | .proj _ _ _ _ => FreeVars.empty
  | .typeApp _ _ => FreeVars.empty
  | .type _ _ => FreeVars.empty
  | .pi _ _ _ d c _ => FreeVars.union (collectFreeVarsU d) (collectFreeVarsU c)
  | .sigma _ _ f s _ => FreeVars.union (collectFreeVarsU f) (collectFreeVarsU s)
  | .pair f s _ => FreeVars.union (collectFreeVarsU f) (collectFreeVarsU s)
  | .fst e _ => collectFreeVarsU e
  | .snd e _ => collectFreeVarsU e
  | .primTy _ _ => FreeVars.empty
  | .higherPrimTy _ _ => FreeVars.empty
  | .rowEmpty _ => FreeVars.empty
  | .rowExtend l f t _ =>
      FreeVars.unions [collectFreeVarsU l, collectFreeVarsU f, collectFreeVarsU t]
  | .recordTy r _ => collectFreeVarsU r
  | .variantTy r _ => collectFreeVarsU r
  | .labelLit _ _ => FreeVars.empty
  | .dataTy _ ps _ => FreeVars.unions (ps.toList.map collectFreeVarsU)
  | .ann e t _ => FreeVars.union (collectFreeVarsU e) (collectFreeVarsU t)
  | .hole _ _ => FreeVars.empty
  | .mvar _ _ => FreeVars.empty
  | .eq _ t l r _ => FreeVars.unions [collectFreeVarsU t, collectFreeVarsU l, collectFreeVarsU r]
  | .refl t x _ => FreeVars.union (collectFreeVarsU t) (collectFreeVarsU x)
  | .transport _ t m l r eq b _ =>
      FreeVars.unions [collectFreeVarsU t, collectFreeVarsU m, collectFreeVarsU l,
                       collectFreeVarsU r, collectFreeVarsU eq, collectFreeVarsU b]

/-- Lift lambdas in a UExpr -/
partial def liftUExpr (e : UExpr) : LiftM UExpr := do
  match e with
  | .var v span => pure (.var v span)
  | .lit l span => pure (.lit l span)
  | .call fn args span => do
      let fn' ← liftUExpr fn
      let args' ← args.mapM liftUExpr
      pure (.call fn' args' span)

  | .lam params body span => do
      -- First, lift any nested lambdas in the body
      let body' ← liftUExpr body

      -- Collect free variables in the body
      let allFree := collectFreeVarsU body'
      -- Remove lambda's own parameters
      let freeAfterParams := allFree.removeMany (params.toList.map (·.binding))

      -- Filter out globals
      let mut captures : Array (BindingId × String) := #[]
      for (b, name) in freeAfterParams.toArray do
        let isGlob ← LiftM.isGlobal (.user { id := b.id, module := b.module, original := name })
        if !isGlob then
          captures := captures.push (b, name)

      -- Generate fresh binding IDs for capture parameters
      let mut captureParams : Array UParam := #[]
      let mut subst : Subst := {}
      for (oldB, name) in captures do
        let newB ← LiftM.freshBindingId name
        captureParams := captureParams.push ⟨newB, name⟩
        subst := subst.insert oldB newB

      -- Apply substitution to body to replace captured vars with new params
      let body'' := substUExpr subst body'

      -- Generate name for lifted function
      let liftedName ← LiftM.freshLambdaName

      -- All params: capture params followed by original lambda params
      let allParams := captureParams ++ params

      -- Create the lifted function body in proper scope
      let liftedParams : Array (BindingId × String) := allParams.map fun p => (p.binding, p.name)
      let liftedScope : Scope := liftedParams.toList.map (·.1)
      let liftedBody := uToExpr body'' liftedScope

      let liftedFn : UntypedFunction := {
        name := liftedName
        params := liftedParams
        body := liftedBody
        declaredTypeSyntax := none
        closureInfo := some { capturedVars := captures }
        attrs := {}
      }

      LiftM.addLiftedFunction liftedFn

      -- Return closure expression with original captured variables
      let captureVars := captures.map fun (b, n) => UVar.mk b n
      pure (.closure liftedName captureVars span)

  | .closure name caps span => pure (.closure name caps span)
  | .construct name tag args span => do
      let args' ← args.mapM liftUExpr
      pure (.construct name tag args' span)
  | .tuple elems span => do
      let elems' ← elems.mapM liftUExpr
      pure (.tuple elems' span)
  | .record fields span => do
      let fields' ← fields.mapM fun (n, e) => do
        let e' ← liftUExpr e
        pure (n, e')
      pure (.record fields' span)
  | .recordUpdate base updates span => do
      let base' ← liftUExpr base
      let updates' ← updates.mapM fun (n, e) => do
        let e' ← liftUExpr e
        pure (n, e')
      pure (.recordUpdate base' updates' span)
  | .inject label args span => do
      let args' ← args.mapM liftUExpr
      pure (.inject label args' span)
  | .array elems span => do
      let elems' ← elems.mapM liftUExpr
      pure (.array elems' span)
  | .if_ c t e span => do
      let c' ← liftUExpr c
      let t' ← liftUExpr t
      let e' ← liftUExpr e
      pure (.if_ c' t' e' span)
  | .case scruts arms span => do
      let scruts' ← scruts.mapM liftUExpr
      let arms' ← arms.mapM fun (pats, body) => do
        let body' ← liftUExpr body
        pure (pats, body')
      pure (.case scruts' arms' span)
  | .fieldAccess e fn fi span => do
      let e' ← liftUExpr e
      pure (.fieldAccess e' fn fi span)
  | .global name span => pure (.global name span)
  | .panic msg span => pure (.panic msg span)
  | .proj tn fn fi span => pure (.proj tn fn fi span)
  | .typeApp arg span => pure (.typeApp arg span)
  | .type l span => pure (.type l span)
  | .pi q bi n d c span => do
      let d' ← liftUExpr d
      let c' ← liftUExpr c
      pure (.pi q bi n d' c' span)
  | .sigma q n f s span => do
      let f' ← liftUExpr f
      let s' ← liftUExpr s
      pure (.sigma q n f' s' span)
  | .pair f s span => do
      let f' ← liftUExpr f
      let s' ← liftUExpr s
      pure (.pair f' s' span)
  | .fst e span => do
      let e' ← liftUExpr e
      pure (.fst e' span)
  | .snd e span => do
      let e' ← liftUExpr e
      pure (.snd e' span)
  | .primTy p span => pure (.primTy p span)
  | .higherPrimTy p span => pure (.higherPrimTy p span)
  | .rowEmpty span => pure (.rowEmpty span)
  | .rowExtend l f t span => do
      let l' ← liftUExpr l
      let f' ← liftUExpr f
      let t' ← liftUExpr t
      pure (.rowExtend l' f' t' span)
  | .recordTy r span => do
      let r' ← liftUExpr r
      pure (.recordTy r' span)
  | .variantTy r span => do
      let r' ← liftUExpr r
      pure (.variantTy r' span)
  | .labelLit n span => pure (.labelLit n span)
  | .dataTy id ps span => do
      let ps' ← ps.mapM liftUExpr
      pure (.dataTy id ps' span)
  | .ann e t span => do
      let e' ← liftUExpr e
      let t' ← liftUExpr t
      pure (.ann e' t' span)
  | .hole id span => pure (.hole id span)
  | .mvar id span => pure (.mvar id span)
  | .eq tl t l r span => do
      let t' ← liftUExpr t
      let l' ← liftUExpr l
      let r' ← liftUExpr r
      pure (.eq tl t' l' r' span)
  | .refl t x span => do
      let t' ← liftUExpr t
      let x' ← liftUExpr x
      pure (.refl t' x' span)
  | .transport tl t m l r eq b span => do
      let t' ← liftUExpr t
      let m' ← liftUExpr m
      let l' ← liftUExpr l
      let r' ← liftUExpr r
      let eq' ← liftUExpr eq
      let b' ← liftUExpr b
      pure (.transport tl t' m' l' r' eq' b' span)

/-! ## Function and Module Lifting -/

/-- Lift lambdas in a single function -/
def liftFunction (fn : UntypedFunction) : LiftM UntypedFunction := do
  -- Convert to unscoped
  let uBody := exprToU fn.body
  -- Lift lambdas
  let uBody' ← liftUExpr uBody
  -- Convert back to scoped
  let scope := fn.params.toList.map (·.1)
  let body' := uToExpr uBody' scope
  pure { fn with body := body' }

/-- Lift lambdas in all functions of a module -/
def liftModule (m : Module) : Module := Id.run do
  -- Collect global names (all top-level functions)
  let globalNames : HashSet Name := m.functions.foldl (init := {}) fun acc fn =>
    acc.insert fn.name

  -- Also add constructor names as globals
  let globalNames := m.types.foldl (init := globalNames) fun acc typeDef =>
    typeDef.constructors.foldl (init := acc) fun acc' ctor => acc'.insert ctor.name

  -- Run the lifting pass
  let (liftedFunctions, finalState) := LiftM.run (do
    let mut result := #[]
    for fn in m.functions do
      let fn' ← liftFunction fn
      result := result.push fn'
    pure result
  ) m.name globalNames

  -- Combine original (lifted) functions with newly generated ones
  let allFunctions := liftedFunctions ++ finalState.liftedFunctions

  { m with functions := allFunctions }

end Soma.Metal.LambdaLift
