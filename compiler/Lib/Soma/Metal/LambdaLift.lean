/-
  Lambda Lifting Pass for Metal IR

  This pass transforms nested lambda expressions into top-level functions with
  explicit capture lists. After this pass, all lambdas are replaced with
  `closure` expressions that reference a lifted function and capture their
  free variables.
-/
import Soma.Metal.Expr
import Soma.Metal.Function
import Soma.Metal.Module
import Soma.Metal.Name
import Soma.Metal.Scope
import Soma.Core.Value
import Std.Data.HashMap
import Std.Data.HashSet

namespace Soma.Metal.LambdaLift

open Soma.Metal
open Soma.Syntax (Span)
open Soma.Core (Value)
open Std (HashMap HashSet)

/-! ## State and Monad -/

/-- State for the lambda lifting pass -/
structure LiftState where
  /-- Counter for generating unique IDs -/
  nextId : Nat := 0
  /-- Accumulated lifted functions -/
  liftedFunctions : Array TypedFunction := #[]
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

def addLiftedFunction (fn : TypedFunction) : LiftM Unit := do
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

/-- Collected free variables: BindingId -> (original name, type) -/
abbrev FreeVars := HashMap BindingId (String × Value)

namespace FreeVars

def empty : FreeVars := {}

def singleton (b : BindingId) (name : String) (ty : Value) : FreeVars :=
  ({} : FreeVars).insert b (name, ty)

def union (fv1 fv2 : FreeVars) : FreeVars :=
  fv2.fold (init := fv1) fun acc b info => acc.insert b info

def unions (fvs : List FreeVars) : FreeVars :=
  fvs.foldl union empty

def removeMany (fv : FreeVars) (bs : List BindingId) : FreeVars :=
  bs.foldl (fun acc b => acc.erase b) fv

def toArray (fv : FreeVars) : Array (BindingId × String × Value) :=
  fv.fold (init := #[]) fun acc b (name, ty) => acc.push (b, name, ty)

end FreeVars

/-- Get type from a typed expression -/
def exprType (e : Expr Value scope) : Value :=
  e.getInfo.getD (Value.vType Soma.Core.Level.zero)

mutual

/-- Collect free variables from a typed expression -/
partial def collectFreeVars : Expr Value scope → FreeVars
  | .var v info _ => FreeVars.singleton v.binding v.original (info)
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

partial def collectFreeVarsExprList : ExprList Value scope → FreeVars
  | .nil => FreeVars.empty
  | .cons e es => FreeVars.union (collectFreeVars e) (collectFreeVarsExprList es)

partial def collectFreeVarsArmList : ArmList Value scope → FreeVars
  | .nil => FreeVars.empty
  | .cons arm arms =>
      let armFree := collectFreeVarsArm arm
      FreeVars.union armFree (collectFreeVarsArmList arms)

partial def collectFreeVarsArm : Arm Value scope → FreeVars
  | .mk patterns body _ =>
      let bodyFree := collectFreeVars body
      bodyFree.removeMany patterns.bindingIds

partial def collectFreeVarsCaptureList : CaptureList Value scope → FreeVars
  | .nil => FreeVars.empty
  | .cons v ty rest =>
      FreeVars.union (FreeVars.singleton v.binding v.original ty) (collectFreeVarsCaptureList rest)

partial def collectFreeVarsRecordFieldList : RecordFieldList Value scope → FreeVars
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
  ty : Value

/-- Unscoped parameter -/
structure UParam where
  binding : BindingId
  name : String
  ty : Value

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
  | call (fn : UExpr) (args : Array UExpr) (ty : Value) (span : Span)
  | lam (params : Array UParam) (body : UExpr) (ty : Value) (span : Span)
  | closure (name : Name) (captures : Array UVar) (ty : Value) (span : Span)
  | construct (name : Name) (tag : Nat) (args : Array UExpr) (ty : Value) (span : Span)
  | tuple (elems : Array UExpr) (ty : Value) (span : Span)
  | record (fields : Array (String × UExpr)) (ty : Value) (span : Span)
  | recordUpdate (base : UExpr) (updates : Array (String × UExpr)) (ty : Value) (span : Span)
  | inject (label : String) (args : Array UExpr) (ty : Value) (span : Span)
  | array (elems : Array UExpr) (ty : Value) (span : Span)
  | if_ (cond : UExpr) (then_ : UExpr) (else_ : UExpr) (ty : Value) (span : Span)
  | case (scruts : Array UExpr) (arms : Array (Array UPattern × UExpr)) (ty : Value) (span : Span)
  | fieldAccess (expr : UExpr) (fieldName : String) (fieldIdx : Nat) (ty : Value) (span : Span)
  | global (name : Name) (ty : Value) (span : Span)
  | panic (msg : String) (ty : Value) (span : Span)
  | proj (typeName : Name) (fieldName : String) (fieldIdx : Nat) (ty : Value) (span : Span)
  | typeApp (arg : TypeArg) (ty : Value) (span : Span)
  | type (level : Soma.Core.Level) (span : Span)
  | pi (qty : Soma.Core.Quantity) (binder : BinderInfo) (name : String)
       (dom : UExpr) (cod : UExpr) (span : Span)
  | sigma (qty : Soma.Core.Quantity) (name : String) (fst : UExpr) (snd : UExpr) (span : Span)
  | pair (fst : UExpr) (snd : UExpr) (ty : Value) (span : Span)
  | fst (e : UExpr) (ty : Value) (span : Span)
  | snd (e : UExpr) (ty : Value) (span : Span)
  | primTy (p : Soma.Core.StarPrimitive) (span : Span)
  | higherPrimTy (p : Soma.Core.HigherPrimitive) (span : Span)
  | rowEmpty (span : Span)
  | rowExtend (label : UExpr) (fieldTy : UExpr) (tail : UExpr) (span : Span)
  | recordTy (row : UExpr) (span : Span)
  | variantTy (row : UExpr) (span : Span)
  | labelLit (name : String) (span : Span)
  | dataTy (id : Soma.Core.TypeId) (params : Array UExpr) (span : Span)
  | ann (expr : UExpr) (ty : UExpr) (exprTy : Value) (span : Span)
  | hole (id : HoleId) (span : Span)
  | mvar (id : Nat) (ty : Value) (span : Span)
  | eq (tyLevel : Soma.Core.Level) (ty : UExpr) (lhs : UExpr) (rhs : UExpr) (span : Span)
  | refl (ty : UExpr) (x : UExpr) (span : Span)
  | transport (tyLevel : Soma.Core.Level) (ty : UExpr) (motive : UExpr)
              (lhs : UExpr) (rhs : UExpr) (eq : UExpr) (body : UExpr) (span : Span)
  deriving Inhabited

/-! ## Conversion to Unscoped -/

/-- Default type for expressions without type info -/
def defaultTy : Value := Value.vType Soma.Core.Level.zero

mutual

partial def patternToU : Pattern Value → UPattern
  | .var binding name _ _ => .var binding name
  | .wildcard _ _ => .wildcard
  | .lit l _ => .lit l
  | .ctor name args _ _ => .ctor name (args.map patternToU)
  | .tuple elems _ _ => .tuple (elems.map patternToU)
  | .array elems _ _ => .array (elems.map patternToU)
  | .cons h t _ _ => .cons (patternToU h) (patternToU t)
  | .as binding name inner _ _ => .as binding name (patternToU inner)
  | .variant label arg _ _ => .variant label (arg.map patternToU)

partial def patternListToU : PatternList Value → Array UPattern
  | .nil => #[]
  | .cons p ps => #[patternToU p] ++ patternListToU ps

partial def exprToU : Expr Value scope → UExpr
  | .var v ty span => .var ⟨v.binding, v.original, ty⟩ span
  | .lit l span => .lit l span
  | .call fn args ty span => .call (exprToU fn) (exprListToU args) ty span
  | .lam params body ty span =>
      let ps := params.toList.map fun (b, n, paramTy) => UParam.mk b n paramTy
      .lam ps.toArray (exprToU body) ty span
  | .closure name caps ty span => .closure name (captureListToU caps) ty span
  | .construct name tag args ty span => .construct name tag (exprListToU args) ty span
  | .tuple elems ty span => .tuple (exprListToU elems) ty span
  | .record fields ty span => .record (recordFieldListToU fields) ty span
  | .recordUpdate base updates ty span =>
      .recordUpdate (exprToU base) (recordFieldListToU updates) ty span
  | .inject label args ty span => .inject label (exprListToU args) ty span
  | .array elems ty span => .array (exprListToU elems) ty span
  | .if_ c t e ty span => .if_ (exprToU c) (exprToU t) (exprToU e) ty span
  | .case scruts arms ty span =>
      .case (exprListToU scruts) (armListToU arms) ty span
  | .fieldAccess e fn fi ty span => .fieldAccess (exprToU e) fn fi ty span
  | .global name ty span => .global name ty span
  | .panic msg ty span => .panic msg ty span
  | .proj tn fn fi ty span => .proj tn fn fi ty span
  | .typeApp arg ty span => .typeApp arg ty span
  | .type l span => .type l span
  | .pi q bi n d c span => .pi q bi n (exprToU d) (exprToU c) span
  | .sigma q n f s span => .sigma q n (exprToU f) (exprToU s) span
  | .pair f s ty span => .pair (exprToU f) (exprToU s) ty span
  | .fst e ty span => .fst (exprToU e) ty span
  | .snd e ty span => .snd (exprToU e) ty span
  | .primTy p span => .primTy p span
  | .higherPrimTy p span => .higherPrimTy p span
  | .rowEmpty span => .rowEmpty span
  | .rowExtend l f t span => .rowExtend (exprToU l) (exprToU f) (exprToU t) span
  | .recordTy r span => .recordTy (exprToU r) span
  | .variantTy r span => .variantTy (exprToU r) span
  | .labelLit n span => .labelLit n span
  | .dataTy id ps span => .dataTy id (exprListToU ps) span
  | .ann e t ty span => .ann (exprToU e) (exprToU t) ty span
  | .hole id span => .hole id span
  | .mvar id ty span => .mvar id ty span
  | .eq tl t l r span => .eq tl (exprToU t) (exprToU l) (exprToU r) span
  | .refl t x span => .refl (exprToU t) (exprToU x) span
  | .transport tl t m l r eq b span =>
      .transport tl (exprToU t) (exprToU m) (exprToU l) (exprToU r) (exprToU eq) (exprToU b) span

partial def exprListToU : ExprList Value scope → Array UExpr
  | .nil => #[]
  | .cons e es => #[exprToU e] ++ exprListToU es

partial def captureListToU : CaptureList Value scope → Array UVar
  | .nil => #[]
  | .cons v ty rest => #[⟨v.binding, v.original, ty⟩] ++ captureListToU rest

partial def armListToU : ArmList Value scope → Array (Array UPattern × UExpr)
  | .nil => #[]
  | .cons (.mk pats body _) rest =>
      #[(patternListToU pats, exprToU body)] ++ armListToU rest

partial def recordFieldListToU : RecordFieldList Value scope → Array (String × UExpr)
  | .nil => #[]
  | .cons name expr rest => #[(name, exprToU expr)] ++ recordFieldListToU rest

end

/-! ## Conversion from Unscoped -/

/-- Convert UPattern back to Pattern, producing bindings -/
partial def uToPattern (p : UPattern) : Pattern Value :=
  match p with
  | .var b n => .var b n defaultTy Span.uninhabited
  | .wildcard => .wildcard defaultTy Span.uninhabited
  | .lit l => .lit l Span.uninhabited
  | .ctor name args => .ctor name (args.map uToPattern) defaultTy Span.uninhabited
  | .tuple elems => .tuple (elems.map uToPattern) defaultTy Span.uninhabited
  | .array elems => .array (elems.map uToPattern) defaultTy Span.uninhabited
  | .cons h t => .cons (uToPattern h) (uToPattern t) defaultTy Span.uninhabited
  | .as b n inner => .as b n (uToPattern inner) defaultTy Span.uninhabited
  | .variant label arg => .variant label (arg.map uToPattern) defaultTy Span.uninhabited

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
partial def uToExpr (e : UExpr) (scope : Scope) : Expr Value scope :=
  match e with
  | .var v span =>
      let sv : ScopedVar scope := ⟨v.binding, v.original, by sorry⟩
      .var sv v.ty span
  | .lit l span => .lit l span
  | .call fn args ty span =>
      let fn' := uToExpr fn scope
      let args' := uToExprList args scope
      .call fn' args' ty span
  | .lam params body ty span =>
      let paramList := paramsToParamList params
      let bodyScope := params.toList.map (·.binding) ++ scope
      let body' := uToExpr body bodyScope
      let body'' : Expr Value (paramList.bindingIds ++ scope) := by
        have h : paramList.bindingIds = params.toList.map (·.binding) := by
          sorry
        rw [h]; exact body'
      .lam paramList body'' ty span
  | .closure name caps ty span =>
      let capList := uToCaptureList caps scope
      .closure name capList ty span
  | .construct name tag args ty span =>
      .construct name tag (uToExprList args scope) ty span
  | .tuple elems ty span =>
      .tuple (uToExprList elems scope) ty span
  | .record fields ty span =>
      .record (uToRecordFieldList fields scope) ty span
  | .recordUpdate base updates ty span =>
      .recordUpdate (uToExpr base scope) (uToRecordFieldList updates scope) ty span
  | .inject label args ty span =>
      .inject label (uToExprList args scope) ty span
  | .array elems ty span =>
      .array (uToExprList elems scope) ty span
  | .if_ c t e ty span =>
      .if_ (uToExpr c scope) (uToExpr t scope) (uToExpr e scope) ty span
  | .case scruts arms ty span =>
      .case (uToExprList scruts scope) (uToArmList arms scope) ty span
  | .fieldAccess expr fn fi ty span =>
      .fieldAccess (uToExpr expr scope) fn fi ty span
  | .global name ty span => .global name ty span
  | .panic msg ty span => .panic msg ty span
  | .proj tn fn fi ty span => .proj tn fn fi ty span
  | .typeApp arg ty span => .typeApp arg ty span
  | .type l span => .type l span
  | .pi q bi n d c span => .pi q bi n (uToExpr d scope) (uToExpr c scope) span
  | .sigma q n f s span => .sigma q n (uToExpr f scope) (uToExpr s scope) span
  | .pair f s ty span => .pair (uToExpr f scope) (uToExpr s scope) ty span
  | .fst e ty span => .fst (uToExpr e scope) ty span
  | .snd e ty span => .snd (uToExpr e scope) ty span
  | .primTy p span => .primTy p span
  | .higherPrimTy p span => .higherPrimTy p span
  | .rowEmpty span => .rowEmpty span
  | .rowExtend l f t span =>
      .rowExtend (uToExpr l scope) (uToExpr f scope) (uToExpr t scope) span
  | .recordTy r span => .recordTy (uToExpr r scope) span
  | .variantTy r span => .variantTy (uToExpr r scope) span
  | .labelLit n span => .labelLit n span
  | .dataTy id ps span => .dataTy id (uToExprList ps scope) span
  | .ann e t ty span => .ann (uToExpr e scope) (uToExpr t scope) ty span
  | .hole id span => .hole id span
  | .mvar id ty span => .mvar id ty span
  | .eq tl t l r span =>
      .eq tl (uToExpr t scope) (uToExpr l scope) (uToExpr r scope) span
  | .refl t x span => .refl (uToExpr t scope) (uToExpr x scope) span
  | .transport tl t m l r eq b span =>
      .transport tl (uToExpr t scope) (uToExpr m scope) (uToExpr l scope)
                 (uToExpr r scope) (uToExpr eq scope) (uToExpr b scope) span
where
  paramsToParamList (params : Array UParam) : ParamList Value :=
    params.foldr (init := .nil) fun p acc => .cons p.binding p.name p.ty acc

  uToExprList (es : Array UExpr) (scope : Scope) : ExprList Value scope :=
    es.foldr (init := .nil) fun e acc => .cons (uToExpr e scope) acc

  uToCaptureList (caps : Array UVar) (scope : Scope) : CaptureList Value scope :=
    caps.foldr (init := .nil) fun v acc =>
      .cons ⟨v.binding, v.original, by sorry⟩ v.ty acc

  uToRecordFieldList (fields : Array (String × UExpr)) (scope : Scope)
      : RecordFieldList Value scope :=
    fields.foldr (init := .nil) fun (n, e) acc => .cons n (uToExpr e scope) acc

  uToArmList (arms : Array (Array UPattern × UExpr)) (scope : Scope)
      : ArmList Value scope :=
    arms.foldr (init := .nil) fun (pats, body) acc =>
      let patList := pats.foldr (init := PatternList.nil) fun p acc =>
        .cons (uToPattern p) acc
      let armBindings := pats.toList.flatMap uPatternBindings
      let armScope := armBindings ++ scope
      let body' := uToExpr body armScope
      let body'' : Expr Value (patList.bindingIds ++ scope) := by
        have h : patList.bindingIds = armBindings := by sorry
        rw [h]
        exact body'
      .cons (.mk patList body'' Span.uninhabited) acc

/-! ## Variable Substitution on UExpr -/

/-- Substitution map: old BindingId -> (new BindingId, new type) -/
abbrev Subst := HashMap BindingId (BindingId × Value)

/-- Apply substitution to a UExpr -/
partial def substUExpr (subst : Subst) : UExpr → UExpr
  | .var v span =>
      match subst.get? v.binding with
      | some (newB, newTy) => .var ⟨newB, v.original, newTy⟩ span
      | none => .var v span
  | .lit l span => .lit l span
  | .call fn args ty span => .call (substUExpr subst fn) (args.map (substUExpr subst)) ty span
  | .lam params body ty span =>
      let subst' := params.foldl (init := subst) fun s p => s.erase p.binding
      .lam params (substUExpr subst' body) ty span
  | .closure name caps ty span =>
      let caps' := caps.map fun v =>
        match subst.get? v.binding with
        | some (newB, newTy) => ⟨newB, v.original, newTy⟩
        | none => v
      .closure name caps' ty span
  | .construct name tag args ty span =>
      .construct name tag (args.map (substUExpr subst)) ty span
  | .tuple elems ty span => .tuple (elems.map (substUExpr subst)) ty span
  | .record fields ty span =>
      .record (fields.map fun (n, e) => (n, substUExpr subst e)) ty span
  | .recordUpdate base updates ty span =>
      .recordUpdate (substUExpr subst base)
                    (updates.map fun (n, e) => (n, substUExpr subst e)) ty span
  | .inject label args ty span => .inject label (args.map (substUExpr subst)) ty span
  | .array elems ty span => .array (elems.map (substUExpr subst)) ty span
  | .if_ c t e ty span => .if_ (substUExpr subst c) (substUExpr subst t) (substUExpr subst e) ty span
  | .case scruts arms ty span =>
      let scruts' := scruts.map (substUExpr subst)
      let arms' := arms.map fun (pats, body) =>
        let patBindings := pats.toList.flatMap uPatternBindings
        let subst' := patBindings.foldl (init := subst) fun s b => s.erase b
        (pats, substUExpr subst' body)
      .case scruts' arms' ty span
  | .fieldAccess e fn fi ty span => .fieldAccess (substUExpr subst e) fn fi ty span
  | .global name ty span => .global name ty span
  | .panic msg ty span => .panic msg ty span
  | .proj tn fn fi ty span => .proj tn fn fi ty span
  | .typeApp arg ty span => .typeApp arg ty span
  | .type l span => .type l span
  | .pi q bi n d c span => .pi q bi n (substUExpr subst d) (substUExpr subst c) span
  | .sigma q n f s span => .sigma q n (substUExpr subst f) (substUExpr subst s) span
  | .pair f s ty span => .pair (substUExpr subst f) (substUExpr subst s) ty span
  | .fst e ty span => .fst (substUExpr subst e) ty span
  | .snd e ty span => .snd (substUExpr subst e) ty span
  | .primTy p span => .primTy p span
  | .higherPrimTy p span => .higherPrimTy p span
  | .rowEmpty span => .rowEmpty span
  | .rowExtend l f t span =>
      .rowExtend (substUExpr subst l) (substUExpr subst f) (substUExpr subst t) span
  | .recordTy r span => .recordTy (substUExpr subst r) span
  | .variantTy r span => .variantTy (substUExpr subst r) span
  | .labelLit n span => .labelLit n span
  | .dataTy id ps span => .dataTy id (ps.map (substUExpr subst)) span
  | .ann e t ty span => .ann (substUExpr subst e) (substUExpr subst t) ty span
  | .hole id span => .hole id span
  | .mvar id ty span => .mvar id ty span
  | .eq tl t l r span =>
      .eq tl (substUExpr subst t) (substUExpr subst l) (substUExpr subst r) span
  | .refl t x span => .refl (substUExpr subst t) (substUExpr subst x) span
  | .transport tl t m l r eq b span =>
      .transport tl (substUExpr subst t) (substUExpr subst m) (substUExpr subst l)
                 (substUExpr subst r) (substUExpr subst eq) (substUExpr subst b) span

/-! ## Lambda Lifting on UExpr -/

/-- Collect free variables from UExpr -/
partial def collectFreeVarsU : UExpr → FreeVars
  | .var v _ => FreeVars.singleton v.binding v.original v.ty
  | .lit _ _ => FreeVars.empty
  | .call fn args _ _ =>
      FreeVars.union (collectFreeVarsU fn) (FreeVars.unions (args.toList.map collectFreeVarsU))
  | .lam params body _ _ =>
      let bodyFree := collectFreeVarsU body
      bodyFree.removeMany (params.toList.map (·.binding))
  | .closure _ caps _ _ =>
      FreeVars.unions (caps.toList.map fun v => FreeVars.singleton v.binding v.original v.ty)
  | .construct _ _ args _ _ => FreeVars.unions (args.toList.map collectFreeVarsU)
  | .tuple elems _ _ => FreeVars.unions (elems.toList.map collectFreeVarsU)
  | .record fields _ _ => FreeVars.unions (fields.toList.map fun (_, e) => collectFreeVarsU e)
  | .recordUpdate base updates _ _ =>
      FreeVars.union (collectFreeVarsU base)
                     (FreeVars.unions (updates.toList.map fun (_, e) => collectFreeVarsU e))
  | .inject _ args _ _ => FreeVars.unions (args.toList.map collectFreeVarsU)
  | .array elems _ _ => FreeVars.unions (elems.toList.map collectFreeVarsU)
  | .if_ c t e _ _ => FreeVars.unions [collectFreeVarsU c, collectFreeVarsU t, collectFreeVarsU e]
  | .case scruts arms _ _ =>
      let scrutFree := FreeVars.unions (scruts.toList.map collectFreeVarsU)
      let armsFree := FreeVars.unions (arms.toList.map fun (pats, body) =>
        let patBindings := pats.toList.flatMap uPatternBindings
        (collectFreeVarsU body).removeMany patBindings)
      FreeVars.union scrutFree armsFree
  | .fieldAccess e _ _ _ _ => collectFreeVarsU e
  | .global _ _ _ => FreeVars.empty
  | .panic _ _ _ => FreeVars.empty
  | .proj _ _ _ _ _ => FreeVars.empty
  | .typeApp _ _ _ => FreeVars.empty
  | .type _ _ => FreeVars.empty
  | .pi _ _ _ d c _ => FreeVars.union (collectFreeVarsU d) (collectFreeVarsU c)
  | .sigma _ _ f s _ => FreeVars.union (collectFreeVarsU f) (collectFreeVarsU s)
  | .pair f s _ _ => FreeVars.union (collectFreeVarsU f) (collectFreeVarsU s)
  | .fst e _ _ => collectFreeVarsU e
  | .snd e _ _ => collectFreeVarsU e
  | .primTy _ _ => FreeVars.empty
  | .higherPrimTy _ _ => FreeVars.empty
  | .rowEmpty _ => FreeVars.empty
  | .rowExtend l f t _ =>
      FreeVars.unions [collectFreeVarsU l, collectFreeVarsU f, collectFreeVarsU t]
  | .recordTy r _ => collectFreeVarsU r
  | .variantTy r _ => collectFreeVarsU r
  | .labelLit _ _ => FreeVars.empty
  | .dataTy _ ps _ => FreeVars.unions (ps.toList.map collectFreeVarsU)
  | .ann e t _ _ => FreeVars.union (collectFreeVarsU e) (collectFreeVarsU t)
  | .hole _ _ => FreeVars.empty
  | .mvar _ _ _ => FreeVars.empty
  | .eq _ t l r _ => FreeVars.unions [collectFreeVarsU t, collectFreeVarsU l, collectFreeVarsU r]
  | .refl t x _ => FreeVars.union (collectFreeVarsU t) (collectFreeVarsU x)
  | .transport _ t m l r eq b _ =>
      FreeVars.unions [collectFreeVarsU t, collectFreeVarsU m, collectFreeVarsU l,
                       collectFreeVarsU r, collectFreeVarsU eq, collectFreeVarsU b]

/-- Build a function type from parameter types and result type -/
def buildFnType (paramTypes : Array Value) (resultType : Value) : Value :=
  paramTypes.foldr (init := resultType) fun paramTy acc =>
    Value.vPi Soma.Core.Quantity.omega BinderInfo.explicit "_" paramTy (Soma.Core.Closure.const "_" acc)

/-- Lift lambdas in a UExpr -/
partial def liftUExpr (e : UExpr) : LiftM UExpr := do
  match e with
  | .var v span => pure (.var v span)
  | .lit l span => pure (.lit l span)
  | .call fn args ty span => do
      let fn' ← liftUExpr fn
      let args' ← args.mapM liftUExpr
      pure (.call fn' args' ty span)

  | .lam params body ty span => do
      -- First, lift any nested lambdas in the body
      let body' ← liftUExpr body

      -- Collect free variables in the body
      let allFree := collectFreeVarsU body'
      -- Remove lambda's own parameters
      let freeAfterParams := allFree.removeMany (params.toList.map (·.binding))

      -- Filter out globals
      let mut captures : Array (BindingId × String × Value) := #[]
      for (b, name, capTy) in freeAfterParams.toArray do
        let isGlob ← LiftM.isGlobal (.user { id := b.id, module := b.module, original := name })
        if !isGlob then
          captures := captures.push (b, name, capTy)

      -- Generate fresh binding IDs for capture parameters
      let mut captureParams : Array UParam := #[]
      let mut subst : Subst := {}
      for (oldB, name, capTy) in captures do
        let newB ← LiftM.freshBindingId name
        captureParams := captureParams.push ⟨newB, name, capTy⟩
        subst := subst.insert oldB (newB, capTy)

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

      -- Build the function type for the lifted function
      let allParamTypes := allParams.map (·.ty)
      let resultType := ty.piCodomain?.getD defaultTy
      let liftedFnType := buildFnType allParamTypes resultType

      let liftedFn : TypedFunction := {
        name := liftedName
        params := liftedParams
        body := liftedBody
        fnType := liftedFnType
        closureInfo := some { capturedVars := captures.map fun (b, n, _) => (b, n) }
        attrs := {}
      }

      LiftM.addLiftedFunction liftedFn

      -- Return closure expression with original captured variables (and their types)
      let captureVars := captures.map fun (b, n, capTy) => UVar.mk b n capTy
      pure (.closure liftedName captureVars ty span)

  | .closure name caps ty span => pure (.closure name caps ty span)
  | .construct name tag args ty span => do
      let args' ← args.mapM liftUExpr
      pure (.construct name tag args' ty span)
  | .tuple elems ty span => do
      let elems' ← elems.mapM liftUExpr
      pure (.tuple elems' ty span)
  | .record fields ty span => do
      let fields' ← fields.mapM fun (n, e) => do
        let e' ← liftUExpr e
        pure (n, e')
      pure (.record fields' ty span)
  | .recordUpdate base updates ty span => do
      let base' ← liftUExpr base
      let updates' ← updates.mapM fun (n, e) => do
        let e' ← liftUExpr e
        pure (n, e')
      pure (.recordUpdate base' updates' ty span)
  | .inject label args ty span => do
      let args' ← args.mapM liftUExpr
      pure (.inject label args' ty span)
  | .array elems ty span => do
      let elems' ← elems.mapM liftUExpr
      pure (.array elems' ty span)
  | .if_ c t e ty span => do
      let c' ← liftUExpr c
      let t' ← liftUExpr t
      let e' ← liftUExpr e
      pure (.if_ c' t' e' ty span)
  | .case scruts arms ty span => do
      let scruts' ← scruts.mapM liftUExpr
      let arms' ← arms.mapM fun (pats, body) => do
        let body' ← liftUExpr body
        pure (pats, body')
      pure (.case scruts' arms' ty span)
  | .fieldAccess e fn fi ty span => do
      let e' ← liftUExpr e
      pure (.fieldAccess e' fn fi ty span)
  | .global name ty span => pure (.global name ty span)
  | .panic msg ty span => pure (.panic msg ty span)
  | .proj tn fn fi ty span => pure (.proj tn fn fi ty span)
  | .typeApp arg ty span => pure (.typeApp arg ty span)
  | .type l span => pure (.type l span)
  | .pi q bi n d c span => do
      let d' ← liftUExpr d
      let c' ← liftUExpr c
      pure (.pi q bi n d' c' span)
  | .sigma q n f s span => do
      let f' ← liftUExpr f
      let s' ← liftUExpr s
      pure (.sigma q n f' s' span)
  | .pair f s ty span => do
      let f' ← liftUExpr f
      let s' ← liftUExpr s
      pure (.pair f' s' ty span)
  | .fst e ty span => do
      let e' ← liftUExpr e
      pure (.fst e' ty span)
  | .snd e ty span => do
      let e' ← liftUExpr e
      pure (.snd e' ty span)
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
  | .ann e t ty span => do
      let e' ← liftUExpr e
      let t' ← liftUExpr t
      pure (.ann e' t' ty span)
  | .hole id span => pure (.hole id span)
  | .mvar id ty span => pure (.mvar id ty span)
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
where
  /-- Extract result type from a function type -/
  UExpr.piCodomain? : UExpr → Option Value
    | .lam _ _ ty _ => some (ty.piCodomain?.getD defaultTy)
    | _ => none

/-! ## Function and Module Lifting -/

/-- Lift lambdas in a single typed function -/
def liftTypedFunction (fn : TypedFunction) : LiftM TypedFunction := do
  -- Convert to unscoped
  let uBody := exprToU fn.body
  -- Lift lambdas
  let uBody' ← liftUExpr uBody
  -- Convert back to scoped
  let scope := fn.params.toList.map (·.1)
  let body' := uToExpr uBody' scope
  pure { fn with body := body' }

/-- Map from function name to typed function -/
abbrev TypedFunctionMap := Std.HashMap String TypedFunction

/-- Lift lambdas in all typed functions -/
def liftTypedFunctions (typedFunctions : TypedFunctionMap) (moduleName : String) : TypedFunctionMap × Array TypedFunction := Id.run do
  -- Collect global names (all top-level functions)
  let globalNames : HashSet Name := typedFunctions.fold (init := {}) fun acc _ fn =>
    acc.insert fn.name

  -- Run the lifting pass
  let (liftedFunctions, finalState) := LiftM.run (do
    let mut result : TypedFunctionMap := {}
    for (fnName, fn) in typedFunctions.toList do
      let fn' ← liftTypedFunction fn
      result := result.insert fnName fn'
    pure result
  ) moduleName globalNames

  -- Return both the lifted original functions and the newly generated closures
  (liftedFunctions, finalState.liftedFunctions)

/-- Lift lambdas in typed functions, returning merged map with all functions -/
def liftAll (typedFunctions : TypedFunctionMap) (moduleName : String) : TypedFunctionMap :=
  let (lifted, generated) := liftTypedFunctions typedFunctions moduleName
  -- Merge generated functions into the map
  generated.foldl (init := lifted) fun acc fn =>
    acc.insert fn.name.display fn

/-! ## Legacy API for untyped modules (deprecated) -/

/-- Lift lambdas in an untyped module (legacy API - converts to typed and back) -/
def liftModule (m : Module) : Module := Id.run do
  -- Collect global names (all top-level functions)
  let globalNames : HashSet Name := m.functions.foldl (init := {}) fun acc fn =>
    acc.insert fn.name

  -- Also add constructor names as globals
  let globalNames := m.types.foldl (init := globalNames) fun acc typeDef =>
    typeDef.constructors.foldl (init := acc) fun acc' ctor => acc'.insert ctor.name

  -- Run the lifting pass on untyped functions (convert Unit -> Value temporarily)
  let (liftedFunctions, finalState) := LiftM.run (do
    let mut result := #[]
    for fn in m.functions do
      -- Convert untyped to "typed" with default types
      let typedBody := fn.body.mapInfo (fun () => defaultTy)
      let pseudoTyped : TypedFunction := {
        name := fn.name
        params := fn.params
        body := typedBody
        fnType := defaultTy
        closureInfo := fn.closureInfo
        attrs := fn.attrs
      }
      let fn' ← liftTypedFunction pseudoTyped
      -- Convert back to untyped
      let untypedBody := fn'.body.mapInfo (fun _ => ())
      let untyped : UntypedFunction := {
        name := fn'.name
        params := fn'.params
        body := untypedBody
        declaredTypeSyntax := fn.declaredTypeSyntax
        closureInfo := fn'.closureInfo
        attrs := fn'.attrs
      }
      result := result.push untyped
    pure result
  ) m.name globalNames

  -- Convert lifted typed functions back to untyped
  let liftedUntyped := finalState.liftedFunctions.map fun fn =>
    let untypedBody := fn.body.mapInfo (fun _ => ())
    ({ name := fn.name
       params := fn.params
       body := untypedBody
       declaredTypeSyntax := none
       closureInfo := fn.closureInfo
       attrs := fn.attrs } : UntypedFunction)

  -- Combine original (lifted) functions with newly generated ones
  let allFunctions := liftedFunctions ++ liftedUntyped

  { m with functions := allFunctions }

end Soma.Metal.LambdaLift
