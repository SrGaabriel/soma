import Soma.Metal.Name
import Soma.Metal.Scope
import Soma.Metal.Literal
import Soma.Metal.Pattern
import Soma.Syntax.Source

open Soma.Typing
open Soma.Metal
open Soma.Syntax (Span)

/-- List of parameters (for lambda) - defined before Expr since it doesn't depend on it -/
inductive Soma.Metal.ParamList (α : Type) : Type where
  | nil : Soma.Metal.ParamList α
  | cons (binding : BindingId) (name : String) (info : α) : Soma.Metal.ParamList α → Soma.Metal.ParamList α

namespace Soma.Metal.ParamList

def toList : ParamList α → List (BindingId × String × α)
  | .nil => []
  | .cons b n i ps => (b, n, i) :: ps.toList

def fromList : List (BindingId × String × α) → ParamList α
  | [] => .nil
  | (b, n, i) :: ps => .cons b n i (fromList ps)

def bindingIds : ParamList α → List BindingId
  | .nil => []
  | .cons b _ _ ps => b :: ps.bindingIds

def length : ParamList α → Nat
  | .nil => 0
  | .cons _ _ _ ps => 1 + ps.length

end Soma.Metal.ParamList

/-- List of patterns (for case arms) - defined before Expr -/
inductive Soma.Metal.PatternList (α : Type) : Type where
  | nil : Soma.Metal.PatternList α
  | cons : Pattern α → Soma.Metal.PatternList α → Soma.Metal.PatternList α

namespace Soma.Metal.PatternList

def toList : PatternList α → List (Pattern α)
  | .nil => []
  | .cons p ps => p :: ps.toList

def fromList : List (Pattern α) → PatternList α
  | [] => .nil
  | p :: ps => .cons p (fromList ps)

def bindingIds : PatternList α → List BindingId
  | .nil => []
  | .cons p ps => p.bindings.toList ++ ps.bindingIds

end Soma.Metal.PatternList

mutual

inductive Soma.Metal.Expr (α : Type) : Scope → Type where
  /-- Local variable reference (must be in scope) -/
  | var (v : ScopedVar scope) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Literal value -/
  | lit (lit : Literal) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Function call / application -/
  | call (fn : Soma.Metal.Expr α scope) (args : Soma.Metal.ExprList α scope) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Let binding: let x = value in body -/
  | let_ (binding : BindingId) (original : String)
         (value : Soma.Metal.Expr α scope)
         (body : Soma.Metal.Expr α (binding :: scope))
         (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Lambda expression: \params -> body -/
  | lam (params : Soma.Metal.ParamList α)
        (body : Soma.Metal.Expr α (params.bindingIds ++ scope))
        (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Closure (lifted lambda with captured environment) -/
  | closure (liftedName : Name)
            (captures : Soma.Metal.CaptureList α scope)
            (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- ADT constructor application -/
  | construct (name : Name) (tag : Nat) (args : Soma.Metal.ExprList α scope) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Tuple construction -/
  | tuple (elements : Soma.Metal.ExprList α scope) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Array literal -/
  | array (elements : Soma.Metal.ExprList α scope) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- If-then-else -/
  | if_ (cond : Soma.Metal.Expr α scope) (then_ : Soma.Metal.Expr α scope) (else_ : Soma.Metal.Expr α scope) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Case expression (pattern matching) -/
  | case (scrutinees : Soma.Metal.ExprList α scope)
         (arms : Soma.Metal.ArmList α scope)
         (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Field access (for structs/tuples) -/
  | fieldAccess (expr : Soma.Metal.Expr α scope) (index : Nat) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Global reference (top-level function or value) -/
  | global (name : Name) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Panic (abort with message) -/
  | panic (message : String) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

/-- List of expressions at the same scope -/
inductive Soma.Metal.ExprList (α : Type) : Scope → Type where
  | nil : Soma.Metal.ExprList α scope
  | cons : Soma.Metal.Expr α scope → Soma.Metal.ExprList α scope → Soma.Metal.ExprList α scope

/-- A case arm with patterns that extend the scope -/
inductive Soma.Metal.Arm (α : Type) : Scope → Type where
  | mk (patterns : Soma.Metal.PatternList α)
       (body : Soma.Metal.Expr α (patterns.bindingIds ++ scope))
       (span : Span)
      : Soma.Metal.Arm α scope

/-- List of arms -/
inductive Soma.Metal.ArmList (α : Type) : Scope → Type where
  | nil : Soma.Metal.ArmList α scope
  | cons : Soma.Metal.Arm α scope → Soma.Metal.ArmList α scope → Soma.Metal.ArmList α scope

/-- List of captures (scoped variables with type info) -/
inductive Soma.Metal.CaptureList (α : Type) : Scope → Type where
  | nil : Soma.Metal.CaptureList α scope
  | cons : ScopedVar scope → α → Soma.Metal.CaptureList α scope → Soma.Metal.CaptureList α scope

end

-- Nonempty instances for partial function compilation
instance : Nonempty (Soma.Metal.CaptureList α scope) := ⟨.nil⟩
instance : Nonempty (Soma.Metal.ExprList α scope) := ⟨.nil⟩
instance : Nonempty (Soma.Metal.ArmList α scope) := ⟨.nil⟩
instance : Nonempty (Soma.Metal.ParamList α) := ⟨.nil⟩
instance : Nonempty (Soma.Metal.PatternList α) := ⟨.nil⟩

-- Use lit for Expr since it doesn't require α
instance : Nonempty (Soma.Metal.Expr α scope) :=
  ⟨.lit (Soma.Metal.Literal.int 0) Soma.Syntax.Span.uninhabited⟩

instance : Nonempty (Soma.Metal.Arm α scope) :=
  ⟨.mk .nil (.lit (Soma.Metal.Literal.int 0) Soma.Syntax.Span.uninhabited) Soma.Syntax.Span.uninhabited⟩

/-! ## mapInfo: Transform annotation type across expressions -/

/-- Map a function over the annotation type of a param list -/
def Soma.Metal.ParamList.mapInfo (f : α → β) : Soma.Metal.ParamList α → Soma.Metal.ParamList β
  | .nil => .nil
  | .cons b n info rest => .cons b n (f info) (rest.mapInfo f)

/-- ParamList.mapInfo preserves bindingIds -/
theorem Soma.Metal.ParamList.mapInfo_bindingIds (f : α → β) (ps : Soma.Metal.ParamList α) :
    (ps.mapInfo f).bindingIds = ps.bindingIds := by
  induction ps with
  | nil => rfl
  | cons b n info rest ih => simp only [mapInfo, ParamList.bindingIds, ih]

/-- Map a function over the annotation type of a pattern list -/
def Soma.Metal.PatternList.mapInfo (f : α → β) : Soma.Metal.PatternList α → Soma.Metal.PatternList β
  | .nil => .nil
  | .cons p ps => .cons (p.map f) (ps.mapInfo f)

/-- PatternList.mapInfo preserves bindingIds -/
theorem Soma.Metal.PatternList.mapInfo_bindingIds (f : α → β) (ps : Soma.Metal.PatternList α) :
    (ps.mapInfo f).bindingIds = ps.bindingIds := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    simp only [mapInfo, PatternList.bindingIds]
    rw [ih]
    congr 1
    have h := Soma.Metal.Pattern.map_bindings f p
    exact congrArg Array.toList h

mutual

/-- Map a function over the annotation type of an expression -/
partial def Soma.Metal.Expr.mapInfo (f : α → β) : Soma.Metal.Expr α scope → Soma.Metal.Expr β scope
  | .var v info span => .var v (f info) span
  | .lit lit span => .lit lit span
  | .call fn args info span => .call (fn.mapInfo f) (args.mapInfo f) (f info) span
  | .let_ b orig val body info span => .let_ b orig (val.mapInfo f) (body.mapInfo f) (f info) span
  | .lam params body info span =>
      let params' := params.mapInfo f
      let body' := Soma.Metal.Expr.mapInfo f body
      let h : params'.bindingIds ++ scope = params.bindingIds ++ scope := by
        rw [Soma.Metal.ParamList.mapInfo_bindingIds]
      .lam params' (h ▸ body') (f info) span
  | .closure name caps info span => .closure name (caps.mapInfo f) (f info) span
  | .construct name tag args info span => .construct name tag (args.mapInfo f) (f info) span
  | .tuple elems info span => .tuple (elems.mapInfo f) (f info) span
  | .array elems info span => .array (elems.mapInfo f) (f info) span
  | .if_ c t e info span => .if_ (c.mapInfo f) (t.mapInfo f) (e.mapInfo f) (f info) span
  | .case scruts arms info span => .case (scruts.mapInfo f) (arms.mapInfo f) (f info) span
  | .fieldAccess e idx info span => .fieldAccess (e.mapInfo f) idx (f info) span
  | .global name info span => .global name (f info) span
  | .panic msg info span => .panic msg (f info) span

/-- Map a function over the annotation type of an expression list -/
partial def Soma.Metal.ExprList.mapInfo (f : α → β) : Soma.Metal.ExprList α scope → Soma.Metal.ExprList β scope
  | .nil => .nil
  | .cons e es => .cons (e.mapInfo f) (es.mapInfo f)

/-- Map a function over the annotation type of a case arm -/
partial def Soma.Metal.Arm.mapInfo (f : α → β) : Soma.Metal.Arm α scope → Soma.Metal.Arm β scope
  | .mk pats body span =>
      let pats' := pats.mapInfo f
      let body' := Soma.Metal.Expr.mapInfo f body
      let h : pats'.bindingIds ++ scope = pats.bindingIds ++ scope := by
        rw [Soma.Metal.PatternList.mapInfo_bindingIds]
      .mk pats' (h ▸ body') span

/-- Map a function over the annotation type of an arm list -/
partial def Soma.Metal.ArmList.mapInfo (f : α → β) : Soma.Metal.ArmList α scope → Soma.Metal.ArmList β scope
  | .nil => .nil
  | .cons a as => .cons (a.mapInfo f) (as.mapInfo f)

/-- Map a function over the annotation type of a capture list -/
partial def Soma.Metal.CaptureList.mapInfo (f : α → β) : Soma.Metal.CaptureList α scope → Soma.Metal.CaptureList β scope
  | .nil => .nil
  | .cons v info rest => .cons v (f info) (rest.mapInfo f)

end

namespace Soma.Metal

/-! ## List utilities -/

namespace ExprList

def toList : ExprList α scope → List (Expr α scope)
  | .nil => []
  | .cons e es => e :: es.toList

def fromList : List (Expr α scope) → ExprList α scope
  | [] => .nil
  | e :: es => .cons e (fromList es)

def length : ExprList α scope → Nat
  | .nil => 0
  | .cons _ es => 1 + es.length

def isEmpty : ExprList α scope → Bool
  | .nil => true
  | .cons _ _ => false

end ExprList

namespace CaptureList

def toList : CaptureList α scope → List (ScopedVar scope × α)
  | .nil => []
  | .cons v i cs => (v, i) :: cs.toList

def fromList : List (ScopedVar scope × α) → CaptureList α scope
  | [] => .nil
  | (v, i) :: cs => .cons v i (fromList cs)

def length : CaptureList α scope → Nat
  | .nil => 0
  | .cons _ _ cs => 1 + cs.length

end CaptureList

namespace ArmList

def toList : ArmList α scope → List (Arm α scope)
  | .nil => []
  | .cons a as => a :: as.toList

def fromList : List (Arm α scope) → ArmList α scope
  | [] => .nil
  | a :: as => .cons a (fromList as)

def length : ArmList α scope → Nat
  | .nil => 0
  | .cons _ as => 1 + as.length

end ArmList

/-! ## Type aliases -/

/-- Untyped expressions (before type checking) -/
abbrev UntypedExpr (scope : Scope) := Expr Unit scope

/-- Typed expressions (after type checking) -/
abbrev TypedExpr (scope : Scope) := Expr MonoTy scope

/-- A closed expression has no free variables -/
abbrev ClosedExpr α := Expr α []

/-- Closed untyped expression -/
abbrev ClosedUntypedExpr := ClosedExpr Unit

/-- Closed typed expression -/
abbrev ClosedTypedExpr := ClosedExpr MonoTy

namespace Expr

/-- Get the span of an expression -/
def span : Expr α scope → Span
  | .var _ _ s => s
  | .lit _ s => s
  | .call _ _ _ s => s
  | .let_ _ _ _ _ _ s => s
  | .lam _ _ _ s => s
  | .closure _ _ _ s => s
  | .construct _ _ _ _ s => s
  | .tuple _ _ s => s
  | .array _ _ s => s
  | .if_ _ _ _ _ s => s
  | .case _ _ _ s => s
  | .fieldAccess _ _ _ s => s
  | .global _ _ s => s
  | .panic _ _ s => s

/-- Get the type info from an expression (if it carries one) -/
def getInfo : Expr α scope → Option α
  | .var _ i _ => some i
  | .lit _ _ => none
  | .call _ _ i _ => some i
  | .let_ _ _ _ _ i _ => some i
  | .lam _ _ i _ => some i
  | .closure _ _ i _ => some i
  | .construct _ _ _ i _ => some i
  | .tuple _ i _ => some i
  | .array _ i _ => some i
  | .if_ _ _ _ i _ => some i
  | .case _ _ i _ => some i
  | .fieldAccess _ _ i _ => some i
  | .global _ i _ => some i
  | .panic _ i _ => some i

end Expr

/-- Get the type of a typed expression -/
def TypedExpr.type (e : TypedExpr scope) : Option MonoTy := e.getInfo

end Soma.Metal
