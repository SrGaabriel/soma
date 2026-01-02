import Soma.Metal.Name
import Soma.Metal.Scope
import Soma.Metal.Literal
import Soma.Metal.Pattern
import Soma.Syntax.Source
import Soma.Syntax.Ast
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Primitive
import Soma.Core.TypeId

open Soma.Metal
open Soma.Syntax (Span)
open Soma.Core (Quantity Level LevelVarId StarPrimitive HigherPrimitive TypeId)

/-- Argument to an explicit type application in Metal IR -/
inductive Soma.Metal.TypeArg where
  /-- A type expression (to be elaborated during type checking) -/
  | type (ty : Soma.Syntax.TypeExpr)
  /-- A label literal for label polymorphism -/
  | label (name : String)
  deriving Inhabited

/-- Binder information: how a variable is bound -/
inductive Soma.Metal.BinderInfo where
  /-- Explicit argument: f x -/
  | explicit
  /-- Implicit argument: f {x} -/
  | implicit
  /-- Instance argument: f [x] or f {{x}} -/
  | instance_
  /-- Strict implicit: f ⦃x⦄ -/
  | strictImplicit
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace Soma.Metal.BinderInfo

instance : ToString BinderInfo where
  toString
    | .explicit => "explicit"
    | .implicit => "implicit"
    | .instance_ => "instance"
    | .strictImplicit => "strictImplicit"

/-- Check if binder is implicit (any kind) -/
def isImplicit : BinderInfo → Bool
  | .explicit => false
  | _ => true

end Soma.Metal.BinderInfo

/-- Hole identifier for user-written holes -/
structure Soma.Metal.HoleId where
  id : Nat
  name : Option String := none
  deriving Repr, BEq, Hashable, Inhabited

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

  /-- Record literal { x = 1, y = 2 } -/
  | record (fields : Soma.Metal.RecordFieldList α scope) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Record update { base | x = 1, y = 2 } -/
  | recordUpdate (base : Soma.Metal.Expr α scope) (updates : Soma.Metal.RecordFieldList α scope) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Variant injection .label args (empty for nullary, singleton for unary, extends to multi-field) -/
  | inject (label : String) (args : Soma.Metal.ExprList α scope) (info : α) (span : Span)
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

  /-- Field access (for structs/records) -/
  | fieldAccess (expr : Soma.Metal.Expr α scope) (fieldName : String) (fieldIndex : Nat) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Global reference (top-level function or value) -/
  | global (name : Name) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Panic (abort with message) -/
  | panic (message : String) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- First-class projection function for nominal record types -/
  | proj (typeName : Name) (fieldName : String) (fieldIndex : Nat) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Explicit type application: @Type or @label (todo: maybe merge) -/
  | typeApp (arg : Soma.Metal.TypeArg) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  -- Dependent Type Constructors

  /-- Universe type: Type_l -/
  | type (level : Level) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Dependent function type (Π-type): (q x : A) -> B
      - qty: quantity annotation (0 = erased, 1 = linear, ω = unrestricted)
      - binder: how the argument is passed (explicit, implicit, instance)
      - name: variable name (for pretty printing)
      - domain: the type A
      - codomain: the type B (may reference the bound variable)
  -/
  | pi (qty : Quantity) (binder : Soma.Metal.BinderInfo) (name : String)
       (domain : Soma.Metal.Expr α scope)
       (codomain : Soma.Metal.Expr α scope)
       (span : Span)
      : Soma.Metal.Expr α scope

  /-- Dependent pair type (Σ-type): (x : A) × B -/
  | sigma (qty : Quantity) (name : String)
          (fst : Soma.Metal.Expr α scope)
          (snd : Soma.Metal.Expr α scope)
          (span : Span)
      : Soma.Metal.Expr α scope

  /-- Dependent pair value -/
  | pair (fst : Soma.Metal.Expr α scope)
         (snd : Soma.Metal.Expr α scope)
         (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- First projection of a pair -/
  | fst (e : Soma.Metal.Expr α scope) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Second projection of a pair -/
  | snd (e : Soma.Metal.Expr α scope) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Primitive type as expression (Int, Bool, etc.) -/
  | primTy (p : StarPrimitive) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Higher-kinded primitive as expression (Array, IO, Ref) -/
  | higherPrimTy (p : HigherPrimitive) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Empty row type -/
  | rowEmpty (span : Span)
      : Soma.Metal.Expr α scope

  /-- Row extension: { label : fieldTy | tail } -/
  | rowExtend (label : Soma.Metal.Expr α scope)
              (fieldTy : Soma.Metal.Expr α scope)
              (tail : Soma.Metal.Expr α scope)
              (span : Span)
      : Soma.Metal.Expr α scope

  /-- Record type from row -/
  | recordTy (row : Soma.Metal.Expr α scope) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Variant type from row -/
  | variantTy (row : Soma.Metal.Expr α scope) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Label literal for label polymorphism -/
  | labelLit (name : String) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Data type applied to parameters (as a type expression) -/
  | dataTy (id : TypeId) (params : Soma.Metal.ExprList α scope) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Type annotation: (e : A) -/
  | ann (expr : Soma.Metal.Expr α scope)
        (ty : Soma.Metal.Expr α scope)
        (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- User-written hole: _ or ?name -/
  | hole (id : Soma.Metal.HoleId) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Metavariable (created during elaboration) -/
  | mvar (id : Nat) (info : α) (span : Span)
      : Soma.Metal.Expr α scope

  /-- Equality type: lhs = rhs : ty -/
  | eq (tyLevel : Level) (ty : Soma.Metal.Expr α scope)
       (lhs : Soma.Metal.Expr α scope)
       (rhs : Soma.Metal.Expr α scope)
       (span : Span)
      : Soma.Metal.Expr α scope

  /-- Reflexivity proof: refl : x = x -/
  | refl (ty : Soma.Metal.Expr α scope)
         (x : Soma.Metal.Expr α scope)
         (span : Span)
      : Soma.Metal.Expr α scope

  /-- Transport along an equality proof: transport P eq px : P y
      Given:
      - P : A -> Type (the motive/predicate)
      - eq : x = y (equality proof)
      - px : P x (value at x)
      Returns: P y (value transported to y)
  -/
  | transport (tyLevel : Level)
              (ty : Soma.Metal.Expr α scope)
              (motive : Soma.Metal.Expr α scope)
              (lhs : Soma.Metal.Expr α scope)
              (rhs : Soma.Metal.Expr α scope)
              (eq : Soma.Metal.Expr α scope)
              (body : Soma.Metal.Expr α scope)
              (span : Span)
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

/-- List of record fields (name-value pairs) -/
inductive Soma.Metal.RecordFieldList (α : Type) : Scope → Type where
  | nil : Soma.Metal.RecordFieldList α scope
  | cons : String → Soma.Metal.Expr α scope → Soma.Metal.RecordFieldList α scope → Soma.Metal.RecordFieldList α scope

end

-- Nonempty instances for partial function compilation
instance : Nonempty (Soma.Metal.CaptureList α scope) := ⟨.nil⟩
instance : Nonempty (Soma.Metal.ExprList α scope) := ⟨.nil⟩
instance : Nonempty (Soma.Metal.ArmList α scope) := ⟨.nil⟩
instance : Nonempty (Soma.Metal.RecordFieldList α scope) := ⟨.nil⟩
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
  | .record fields info span => .record (fields.mapInfo f) (f info) span
  | .recordUpdate base updates info span => .recordUpdate (base.mapInfo f) (updates.mapInfo f) (f info) span
  | .inject label args info span => .inject label (args.mapInfo f) (f info) span
  | .array elems info span => .array (elems.mapInfo f) (f info) span
  | .if_ c t e info span => .if_ (c.mapInfo f) (t.mapInfo f) (e.mapInfo f) (f info) span
  | .case scruts arms info span => .case (scruts.mapInfo f) (arms.mapInfo f) (f info) span
  | .fieldAccess e name idx info span => .fieldAccess (e.mapInfo f) name idx (f info) span
  | .global name info span => .global name (f info) span
  | .panic msg info span => .panic msg (f info) span
  | .proj typeName fieldName idx info span => .proj typeName fieldName idx (f info) span
  | .typeApp arg info span => .typeApp arg (f info) span
  -- Dependent type constructors
  | .type level span => .type level span
  | .pi qty binder name dom cod span => .pi qty binder name (dom.mapInfo f) (cod.mapInfo f) span
  | .sigma qty name fst snd span => .sigma qty name (fst.mapInfo f) (snd.mapInfo f) span
  | .pair fst snd info span => .pair (fst.mapInfo f) (snd.mapInfo f) (f info) span
  | .fst e info span => .fst (e.mapInfo f) (f info) span
  | .snd e info span => .snd (e.mapInfo f) (f info) span
  | .primTy p span => .primTy p span
  | .higherPrimTy p span => .higherPrimTy p span
  | .rowEmpty span => .rowEmpty span
  | .rowExtend label fieldTy tail span =>
      .rowExtend (label.mapInfo f) (fieldTy.mapInfo f) (tail.mapInfo f) span
  | .recordTy row span => .recordTy (row.mapInfo f) span
  | .variantTy row span => .variantTy (row.mapInfo f) span
  | .labelLit name span => .labelLit name span
  | .dataTy id params span => .dataTy id (params.mapInfo f) span
  | .ann expr ty info span => .ann (expr.mapInfo f) (ty.mapInfo f) (f info) span
  | .hole id span => .hole id span
  | .mvar id info span => .mvar id (f info) span
  | .eq tyLevel ty lhs rhs span => .eq tyLevel (ty.mapInfo f) (lhs.mapInfo f) (rhs.mapInfo f) span
  | .refl ty x span => .refl (ty.mapInfo f) (x.mapInfo f) span
  | .transport tyLevel ty motive lhs rhs eq body span =>
      .transport tyLevel (ty.mapInfo f) (motive.mapInfo f) (lhs.mapInfo f)
                 (rhs.mapInfo f) (eq.mapInfo f) (body.mapInfo f) span

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

/-- Map a function over the annotation type of a record field list -/
partial def Soma.Metal.RecordFieldList.mapInfo (f : α → β) : Soma.Metal.RecordFieldList α scope → Soma.Metal.RecordFieldList β scope
  | .nil => .nil
  | .cons name expr rest => .cons name (expr.mapInfo f) (rest.mapInfo f)

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

namespace RecordFieldList

def toList : RecordFieldList α scope → List (String × Expr α scope)
  | .nil => []
  | .cons name expr rest => (name, expr) :: rest.toList

def fromList : List (String × Expr α scope) → RecordFieldList α scope
  | [] => .nil
  | (name, expr) :: rest => .cons name expr (fromList rest)

def length : RecordFieldList α scope → Nat
  | .nil => 0
  | .cons _ _ rest => 1 + rest.length

end RecordFieldList

/-! ## Type aliases -/

/-- Untyped expressions (before type checking) -/
abbrev UntypedExpr (scope : Scope) := Expr Unit scope

/-- A closed expression has no free variables -/
abbrev ClosedExpr α := Expr α []

/-- Closed untyped expression -/
abbrev ClosedUntypedExpr := ClosedExpr Unit

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
  | .record _ _ s => s
  | .recordUpdate _ _ _ s => s
  | .inject _ _ _ s => s
  | .array _ _ s => s
  | .if_ _ _ _ _ s => s
  | .case _ _ _ s => s
  | .fieldAccess _ _ _ _ s => s
  | .global _ _ s => s
  | .panic _ _ s => s
  | .proj _ _ _ _ s => s
  | .typeApp _ _ s => s
  -- Dependent type constructors
  | .type _ s => s
  | .pi _ _ _ _ _ s => s
  | .sigma _ _ _ _ s => s
  | .pair _ _ _ s => s
  | .fst _ _ s => s
  | .snd _ _ s => s
  | .primTy _ s => s
  | .higherPrimTy _ s => s
  | .rowEmpty s => s
  | .rowExtend _ _ _ s => s
  | .recordTy _ s => s
  | .variantTy _ s => s
  | .labelLit _ s => s
  | .dataTy _ _ s => s
  | .ann _ _ _ s => s
  | .hole _ s => s
  | .mvar _ _ s => s
  | .eq _ _ _ _ s => s
  | .refl _ _ s => s
  | .transport _ _ _ _ _ _ _ s => s

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
  | .record _ i _ => some i
  | .recordUpdate _ _ i _ => some i
  | .inject _ _ i _ => some i
  | .array _ i _ => some i
  | .if_ _ _ _ i _ => some i
  | .case _ _ i _ => some i
  | .fieldAccess _ _ _ i _ => some i
  | .global _ i _ => some i
  | .panic _ i _ => some i
  | .proj _ _ _ i _ => some i
  | .typeApp _ i _ => some i
  -- Dependent type constructors
  | .type _ _ => none  -- Type literals don't carry runtime info
  | .pi _ _ _ _ _ _ => none  -- Pi types are type-level
  | .sigma _ _ _ _ _ => none  -- Sigma types are type-level
  | .pair _ _ i _ => some i
  | .fst _ i _ => some i
  | .snd _ i _ => some i
  | .primTy _ _ => none  -- Primitive types don't carry runtime info
  | .higherPrimTy _ _ => none
  | .rowEmpty _ => none
  | .rowExtend _ _ _ _ => none
  | .recordTy _ _ => none
  | .variantTy _ _ => none
  | .labelLit _ _ => none
  | .dataTy _ _ _ => none
  | .ann _ _ i _ => some i
  | .hole _ _ => none
  | .mvar _ i _ => some i
  | .eq _ _ _ _ _ => none  -- Equality types are type-level
  | .refl _ _ _ => none  -- Refl is a proof term
  | .transport _ _ _ _ _ _ _ _ => none  -- Transport is a proof term

end Expr

end Soma.Metal
