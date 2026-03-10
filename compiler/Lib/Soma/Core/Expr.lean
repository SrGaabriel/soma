import Soma.Unique
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Primitive
import Soma.Unique
import Soma.Core.MetaId
import Soma.Core.Literal
import Kenosis

namespace Soma.Core

open Soma (Unique)
open Soma.Core (Literal)
open Kenosis

/-- Qualified name for global constants -/
structure QualifiedName where
  id : Unique
  deriving Repr, Inhabited, Serialize, Deserialize

namespace QualifiedName

instance : BEq QualifiedName where
  beq q1 q2 := q1.id == q2.id

instance : Hashable QualifiedName where
  hash q := hash q.id

def display (qn : QualifiedName) : String := qn.id.display
def qualifiedDisplay (qn : QualifiedName) : String := qn.id.qualifiedDisplay
def mangle (qn : QualifiedName) : String := qn.id.mangle
def symbolName (qn : QualifiedName) : String := qn.id.symbolName
def module (qn : QualifiedName) : String := qn.id.module

instance : ToString QualifiedName := ⟨QualifiedName.display⟩

def ofUnique (u : Unique) : QualifiedName := ⟨u⟩

end QualifiedName

/-- Binder information for the core expression type -/
inductive BinderInfo where
  | explicit
  | implicit
  | instance_
  | strictImplicit
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Serialize, Deserialize

namespace BinderInfo

instance : ToString BinderInfo where
  toString
    | .explicit => "explicit"
    | .implicit => "implicit"
    | .instance_ => "instance"
    | .strictImplicit => "strictImplicit"

def isImplicit : BinderInfo → Bool
  | .explicit => false
  | _ => true

end BinderInfo

/-- Patterns for case expressions in the core IR -/
inductive Pattern where
  | var (name : Option Unique)
  | ctor (name : QualifiedName) (tag : Nat) (fields : Array Pattern)
  | lit (l : Literal)
  | wildcard
  /-- Variant pattern: match on a row-polymorphic variant label -/
  | inject (label : String) (arg : Option Pattern)

instance : Inhabited Pattern := ⟨.wildcard⟩
instance : Nonempty Pattern := ⟨.wildcard⟩
deriving instance Serialize, Deserialize for Pattern

namespace Pattern

partial def bindingCount : Pattern → Nat
  | .var (some _) => 1
  | .var none => 0
  | .ctor _ _ fields => fields.foldl (fun acc p => acc + p.bindingCount) 0
  | .lit _ => 0
  | .wildcard => 0
  | .inject _ (some p) => p.bindingCount
  | .inject _ none => 0

end Pattern

mutual

/-- Core expression type with locally nameless binding -/
inductive Expr where
  -- Variables (locally nameless)
  | bvar (idx : Nat)
  | fvar (id : Unique) (ty : Expr)
  | mvar (id : MetaId)
  | const (name : QualifiedName) (ty : Expr)

  -- Core lambda calculus
  | app (fn : Expr) (arg : Expr)
  | lam (info : BinderInfo) (name : String) (domain : Expr) (body : Expr)
  | let_ (name : String) (ty : Expr) (val : Expr) (body : Expr)
  | lit (l : Literal)

  -- Type constructs (types are terms)
  | sort (level : Level)
  | pi (qty : Quantity) (info : BinderInfo) (name : String)
       (domain : Expr) (codomain : Expr)
  | sigma (qty : Quantity) (info : BinderInfo) (name : String)
          (fst : Expr) (snd : Expr)

  -- Pairs (values of Sigma types)
  | pair (fst : Expr) (snd : Expr)
  | projFst (e : Expr)
  | projSnd (e : Expr)

  -- Data types and constructors
  | construct (name : QualifiedName) (tag : Nat) (args : Array Expr) (resultTy : Expr)
  | «case» (scrutinees : Array Expr) (arms : Array Arm) (resultTy : Expr)

  -- Records and variants (row polymorphism)
  | record (fields : Array (String × Expr))
  | recordUpdate (base : Expr) (updates : Array (String × Expr))
  | fieldAccess (e : Expr) (field : String) (idx : Nat)
  | inject (label : String) (args : Array Expr) (resultTy : Expr)

  -- Primitive types as expressions
  | primTy (p : PrimType)
  | rowSort
  | labelSort
  | rowEmpty
  | rowExtend (label : Expr) (fieldTy : Expr) (tail : Expr)
  | recordTy (row : Expr)
  | variantTy (row : Expr)
  | labelLit (name : String)
  | dataTy (id : Unique) (params : Array Expr)

  -- Equality types
  | eqTy (tyLevel : Level) (ty : Expr) (lhs : Expr) (rhs : Expr)
  | refl (ty : Expr) (x : Expr)
  | transport (tyLevel : Level) (ty : Expr) (motive : Expr)
              (lhs : Expr) (rhs : Expr) (eqProof : Expr) (body : Expr)

  -- Control flow
  | if_ (cond : Expr) (then_ : Expr) (else_ : Expr)
  | panic (msg : String)

  -- Post lambda-lift
  | closure (name : QualifiedName) (captures : Array Expr)

  -- Arrays and tuples
  | array (elements : Array Expr) (resultTy : Expr)
  | tuple (elements : Array Expr)

  -- Projection function (first-class field accessor)
  | proj (typeName : QualifiedName) (field : String) (idx : Nat)

  -- Annotation (transparent wrapper, for type checking output)
  | ann (expr : Expr) (ty : Expr)

/-- Case arm: patterns + body -/
inductive Arm where
  | mk (patterns : Array Pattern) (body : Expr)

end

namespace Arm
def patterns : Arm → Array Pattern
  | .mk ps _ => ps
def body : Arm → Expr
  | .mk _ b => b
end Arm

instance : Inhabited Expr := ⟨.sort Level.zero⟩
instance : Inhabited Arm := ⟨.mk #[] default⟩

/-- Short constructor name for diagnostic messages -/
def Expr.ctorName : Expr → String
  | .bvar _ => "bvar" | .fvar _ _ => "fvar" | .mvar _ => "mvar" | .const _ _ => "const"
  | .app _ _ => "app" | .lam _ _ _ _ => "lam" | .let_ _ _ _ _ => "let" | .lit _ => "lit"
  | .sort _ => "sort" | .pi _ _ _ _ _ => "pi" | .sigma _ _ _ _ _ => "sigma"
  | .pair _ _ => "pair" | .projFst _ => "projFst" | .projSnd _ => "projSnd"
  | .construct _ _ _ _ => "construct" | .case _ _ _ => "case"
  | .record _ => "record" | .recordUpdate _ _ => "recordUpdate"
  | .fieldAccess _ _ _ => "fieldAccess" | .inject _ _ _ => "inject"
  | .primTy _ => "primTy" | .rowSort => "rowSort" | .labelSort => "labelSort"
  | .rowEmpty => "rowEmpty" | .rowExtend _ _ _ => "rowExtend"
  | .recordTy _ => "recordTy" | .variantTy _ => "variantTy"
  | .labelLit _ => "labelLit" | .dataTy _ _ => "dataTy"
  | .eqTy _ _ _ _ => "eqTy" | .refl _ _ => "refl" | .transport _ _ _ _ _ _ _ => "transport"
  | .if_ _ _ _ => "if" | .panic _ => "panic"
  | .closure _ _ => "closure" | .array _ _ => "array" | .tuple _ => "tuple"
  | .proj _ _ _ => "proj" | .ann _ _ => "ann"

deriving instance Serialize, Deserialize for Expr
deriving instance Serialize, Deserialize for Arm

private def patternsBindingCount (ps : Array Pattern) : Nat :=
  ps.foldl (fun acc p => acc + p.bindingCount) 0

private def mapArmBodies (arms : Array Arm) (f : Expr → Nat → Expr) (baseDepth : Nat) : Array Arm :=
  arms.map fun arm =>
    let binds := patternsBindingCount arm.patterns
    Arm.mk arm.patterns (f arm.body (baseDepth + binds))

private def mapArmBodiesSimple (arms : Array Arm) (f : Expr → Expr) : Array Arm :=
  arms.map fun arm => Arm.mk arm.patterns (f arm.body)

namespace Expr

/-- Shift all BVars at or above `cutoff` by `amount` -/
partial def shift (e : Expr) (amount : Int) (cutoff : Nat) : Expr :=
  match e with
  | .bvar i =>
    if i >= cutoff then .bvar (Int.ofNat i + amount).toNat
    else e
  | .fvar id ty => .fvar id (ty.shift amount cutoff)
  | .const name ty => .const name (ty.shift amount cutoff)
  | .mvar _ | .sort _ | .primTy _ | .rowSort
  | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
  | .lit _ => e
  | .app f a => .app (f.shift amount cutoff) (a.shift amount cutoff)
  | .lam info n d b =>
    .lam info n (d.shift amount cutoff) (b.shift amount (cutoff + 1))
  | .let_ n t v b =>
    .let_ n (t.shift amount cutoff) (v.shift amount cutoff) (b.shift amount (cutoff + 1))
  | .pi q info n d c =>
    .pi q info n (d.shift amount cutoff) (c.shift amount (cutoff + 1))
  | .sigma q info n f s =>
    .sigma q info n (f.shift amount cutoff) (s.shift amount (cutoff + 1))
  | .pair f s => .pair (f.shift amount cutoff) (s.shift amount cutoff)
  | .projFst x => .projFst (x.shift amount cutoff)
  | .projSnd x => .projSnd (x.shift amount cutoff)
  | .construct n t args rty =>
    .construct n t (args.map (·.shift amount cutoff)) (rty.shift amount cutoff)
  | .«case» scruts arms rty =>
    .«case» (scruts.map (·.shift amount cutoff))
      (mapArmBodies arms (fun b d => b.shift amount d) cutoff)
      (rty.shift amount cutoff)
  | .record fields =>
    .record (fields.map fun (n, e) => (n, e.shift amount cutoff))
  | .recordUpdate b us =>
    .recordUpdate (b.shift amount cutoff)
      (us.map fun (n, e) => (n, e.shift amount cutoff))
  | .fieldAccess x f i => .fieldAccess (x.shift amount cutoff) f i
  | .inject l args rty => .inject l (args.map (·.shift amount cutoff)) (rty.shift amount cutoff)
  | .if_ c t el =>
    .if_ (c.shift amount cutoff) (t.shift amount cutoff) (el.shift amount cutoff)
  | .closure n caps => .closure n (caps.map (·.shift amount cutoff))
  | .array es ety => .array (es.map (·.shift amount cutoff)) (ety.shift amount cutoff)
  | .tuple es => .tuple (es.map (·.shift amount cutoff))
  | .rowExtend l f t =>
    .rowExtend (l.shift amount cutoff) (f.shift amount cutoff) (t.shift amount cutoff)
  | .recordTy r => .recordTy (r.shift amount cutoff)
  | .variantTy r => .variantTy (r.shift amount cutoff)
  | .dataTy id ps => .dataTy id (ps.map (·.shift amount cutoff))
  | .eqTy lv t l r =>
    .eqTy lv (t.shift amount cutoff) (l.shift amount cutoff) (r.shift amount cutoff)
  | .refl t x => .refl (t.shift amount cutoff) (x.shift amount cutoff)
  | .transport lv t m l r ep b =>
    .transport lv (t.shift amount cutoff) (m.shift amount cutoff)
               (l.shift amount cutoff) (r.shift amount cutoff)
               (ep.shift amount cutoff) (b.shift amount cutoff)
  | .ann x t => .ann (x.shift amount cutoff) (t.shift amount cutoff)

def shiftUp (e : Expr) (n : Nat := 1) : Expr :=
  e.shift (Int.ofNat n) 0

/-- Close over a free variable: FVar(fvar) → BVar(depth) -/
partial def abstractFVar (e : Expr) (fvar : Unique) : Expr :=
  go e 0
where
  go (e : Expr) (depth : Nat) : Expr :=
    match e with
    | .fvar u ty => if u == fvar then .bvar depth else .fvar u (go ty depth)
    | .bvar i => if i >= depth then .bvar (i + 1) else e
    | .const name ty => .const name (go ty depth)
    | .mvar _ | .sort _ | .primTy _ | .rowSort | .labelSort
    | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ | .lit _ => e
    | .app f a => .app (go f depth) (go a depth)
    | .lam info n d b => .lam info n (go d depth) (go b (depth + 1))
    | .let_ n t v b => .let_ n (go t depth) (go v depth) (go b (depth + 1))
    | .pi q info n d c => .pi q info n (go d depth) (go c (depth + 1))
    | .sigma q info n f s => .sigma q info n (go f depth) (go s (depth + 1))
    | .pair f s => .pair (go f depth) (go s depth)
    | .projFst x => .projFst (go x depth)
    | .projSnd x => .projSnd (go x depth)
    | .construct n t args rty => .construct n t (args.map (go · depth)) (go rty depth)
    | .«case» scruts arms rty =>
      .«case» (scruts.map (go · depth))
        (mapArmBodies arms (fun b d => go b d) depth)
        (go rty depth)
    | .record fields => .record (fields.map fun (n, e) => (n, go e depth))
    | .recordUpdate b us =>
      .recordUpdate (go b depth) (us.map fun (n, e) => (n, go e depth))
    | .fieldAccess x f i => .fieldAccess (go x depth) f i
    | .inject l args rty => .inject l (args.map (go · depth)) (go rty depth)
    | .if_ c t el => .if_ (go c depth) (go t depth) (go el depth)
    | .closure n caps => .closure n (caps.map (go · depth))
    | .array es ety => .array (es.map (go · depth)) (go ety depth)
    | .tuple es => .tuple (es.map (go · depth))
    | .rowExtend l f t => .rowExtend (go l depth) (go f depth) (go t depth)
    | .recordTy r => .recordTy (go r depth)
    | .variantTy r => .variantTy (go r depth)
    | .dataTy id ps => .dataTy id (ps.map (go · depth))
    | .eqTy lv t l r => .eqTy lv (go t depth) (go l depth) (go r depth)
    | .refl t x => .refl (go t depth) (go x depth)
    | .transport lv t m l r ep b =>
      .transport lv (go t depth) (go m depth) (go l depth)
                 (go r depth) (go ep depth) (go b depth)
    | .ann x t => .ann (go x depth) (go t depth)

/-- Open a binder: replace BVar(depth) with replacement -/
partial def instantiate (e : Expr) (replacement : Expr) : Expr :=
  go e 0
where
  go (e : Expr) (depth : Nat) : Expr :=
    match e with
    | .bvar i =>
      if i == depth then replacement.shift (Int.ofNat depth) 0
      else if i > depth then .bvar (i - 1)
      else e
    | .fvar id ty => .fvar id (go ty depth)
    | .const name ty => .const name (go ty depth)
    | .mvar _ | .sort _ | .primTy _ | .rowSort
    | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
    | .lit _ => e
    | .app f a => .app (go f depth) (go a depth)
    | .lam info n d b => .lam info n (go d depth) (go b (depth + 1))
    | .let_ n t v b => .let_ n (go t depth) (go v depth) (go b (depth + 1))
    | .pi q info n d c => .pi q info n (go d depth) (go c (depth + 1))
    | .sigma q info n f s => .sigma q info n (go f depth) (go s (depth + 1))
    | .pair f s => .pair (go f depth) (go s depth)
    | .projFst x => .projFst (go x depth)
    | .projSnd x => .projSnd (go x depth)
    | .construct n t args rty => .construct n t (args.map (go · depth)) (go rty depth)
    | .«case» scruts arms rty =>
      .«case» (scruts.map (go · depth))
        (mapArmBodies arms (fun b d => go b d) depth)
        (go rty depth)
    | .record fields => .record (fields.map fun (n, e) => (n, go e depth))
    | .recordUpdate b us =>
      .recordUpdate (go b depth) (us.map fun (n, e) => (n, go e depth))
    | .fieldAccess x f i => .fieldAccess (go x depth) f i
    | .inject l args rty => .inject l (args.map (go · depth)) (go rty depth)
    | .if_ c t el => .if_ (go c depth) (go t depth) (go el depth)
    | .closure n caps => .closure n (caps.map (go · depth))
    | .array es ety => .array (es.map (go · depth)) (go ety depth)
    | .tuple es => .tuple (es.map (go · depth))
    | .rowExtend l f t => .rowExtend (go l depth) (go f depth) (go t depth)
    | .recordTy r => .recordTy (go r depth)
    | .variantTy r => .variantTy (go r depth)
    | .dataTy id ps => .dataTy id (ps.map (go · depth))
    | .eqTy lv t l r => .eqTy lv (go t depth) (go l depth) (go r depth)
    | .refl t x => .refl (go t depth) (go x depth)
    | .transport lv t m l r ep b =>
      .transport lv (go t depth) (go m depth) (go l depth)
                 (go r depth) (go ep depth) (go b depth)
    | .ann x t => .ann (go x depth) (go t depth)

/-- Replace all occurrences of FVar(fvar) with replacement -/
partial def replaceFVar (e : Expr) (fvar : Unique) (replacement : Expr) : Expr :=
  match e with
  | .fvar u ty => if u == fvar then replacement else .fvar u (ty.replaceFVar fvar replacement)
  | .const name ty => .const name (ty.replaceFVar fvar replacement)
  | .bvar _ | .mvar _ | .sort _ | .primTy _ | .rowSort
  | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
  | .lit _ => e
  | .app f a =>
    .app (f.replaceFVar fvar replacement) (a.replaceFVar fvar replacement)
  | .lam info n d b =>
    .lam info n (d.replaceFVar fvar replacement) (b.replaceFVar fvar replacement)
  | .let_ n t v b =>
    .let_ n (t.replaceFVar fvar replacement) (v.replaceFVar fvar replacement)
           (b.replaceFVar fvar replacement)
  | .pi q info n d c =>
    .pi q info n (d.replaceFVar fvar replacement) (c.replaceFVar fvar replacement)
  | .sigma q info n f s =>
    .sigma q info n (f.replaceFVar fvar replacement) (s.replaceFVar fvar replacement)
  | .pair f s =>
    .pair (f.replaceFVar fvar replacement) (s.replaceFVar fvar replacement)
  | .projFst x => .projFst (x.replaceFVar fvar replacement)
  | .projSnd x => .projSnd (x.replaceFVar fvar replacement)
  | .construct n t args rty =>
    .construct n t (args.map (·.replaceFVar fvar replacement)) (rty.replaceFVar fvar replacement)
  | .«case» scruts arms rty =>
    .«case» (scruts.map (·.replaceFVar fvar replacement))
      (mapArmBodiesSimple arms (·.replaceFVar fvar replacement))
      (rty.replaceFVar fvar replacement)
  | .record fields =>
    .record (fields.map fun (n, e) => (n, e.replaceFVar fvar replacement))
  | .recordUpdate b us =>
    .recordUpdate (b.replaceFVar fvar replacement)
      (us.map fun (n, e) => (n, e.replaceFVar fvar replacement))
  | .fieldAccess x f i => .fieldAccess (x.replaceFVar fvar replacement) f i
  | .inject l args rty => .inject l (args.map (·.replaceFVar fvar replacement)) (rty.replaceFVar fvar replacement)
  | .if_ c t el =>
    .if_ (c.replaceFVar fvar replacement)
         (t.replaceFVar fvar replacement) (el.replaceFVar fvar replacement)
  | .closure n caps => .closure n (caps.map (·.replaceFVar fvar replacement))
  | .array es ety => .array (es.map (·.replaceFVar fvar replacement)) (ety.replaceFVar fvar replacement)
  | .tuple es => .tuple (es.map (·.replaceFVar fvar replacement))
  | .rowExtend l f t =>
    .rowExtend (l.replaceFVar fvar replacement) (f.replaceFVar fvar replacement)
               (t.replaceFVar fvar replacement)
  | .recordTy r => .recordTy (r.replaceFVar fvar replacement)
  | .variantTy r => .variantTy (r.replaceFVar fvar replacement)
  | .dataTy id ps => .dataTy id (ps.map (·.replaceFVar fvar replacement))
  | .eqTy lv t l r =>
    .eqTy lv (t.replaceFVar fvar replacement) (l.replaceFVar fvar replacement)
             (r.replaceFVar fvar replacement)
  | .refl t x =>
    .refl (t.replaceFVar fvar replacement) (x.replaceFVar fvar replacement)
  | .transport lv t m l r ep b =>
    .transport lv (t.replaceFVar fvar replacement) (m.replaceFVar fvar replacement)
               (l.replaceFVar fvar replacement) (r.replaceFVar fvar replacement)
               (ep.replaceFVar fvar replacement) (b.replaceFVar fvar replacement)
  | .ann x t =>
    .ann (x.replaceFVar fvar replacement) (t.replaceFVar fvar replacement)

/-- Collect all free variables (FVars) in an expression -/
partial def collectFVars (e : Expr) : Std.HashSet Unique :=
  go e {}
where
  go (e : Expr) (acc : Std.HashSet Unique) : Std.HashSet Unique :=
    match e with
    | .fvar u ty => go ty (acc.insert u)
    | .const _ ty => go ty acc
    | .bvar _ | .mvar _ | .sort _ | .primTy _ | .rowSort
    | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
    | .lit _ => acc
    | .app f a => go a (go f acc)
    | .lam _ _ d b => go b (go d acc)
    | .let_ _ t v b => go b (go v (go t acc))
    | .pi _ _ _ d c => go c (go d acc)
    | .sigma _ _ _ f s => go s (go f acc)
    | .pair f s => go s (go f acc)
    | .projFst x => go x acc
    | .projSnd x => go x acc
    | .construct _ _ args rty => go rty (args.foldl (fun a e => go e a) acc)
    | .«case» scruts arms rty =>
      let acc := scruts.foldl (fun a e => go e a) acc
      let acc := arms.foldl (fun a arm => go arm.body a) acc
      go rty acc
    | .record fields => fields.foldl (fun a (_, e) => go e a) acc
    | .recordUpdate b us =>
      let acc := go b acc
      us.foldl (fun a (_, e) => go e a) acc
    | .fieldAccess x _ _ => go x acc
    | .inject _ args rty => go rty (args.foldl (fun a e => go e a) acc)
    | .if_ c t el => go el (go t (go c acc))
    | .closure _ caps => caps.foldl (fun a e => go e a) acc
    | .array es ety => go ety (es.foldl (fun a e => go e a) acc)
    | .tuple es => es.foldl (fun a e => go e a) acc
    | .rowExtend l f t => go t (go f (go l acc))
    | .recordTy r => go r acc
    | .variantTy r => go r acc
    | .dataTy _ ps => ps.foldl (fun a e => go e a) acc
    | .eqTy _ t l r => go r (go l (go t acc))
    | .refl t x => go x (go t acc)
    | .transport _ t m l r ep b =>
      go b (go ep (go r (go l (go m (go t acc)))))
    | .ann x t => go t (go x acc)

/-- Check if an expression contains a specific free variable -/
partial def hasFVar (e : Expr) (fvar : Unique) : Bool :=
  match e with
  | .fvar u ty => u == fvar || ty.hasFVar fvar
  | .const _ ty => ty.hasFVar fvar
  | .bvar _ | .mvar _ | .sort _ | .primTy _ | .rowSort
  | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
  | .lit _ => false
  | .app f a => f.hasFVar fvar || a.hasFVar fvar
  | .lam _ _ d b => d.hasFVar fvar || b.hasFVar fvar
  | .let_ _ t v b => t.hasFVar fvar || v.hasFVar fvar || b.hasFVar fvar
  | .pi _ _ _ d c => d.hasFVar fvar || c.hasFVar fvar
  | .sigma _ _ _ f s => f.hasFVar fvar || s.hasFVar fvar
  | .pair f s => f.hasFVar fvar || s.hasFVar fvar
  | .projFst x => x.hasFVar fvar
  | .projSnd x => x.hasFVar fvar
  | .construct _ _ args rty => args.any (·.hasFVar fvar) || rty.hasFVar fvar
  | .«case» scruts arms rty =>
    scruts.any (·.hasFVar fvar) || arms.any (fun arm => arm.body.hasFVar fvar) || rty.hasFVar fvar
  | .record fields => fields.any (fun p => p.2.hasFVar fvar)
  | .recordUpdate b us =>
    b.hasFVar fvar || us.any (fun p => p.2.hasFVar fvar)
  | .fieldAccess x _ _ => x.hasFVar fvar
  | .inject _ args rty => args.any (·.hasFVar fvar) || rty.hasFVar fvar
  | .if_ c t el => c.hasFVar fvar || t.hasFVar fvar || el.hasFVar fvar
  | .closure _ caps => caps.any (·.hasFVar fvar)
  | .array es ety => es.any (·.hasFVar fvar) || ety.hasFVar fvar
  | .tuple es => es.any (·.hasFVar fvar)
  | .rowExtend l f t => l.hasFVar fvar || f.hasFVar fvar || t.hasFVar fvar
  | .recordTy r => r.hasFVar fvar
  | .variantTy r => r.hasFVar fvar
  | .dataTy _ ps => ps.any (·.hasFVar fvar)
  | .eqTy _ t l r => t.hasFVar fvar || l.hasFVar fvar || r.hasFVar fvar
  | .refl t x => t.hasFVar fvar || x.hasFVar fvar
  | .transport _ t m l r ep b =>
    t.hasFVar fvar || m.hasFVar fvar || l.hasFVar fvar ||
    r.hasFVar fvar || ep.hasFVar fvar || b.hasFVar fvar
  | .ann x t => x.hasFVar fvar || t.hasFVar fvar

/-- Count the number of occurrences of a specific free variable in an expression -/
partial def countFVar (e : Expr) (fvar : Unique) : Nat :=
  match e with
  | .fvar u ty => (if u == fvar then 1 else 0) + ty.countFVar fvar
  | .const _ ty => ty.countFVar fvar
  | .bvar _ | .mvar _ | .sort _ | .primTy _ | .rowSort
  | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
  | .lit _ => 0
  | .app f a => f.countFVar fvar + a.countFVar fvar
  | .lam _ _ d b => d.countFVar fvar + b.countFVar fvar
  | .let_ _ t v b => t.countFVar fvar + v.countFVar fvar + b.countFVar fvar
  | .pi _ _ _ d c => d.countFVar fvar + c.countFVar fvar
  | .sigma _ _ _ f s => f.countFVar fvar + s.countFVar fvar
  | .pair f s => f.countFVar fvar + s.countFVar fvar
  | .projFst x => x.countFVar fvar
  | .projSnd x => x.countFVar fvar
  | .construct _ _ args rty => args.foldl (fun acc a => acc + a.countFVar fvar) 0 + rty.countFVar fvar
  | .«case» scruts arms rty =>
    let scrutCount := scruts.foldl (fun acc s => acc + s.countFVar fvar) 0
    let armSum := arms.foldl (fun acc arm => acc + arm.body.countFVar fvar) 0
    scrutCount + armSum + rty.countFVar fvar
  | .record fields => fields.foldl (fun acc (_, e) => acc + e.countFVar fvar) 0
  | .recordUpdate b us =>
    b.countFVar fvar + us.foldl (fun acc (_, e) => acc + e.countFVar fvar) 0
  | .fieldAccess x _ _ => x.countFVar fvar
  | .inject _ args rty => args.foldl (fun acc a => acc + a.countFVar fvar) 0 + rty.countFVar fvar
  | .if_ c t el =>
    c.countFVar fvar + t.countFVar fvar + el.countFVar fvar
  | .closure _ caps => caps.foldl (fun acc e => acc + e.countFVar fvar) 0
  | .array es ety => es.foldl (fun acc e => acc + e.countFVar fvar) 0 + ety.countFVar fvar
  | .tuple es => es.foldl (fun acc e => acc + e.countFVar fvar) 0
  | .rowExtend l f t => l.countFVar fvar + f.countFVar fvar + t.countFVar fvar
  | .recordTy r => r.countFVar fvar
  | .variantTy r => r.countFVar fvar
  | .dataTy _ ps => ps.foldl (fun acc p => acc + p.countFVar fvar) 0
  | .eqTy _ t l r => t.countFVar fvar + l.countFVar fvar + r.countFVar fvar
  | .refl t x => t.countFVar fvar + x.countFVar fvar
  | .transport _ t m l r ep b =>
    t.countFVar fvar + m.countFVar fvar + l.countFVar fvar +
    r.countFVar fvar + ep.countFVar fvar + b.countFVar fvar
  | .ann x t => x.countFVar fvar + t.countFVar fvar

end Expr

end Soma.Core
