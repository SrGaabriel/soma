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

/-- Collect binding Unique IDs from a pattern in left-to-right depth-first order -/
partial def collectBindingIds : Pattern → Array Unique
  | .var (some u) => #[u]
  | .var none => #[]
  | .ctor _ _ fields => fields.foldl (fun acc p => acc ++ p.collectBindingIds) #[]
  | .lit _ => #[]
  | .wildcard => #[]
  | .inject _ (some p) => p.collectBindingIds
  | .inject _ none => #[]

end Pattern

mutual

/-- Core expression type with locally nameless binding -/
inductive Expr where
  -- Variables (locally nameless)
  | bvar (idx : Nat)
  | fvar (id : Unique) (ty : Expr)
  | mvar (id : MetaId)
  | const (name : QualifiedName) (ty : Expr)
  | tyvar (lvl : DeBruijnLvl) (name : String)

  -- Core lambda calculus
  | app (fn : Expr) (arg : Expr)
  | lam (info : BinderInfo) (name : String) (domain : Expr) (body : Expr)
  | let_ (name : String) (ty : Expr) (val : Expr) (body : Expr)
  | lit (l : Literal)

  -- Type constructs (types are terms)
  | sort (level : Level)
  | pi (qty : Quantity) (info : BinderInfo) (name : String)
       (domain : Expr) (codomain : Expr)

  -- Data types and constructors
  | construct (name : QualifiedName) (tag : Nat) (args : Array Expr) (resultTy : Expr)
  /-- Dependent case analysis -/
  | «case» (scrutinees : Array Expr) (motive : Expr) (arms : Array Arm)

  -- Records and variants (row polymorphism)
  | record (fields : Array (String × Expr))
  | recordUpdate (base : Expr) (updates : Array (String × Expr))
  | fieldAccess (e : Expr) (field : String) (idx : Nat)
  | inject (label : String) (args : Array Expr) (resultTy : Expr)

  -- Primitive types as expressions
  | rowSort
  | labelSort
  | rowEmpty
  | rowExtend (label : Expr) (fieldTy : Expr) (tail : Expr)
  | recordTy (row : Expr)
  | variantTy (row : Expr)
  | labelLit (name : String)
  | dataTy (id : Unique) (params : Array Expr)

  -- Control flow
  | if_ (cond : Expr) (then_ : Expr) (else_ : Expr)
  | panic (msg : String)

  -- Post lambda-lift
  | closure (name : QualifiedName) (captures : Array Expr) (ty : Expr)

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

/-- Replace all occurrences of a metavariable with a given expression -/
partial def Expr.replaceMvar (e : Expr) (metaId : MetaId) (replacement : Expr) : Expr :=
  match e with
  | .mvar mid => if mid == metaId then replacement else e
  | .app f a => .app (f.replaceMvar metaId replacement) (a.replaceMvar metaId replacement)
  | .lam info n d b => .lam info n (d.replaceMvar metaId replacement) (b.replaceMvar metaId replacement)
  | .let_ n ty v b => .let_ n (ty.replaceMvar metaId replacement) (v.replaceMvar metaId replacement) (b.replaceMvar metaId replacement)
  | .pi qty info n d c => .pi qty info n (d.replaceMvar metaId replacement) (c.replaceMvar metaId replacement)
  | .ann x t => .ann (x.replaceMvar metaId replacement) (t.replaceMvar metaId replacement)
  | .construct n t args rty =>
    .construct n t (args.map (·.replaceMvar metaId replacement)) (rty.replaceMvar metaId replacement)
  | .«case» scruts motive arms =>
    .«case» (scruts.map (·.replaceMvar metaId replacement))
      (motive.replaceMvar metaId replacement)
      (arms.map fun arm => Arm.mk arm.patterns (arm.body.replaceMvar metaId replacement))
  | .record fields =>
    .record (fields.map fun (n, x) => (n, x.replaceMvar metaId replacement))
  | .recordUpdate base updates =>
    .recordUpdate (base.replaceMvar metaId replacement)
      (updates.map fun (n, x) => (n, x.replaceMvar metaId replacement))
  | .fieldAccess x f i => .fieldAccess (x.replaceMvar metaId replacement) f i
  | .inject l args rty =>
    .inject l (args.map (·.replaceMvar metaId replacement)) (rty.replaceMvar metaId replacement)
  | .if_ c t el =>
    .if_ (c.replaceMvar metaId replacement) (t.replaceMvar metaId replacement) (el.replaceMvar metaId replacement)
  | .closure n caps ty =>
    .closure n (caps.map (·.replaceMvar metaId replacement)) (ty.replaceMvar metaId replacement)
  | .array es ety => .array (es.map (·.replaceMvar metaId replacement)) (ety.replaceMvar metaId replacement)
  | .tuple es => .tuple (es.map (·.replaceMvar metaId replacement))
  | .rowExtend l f t =>
    .rowExtend (l.replaceMvar metaId replacement) (f.replaceMvar metaId replacement) (t.replaceMvar metaId replacement)
  | .recordTy r => .recordTy (r.replaceMvar metaId replacement)
  | .variantTy r => .variantTy (r.replaceMvar metaId replacement)
  | .dataTy id ps => .dataTy id (ps.map (·.replaceMvar metaId replacement))
  | .fvar id ty => .fvar id (ty.replaceMvar metaId replacement)
  | .const n ty => .const n (ty.replaceMvar metaId replacement)
  | .bvar _ | .sort _ | .lit _ | .rowSort | .labelSort
  | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ | .tyvar _ _ => e

partial def Expr.containsPairExpr : Expr → Bool
  | .app f a => f.containsPairExpr || a.containsPairExpr
  | .lam _ _ _ b => b.containsPairExpr
  | .let_ _ _ v b => v.containsPairExpr || b.containsPairExpr
  | .«case» scruts _ arms => scruts.any (·.containsPairExpr) || arms.any (·.body.containsPairExpr)
  | .closure _ caps _ => caps.any (·.containsPairExpr)
  | _ => false

partial def Expr.toDebugString : Expr → String
  | .bvar i => s!"#{i}"
  | .fvar id _ => s!"&{id.original}"
  | .mvar i => s!"?{i.id}"
  | .const name _ => s!"@{name.display}"
  | .tyvar _ name => s!"τ{name}"
  | .app f a => s!"({f.toDebugString} {a.toDebugString})"
  | .lam _ name _ b => s!"(λ{name}. {b.toDebugString})"
  | .let_ name _ v b => s!"(let {name} := {v.toDebugString} in {b.toDebugString})"
  | .lit (.string s) => s!"\"{s}\""
  | .lit (.int n) => s!"{n}"
  | .lit (.float f) => s!"{f}"
  | .sort _ => "Sort"
  | .pi _ _ name d c => s!"((${name} : {d.toDebugString}) → {c.toDebugString})"
  | .construct n _ args _ =>
    let argsStr := args.map (·.toDebugString) |>.toList |> String.intercalate ", "
    s!"{n.display}<{argsStr}>"
  | .case scruts _ arms =>
    let scrutsStr := scruts.map (·.toDebugString) |>.toList |> String.intercalate ", "
    let armsStr := arms.map (fun arm => s!"… => {arm.body.toDebugString}")
      |>.toList |> String.intercalate " ; "
    s!"case {scrutsStr} of [{armsStr}]"
  | .record fields =>
    let fieldsStr := (fields.map (fun (n, e) => s!"{n} = {e.toDebugString}")).toList
    "{ " ++ String.intercalate ", " fieldsStr ++ " }"
  | .recordUpdate base updates =>
    let updatesStr := (updates.map (fun (n, e) => s!"{n} := {e.toDebugString}")).toList
    base.toDebugString ++ " with { " ++ String.intercalate ", " updatesStr ++ " }"
  | .fieldAccess e f _ => s!"{e.toDebugString}.{f}"
  | .inject l args _ =>
    let argsStr := args.map (·.toDebugString) |>.toList |> String.intercalate ", "
    s!".{l}<{argsStr}>"
  | .rowSort => "Row"
  | .labelSort => "Label"
  | .rowEmpty => "{}"
  | .rowExtend l f t => "rowext(" ++ l.toDebugString ++ "," ++ f.toDebugString ++ "," ++ t.toDebugString ++ ")"
  | .recordTy r => "RecTy(" ++ r.toDebugString ++ ")"
  | .variantTy r => s!"<Var {r.toDebugString}>"
  | .labelLit n => s!"'{n}"
  | .dataTy id ps =>
    let psStr := ps.map (·.toDebugString) |>.toList |> String.intercalate ", "
    s!"Data<{id.original}, {psStr}>"
  | .if_ c t e => s!"(if {c.toDebugString} then {t.toDebugString} else {e.toDebugString})"
  | .panic msg => s!"panic({msg})"
  | .closure n caps _ =>
    let capsStr := caps.map (·.toDebugString) |>.toList |> String.intercalate ", "
    s!"{n.display}#[{capsStr}]"
  | .array es _ =>
    let esStr := es.map (·.toDebugString) |>.toList |> String.intercalate ", "
    s!"[{esStr}]"
  | .tuple es =>
    let esStr := es.map (·.toDebugString) |>.toList |> String.intercalate ", "
    s!"({esStr})"
  | .proj t f _ => s!"proj{t.display}::{f}"
  | .ann e _ => e.toDebugString

instance : ToString Expr := ⟨Expr.toDebugString⟩

/-- Short constructor name for diagnostic messages -/
def Expr.ctorName : Expr → String
  | .bvar _ => "bvar" | .fvar _ _ => "fvar" | .mvar _ => "mvar" | .const _ _ => "const"
  | .tyvar _ _ => "tyvar"
  | .app _ _ => "app" | .lam _ _ _ _ => "lam" | .let_ _ _ _ _ => "let" | .lit _ => "lit"
  | .sort _ => "sort" | .pi _ _ _ _ _ => "pi"
  | .construct _ _ _ _ => "construct" | .case _ _ _ => "case"
  | .record _ => "record" | .recordUpdate _ _ => "recordUpdate"
  | .fieldAccess _ _ _ => "fieldAccess" | .inject _ _ _ => "inject"
  | .rowSort => "rowSort" | .labelSort => "labelSort"
  | .rowEmpty => "rowEmpty" | .rowExtend _ _ _ => "rowExtend"
  | .recordTy _ => "recordTy" | .variantTy _ => "variantTy"
  | .labelLit _ => "labelLit" | .dataTy _ _ => "dataTy"
  | .if_ _ _ _ => "if" | .panic _ => "panic"
  | .closure _ _ _ => "closure" | .array _ _ => "array" | .tuple _ => "tuple"
  | .proj _ _ _ => "proj" | .ann _ _ => "ann"

deriving instance Serialize, Deserialize for Expr
deriving instance Serialize, Deserialize for Arm
deriving instance BEq for Pattern
deriving instance BEq for Expr
deriving instance BEq for Arm

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
  | .mvar _ | .sort _ | .rowSort
  | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
  | .lit _ | .tyvar _ _ => e
  | .app f a => .app (f.shift amount cutoff) (a.shift amount cutoff)
  | .lam info n d b =>
    .lam info n (d.shift amount cutoff) (b.shift amount (cutoff + 1))
  | .let_ n t v b =>
    .let_ n (t.shift amount cutoff) (v.shift amount cutoff) (b.shift amount (cutoff + 1))
  | .pi q info n d c =>
    .pi q info n (d.shift amount cutoff) (c.shift amount (cutoff + 1))
  | .construct n t args rty =>
    .construct n t (args.map (·.shift amount cutoff)) (rty.shift amount cutoff)
  | .«case» scruts motive arms =>
    .«case» (scruts.map (·.shift amount cutoff))
      (motive.shift amount cutoff)
      (mapArmBodies arms (fun b d => b.shift amount d) cutoff)
  | .record fields =>
    .record (fields.map fun (n, e) => (n, e.shift amount cutoff))
  | .recordUpdate b us =>
    .recordUpdate (b.shift amount cutoff)
      (us.map fun (n, e) => (n, e.shift amount cutoff))
  | .fieldAccess x f i => .fieldAccess (x.shift amount cutoff) f i
  | .inject l args rty => .inject l (args.map (·.shift amount cutoff)) (rty.shift amount cutoff)
  | .if_ c t el =>
    .if_ (c.shift amount cutoff) (t.shift amount cutoff) (el.shift amount cutoff)
  | .closure n caps ty =>
    .closure n (caps.map (·.shift amount cutoff)) (ty.shift amount cutoff)
  | .array es ety => .array (es.map (·.shift amount cutoff)) (ety.shift amount cutoff)
  | .tuple es => .tuple (es.map (·.shift amount cutoff))
  | .rowExtend l f t =>
    .rowExtend (l.shift amount cutoff) (f.shift amount cutoff) (t.shift amount cutoff)
  | .recordTy r => .recordTy (r.shift amount cutoff)
  | .variantTy r => .variantTy (r.shift amount cutoff)
  | .dataTy id ps => .dataTy id (ps.map (·.shift amount cutoff))
  | .ann x t => .ann (x.shift amount cutoff) (t.shift amount cutoff)

def shiftUp (e : Expr) (n : Nat := 1) : Expr :=
  e.shift (Int.ofNat n) 0

/-- Close over a tyvar (out-of-scope quoted variable) -/
partial def abstractTyvar (e : Expr) (target : DeBruijnLvl) : Expr :=
  go e 0
where
  go (e : Expr) (depth : Nat) : Expr :=
    match e with
    | .tyvar lvl _ => if lvl == target then .bvar depth else e
    | .bvar i => if i >= depth then .bvar (i + 1) else e
    | .fvar id ty => .fvar id (go ty depth)
    | .const name ty => .const name (go ty depth)
    | .mvar _ | .sort _ | .rowSort | .labelSort
    | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ | .lit _ => e
    | .app f a => .app (go f depth) (go a depth)
    | .lam info n d b => .lam info n (go d depth) (go b (depth + 1))
    | .let_ n t v b => .let_ n (go t depth) (go v depth) (go b (depth + 1))
    | .pi q info n d c => .pi q info n (go d depth) (go c (depth + 1))
    | .construct n t args rty => .construct n t (args.map (go · depth)) (go rty depth)
    | .«case» scruts motive arms =>
      .«case» (scruts.map (go · depth))
        (go motive depth)
        (mapArmBodies arms (fun b d => go b d) depth)
    | .record fields => .record (fields.map fun (n, e) => (n, go e depth))
    | .recordUpdate b us =>
      .recordUpdate (go b depth) (us.map fun (n, e) => (n, go e depth))
    | .fieldAccess x f i => .fieldAccess (go x depth) f i
    | .inject l args rty => .inject l (args.map (go · depth)) (go rty depth)
    | .if_ c t el => .if_ (go c depth) (go t depth) (go el depth)
    | .closure n caps ty => .closure n (caps.map (go · depth)) (go ty depth)
    | .array es ety => .array (es.map (go · depth)) (go ety depth)
    | .tuple es => .tuple (es.map (go · depth))
    | .rowExtend l f t => .rowExtend (go l depth) (go f depth) (go t depth)
    | .recordTy r => .recordTy (go r depth)
    | .variantTy r => .variantTy (go r depth)
    | .dataTy id ps => .dataTy id (ps.map (go · depth))
    | .ann x t => .ann (go x depth) (go t depth)

/-- Close over a free variable: FVar(fvar) → BVar(depth) -/
partial def abstractFVar (e : Expr) (fvar : Unique) : Expr :=
  go e 0
where
  go (e : Expr) (depth : Nat) : Expr :=
    match e with
    | .fvar u ty => if u == fvar then .bvar depth else .fvar u (go ty depth)
    | .bvar i => if i >= depth then .bvar (i + 1) else e
    | .const name ty => .const name (go ty depth)
    | .mvar _ | .sort _ | .rowSort | .labelSort
    | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ | .lit _ | .tyvar _ _ => e
    | .app f a => .app (go f depth) (go a depth)
    | .lam info n d b => .lam info n (go d depth) (go b (depth + 1))
    | .let_ n t v b => .let_ n (go t depth) (go v depth) (go b (depth + 1))
    | .pi q info n d c => .pi q info n (go d depth) (go c (depth + 1))
    | .construct n t args rty => .construct n t (args.map (go · depth)) (go rty depth)
    | .«case» scruts motive arms =>
      .«case» (scruts.map (go · depth))
        (go motive depth)
        (mapArmBodies arms (fun b d => go b d) depth)
    | .record fields => .record (fields.map fun (n, e) => (n, go e depth))
    | .recordUpdate b us =>
      .recordUpdate (go b depth) (us.map fun (n, e) => (n, go e depth))
    | .fieldAccess x f i => .fieldAccess (go x depth) f i
    | .inject l args rty => .inject l (args.map (go · depth)) (go rty depth)
    | .if_ c t el => .if_ (go c depth) (go t depth) (go el depth)
    | .closure n caps ty => .closure n (caps.map (go · depth)) (go ty depth)
    | .array es ety => .array (es.map (go · depth)) (go ety depth)
    | .tuple es => .tuple (es.map (go · depth))
    | .rowExtend l f t => .rowExtend (go l depth) (go f depth) (go t depth)
    | .recordTy r => .recordTy (go r depth)
    | .variantTy r => .variantTy (go r depth)
    | .dataTy id ps => .dataTy id (ps.map (go · depth))
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
    | .mvar _ | .sort _ | .rowSort
    | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
    | .lit _ | .tyvar _ _ => e
    | .app f a => .app (go f depth) (go a depth)
    | .lam info n d b => .lam info n (go d depth) (go b (depth + 1))
    | .let_ n t v b => .let_ n (go t depth) (go v depth) (go b (depth + 1))
    | .pi q info n d c => .pi q info n (go d depth) (go c (depth + 1))
    | .construct n t args rty => .construct n t (args.map (go · depth)) (go rty depth)
    | .«case» scruts motive arms =>
      .«case» (scruts.map (go · depth))
        (go motive depth)
        (mapArmBodies arms (fun b d => go b d) depth)
    | .record fields => .record (fields.map fun (n, e) => (n, go e depth))
    | .recordUpdate b us =>
      .recordUpdate (go b depth) (us.map fun (n, e) => (n, go e depth))
    | .fieldAccess x f i => .fieldAccess (go x depth) f i
    | .inject l args rty => .inject l (args.map (go · depth)) (go rty depth)
    | .if_ c t el => .if_ (go c depth) (go t depth) (go el depth)
    | .closure n caps ty => .closure n (caps.map (go · depth)) (go ty depth)
    | .array es ety => .array (es.map (go · depth)) (go ety depth)
    | .tuple es => .tuple (es.map (go · depth))
    | .rowExtend l f t => .rowExtend (go l depth) (go f depth) (go t depth)
    | .recordTy r => .recordTy (go r depth)
    | .variantTy r => .variantTy (go r depth)
    | .dataTy id ps => .dataTy id (ps.map (go · depth))
    | .ann x t => .ann (go x depth) (go t depth)

/-- Replace all occurrences of FVar(fvar) with replacement -/
partial def replaceFVar (e : Expr) (fvar : Unique) (replacement : Expr) : Expr :=
  match e with
  | .fvar u ty => if u == fvar then replacement else .fvar u (ty.replaceFVar fvar replacement)
  | .const name ty => .const name (ty.replaceFVar fvar replacement)
  | .bvar _ | .mvar _ | .sort _ | .rowSort
  | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
  | .lit _ | .tyvar _ _ => e
  | .app f a =>
    .app (f.replaceFVar fvar replacement) (a.replaceFVar fvar replacement)
  | .lam info n d b =>
    .lam info n (d.replaceFVar fvar replacement) (b.replaceFVar fvar replacement)
  | .let_ n t v b =>
    .let_ n (t.replaceFVar fvar replacement) (v.replaceFVar fvar replacement)
           (b.replaceFVar fvar replacement)
  | .pi q info n d c =>
    .pi q info n (d.replaceFVar fvar replacement) (c.replaceFVar fvar replacement)
  | .construct n t args rty =>
    .construct n t (args.map (·.replaceFVar fvar replacement)) (rty.replaceFVar fvar replacement)
  | .«case» scruts motive arms =>
    .«case» (scruts.map (·.replaceFVar fvar replacement))
      (motive.replaceFVar fvar replacement)
      (mapArmBodiesSimple arms (·.replaceFVar fvar replacement))
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
  | .closure n caps ty =>
    .closure n (caps.map (·.replaceFVar fvar replacement)) (ty.replaceFVar fvar replacement)
  | .array es ety => .array (es.map (·.replaceFVar fvar replacement)) (ety.replaceFVar fvar replacement)
  | .tuple es => .tuple (es.map (·.replaceFVar fvar replacement))
  | .rowExtend l f t =>
    .rowExtend (l.replaceFVar fvar replacement) (f.replaceFVar fvar replacement)
               (t.replaceFVar fvar replacement)
  | .recordTy r => .recordTy (r.replaceFVar fvar replacement)
  | .variantTy r => .variantTy (r.replaceFVar fvar replacement)
  | .dataTy id ps => .dataTy id (ps.map (·.replaceFVar fvar replacement))
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
    | .bvar _ | .mvar _ | .sort _ | .rowSort
    | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
    | .lit _ | .tyvar _ _ => acc
    | .app f a => go a (go f acc)
    | .lam _ _ d b => go b (go d acc)
    | .let_ _ t v b => go b (go v (go t acc))
    | .pi _ _ _ d c => go c (go d acc)
    | .construct _ _ args rty => go rty (args.foldl (fun a e => go e a) acc)
    | .«case» scruts motive arms =>
      let acc := scruts.foldl (fun a e => go e a) acc
      let acc := go motive acc
      arms.foldl (fun a arm => go arm.body a) acc
    | .record fields => fields.foldl (fun a (_, e) => go e a) acc
    | .recordUpdate b us =>
      let acc := go b acc
      us.foldl (fun a (_, e) => go e a) acc
    | .fieldAccess x _ _ => go x acc
    | .inject _ args rty => go rty (args.foldl (fun a e => go e a) acc)
    | .if_ c t el => go el (go t (go c acc))
    | .closure _ caps ty => go ty (caps.foldl (fun a e => go e a) acc)
    | .array es ety => go ety (es.foldl (fun a e => go e a) acc)
    | .tuple es => es.foldl (fun a e => go e a) acc
    | .rowExtend l f t => go t (go f (go l acc))
    | .recordTy r => go r acc
    | .variantTy r => go r acc
    | .dataTy _ ps => ps.foldl (fun a e => go e a) acc
    | .ann x t => go t (go x acc)

/-- Collect every global (`.const`) reference in an expression, keyed by the callee's `QualifiedName`) -/
partial def collectConsts (e : Expr) : Std.HashSet QualifiedName :=
  go e {}
where
  go (e : Expr) (acc : Std.HashSet QualifiedName) : Std.HashSet QualifiedName :=
    match e with
    | .const name ty => go ty (acc.insert name)
    | .fvar _ ty => go ty acc
    | .bvar _ | .mvar _ | .sort _ | .rowSort
    | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
    | .lit _ | .tyvar _ _ => acc
    | .app f a => go a (go f acc)
    | .lam _ _ d b => go b (go d acc)
    | .let_ _ t v b => go b (go v (go t acc))
    | .pi _ _ _ d c => go c (go d acc)
    | .construct _ _ args rty => go rty (args.foldl (fun a e => go e a) acc)
    | .«case» scruts motive arms =>
      let acc := scruts.foldl (fun a e => go e a) acc
      let acc := go motive acc
      arms.foldl (fun a arm => go arm.body a) acc
    | .record fields => fields.foldl (fun a (_, e) => go e a) acc
    | .recordUpdate b us =>
      let acc := go b acc
      us.foldl (fun a (_, e) => go e a) acc
    | .fieldAccess x _ _ => go x acc
    | .inject _ args rty => go rty (args.foldl (fun a e => go e a) acc)
    | .if_ c t el => go el (go t (go c acc))
    | .closure _ caps ty => go ty (caps.foldl (fun a e => go e a) acc)
    | .array es ety => go ety (es.foldl (fun a e => go e a) acc)
    | .tuple es => es.foldl (fun a e => go e a) acc
    | .rowExtend l f t => go t (go f (go l acc))
    | .recordTy r => go r acc
    | .variantTy r => go r acc
    | .dataTy _ ps => ps.foldl (fun a e => go e a) acc
    | .ann x t => go t (go x acc)

/-- Check if an expression contains a specific free variable -/
partial def hasFVar (e : Expr) (fvar : Unique) : Bool :=
  match e with
  | .fvar u ty => u == fvar || ty.hasFVar fvar
  | .const _ ty => ty.hasFVar fvar
  | .bvar _ | .mvar _ | .sort _ | .rowSort
  | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
  | .lit _ | .tyvar _ _ => false
  | .app f a => f.hasFVar fvar || a.hasFVar fvar
  | .lam _ _ d b => d.hasFVar fvar || b.hasFVar fvar
  | .let_ _ t v b => t.hasFVar fvar || v.hasFVar fvar || b.hasFVar fvar
  | .pi _ _ _ d c => d.hasFVar fvar || c.hasFVar fvar
  | .construct _ _ args rty => args.any (·.hasFVar fvar) || rty.hasFVar fvar
  | .«case» scruts motive arms =>
    scruts.any (·.hasFVar fvar) || motive.hasFVar fvar || arms.any (fun arm => arm.body.hasFVar fvar)
  | .record fields => fields.any (fun p => p.2.hasFVar fvar)
  | .recordUpdate b us =>
    b.hasFVar fvar || us.any (fun p => p.2.hasFVar fvar)
  | .fieldAccess x _ _ => x.hasFVar fvar
  | .inject _ args rty => args.any (·.hasFVar fvar) || rty.hasFVar fvar
  | .if_ c t el => c.hasFVar fvar || t.hasFVar fvar || el.hasFVar fvar
  | .closure _ caps ty => caps.any (·.hasFVar fvar) || ty.hasFVar fvar
  | .array es ety => es.any (·.hasFVar fvar) || ety.hasFVar fvar
  | .tuple es => es.any (·.hasFVar fvar)
  | .rowExtend l f t => l.hasFVar fvar || f.hasFVar fvar || t.hasFVar fvar
  | .recordTy r => r.hasFVar fvar
  | .variantTy r => r.hasFVar fvar
  | .dataTy _ ps => ps.any (·.hasFVar fvar)
  | .ann x t => x.hasFVar fvar || t.hasFVar fvar

/-- Is the type expression `ty` itself a universe -/
private partial def isTypeUniverse : Expr → Bool
  | .sort _ => true
  | .pi _ _ _ _ codomain => isTypeUniverse codomain
  | .ann e _ => isTypeUniverse e
  | _ => false

/-- An expression is type-level when it inhabits the universe of types and has no runtime content -/
partial def isTypeLevelExpr : Expr → Bool
  | .sort _ | .pi _ _ _ _ _
  | .rowSort | .labelSort | .rowEmpty | .rowExtend _ _ _
  | .recordTy _ | .variantTy _ | .labelLit _ | .dataTy _ _
  | .mvar _ | .tyvar _ _ => true
  | .const _ ty => isTypeUniverse ty
  | .fvar _ ty => isTypeUniverse ty
  | .ann e _ => isTypeLevelExpr e
  | .app fn _ => isTypeLevelExpr fn
  | _ => false

/-- Collect an application spine: `f a b c` → `(f, #[a, b, c])` -/
def collectAppSpine (e : Expr) : Expr × Array Expr :=
  let (head, revArgs) := go e #[]
  (head, revArgs.reverse)
where
  go (e : Expr) (acc : Array Expr) : Expr × Array Expr :=
    match e with
    | .app fn arg => go fn (acc.push arg)
    | _ => (e, acc)

/-- Rebuild an application spine from head and args -/
def rebuildAppSpine (fn : Expr) (args : Array Expr) : Expr :=
  args.foldl (init := fn) fun acc arg => .app acc arg

/-- Count occurrences of bvar(depth) in an expression -/
partial def countBVar (e : Expr) (depth : Nat := 0) : Nat :=
  match e with
  | .bvar i => if i == depth then 1 else 0
  | .app f a => countBVar f depth + countBVar a depth
  | .lam _ _ d b => countBVar d depth + countBVar b (depth + 1)
  | .let_ _ t v b => countBVar t depth + countBVar v depth + countBVar b (depth + 1)
  | .«case» scruts motive arms =>
    let s := scruts.foldl (fun acc e => acc + countBVar e depth) 0
    let m := countBVar motive depth
    let a := arms.foldl (fun acc arm =>
      acc + countBVar arm.body (depth + arm.patterns.foldl (fun n p => n + p.bindingCount) 0)) 0
    s + m + a
  | .if_ c t el => countBVar c depth + countBVar t depth + countBVar el depth
  | .construct _ _ args _ => args.foldl (fun acc e => acc + countBVar e depth) 0
  | .fieldAccess x _ _ => countBVar x depth
  | .closure _ caps ty =>
    caps.foldl (fun acc e => acc + countBVar e depth) 0 + countBVar ty depth
  | .fvar _ _ => 0
  | .const _ _ => 0
  | _ => 0

/-- Exhaustive beta-reduction: reduces `app (lam ...) arg` redexes.
    When `stripTypeArgs` is true, type-level arguments applied to non-lambda
    heads are dropped (useful after dictionary specialization)

    Sharing-preserving: if the binder is `.explicit` and the bound variable
    is used more than once in the body, we emit `.let_` rather than
    substitute `arg'` at every use site -/
partial def betaReduce (e : Expr) (stripTypeArgs : Bool := false) : Expr :=
  match e with
  | .app fn arg =>
    let fn' := betaReduce fn stripTypeArgs
    let arg' := betaReduce arg stripTypeArgs
    match fn' with
    | .lam info name domain body =>
      let uses := body.countBVar 0
      if uses <= 1 || info != .explicit then
        betaReduce (body.instantiate arg') stripTypeArgs
      else
        .let_ name (betaReduce domain stripTypeArgs) arg' (betaReduce body stripTypeArgs)
    | _ =>
      if stripTypeArgs && isTypeLevelExpr arg' then fn'
      else .app fn' arg'
  | .lam info name domain body =>
    .lam info name (betaReduce domain stripTypeArgs) (betaReduce body stripTypeArgs)
  | .let_ name ty val body =>
    .let_ name (betaReduce ty stripTypeArgs) (betaReduce val stripTypeArgs) (betaReduce body stripTypeArgs)
  | .pi qty info name domain codomain =>
    .pi qty info name (betaReduce domain stripTypeArgs) (betaReduce codomain stripTypeArgs)
  | .if_ c t el => .if_ (betaReduce c stripTypeArgs) (betaReduce t stripTypeArgs) (betaReduce el stripTypeArgs)
  | .«case» scruts motive arms =>
    .«case» (scruts.map (betaReduce · stripTypeArgs))
      (betaReduce motive stripTypeArgs)
      (arms.map fun arm => Arm.mk arm.patterns (betaReduce arm.body stripTypeArgs))
  | .construct name tag args resultTy =>
    .construct name tag (args.map (betaReduce · stripTypeArgs)) (betaReduce resultTy stripTypeArgs)
  | .fieldAccess expr field idx => .fieldAccess (betaReduce expr stripTypeArgs) field idx
  | .record fields => .record (fields.map fun (n, x) => (n, betaReduce x stripTypeArgs))
  | .recordUpdate base updates =>
    .recordUpdate (betaReduce base stripTypeArgs) (updates.map fun (n, x) => (n, betaReduce x stripTypeArgs))
  | .inject label args resultTy => .inject label (args.map (betaReduce · stripTypeArgs)) (betaReduce resultTy stripTypeArgs)
  | .closure name captures ty =>
    .closure name (captures.map (betaReduce · stripTypeArgs)) (betaReduce ty stripTypeArgs)
  | .array es ety => .array (es.map (betaReduce · stripTypeArgs)) (betaReduce ety stripTypeArgs)
  | .tuple es => .tuple (es.map (betaReduce · stripTypeArgs))
  | .ann x t => .ann (betaReduce x stripTypeArgs) (betaReduce t stripTypeArgs)
  | _ => e

/-- Count the number of occurrences of a specific free variable in an expression -/
partial def countFVar (e : Expr) (fvar : Unique) : Nat :=
  match e with
  | .fvar u ty => (if u == fvar then 1 else 0) + ty.countFVar fvar
  | .const _ ty => ty.countFVar fvar
  | .bvar _ | .mvar _ | .sort _ | .rowSort
  | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
  | .lit _ | .tyvar _ _ => 0
  | .app f a => f.countFVar fvar + a.countFVar fvar
  | .lam _ _ d b => d.countFVar fvar + b.countFVar fvar
  | .let_ _ t v b => t.countFVar fvar + v.countFVar fvar + b.countFVar fvar
  | .pi _ _ _ d c => d.countFVar fvar + c.countFVar fvar
  | .construct _ _ args rty => args.foldl (fun acc a => acc + a.countFVar fvar) 0 + rty.countFVar fvar
  | .«case» scruts motive arms =>
    let scrutCount := scruts.foldl (fun acc s => acc + s.countFVar fvar) 0
    let armSum := arms.foldl (fun acc arm => acc + arm.body.countFVar fvar) 0
    scrutCount + motive.countFVar fvar + armSum
  | .record fields => fields.foldl (fun acc (_, e) => acc + e.countFVar fvar) 0
  | .recordUpdate b us =>
    b.countFVar fvar + us.foldl (fun acc (_, e) => acc + e.countFVar fvar) 0
  | .fieldAccess x _ _ => x.countFVar fvar
  | .inject _ args rty => args.foldl (fun acc a => acc + a.countFVar fvar) 0 + rty.countFVar fvar
  | .if_ c t el =>
    c.countFVar fvar + t.countFVar fvar + el.countFVar fvar
  | .closure _ caps ty =>
    caps.foldl (fun acc e => acc + e.countFVar fvar) 0 + ty.countFVar fvar
  | .array es ety => es.foldl (fun acc e => acc + e.countFVar fvar) 0 + ety.countFVar fvar
  | .tuple es => es.foldl (fun acc e => acc + e.countFVar fvar) 0
  | .rowExtend l f t => l.countFVar fvar + f.countFVar fvar + t.countFVar fvar
  | .recordTy r => r.countFVar fvar
  | .variantTy r => r.countFVar fvar
  | .dataTy _ ps => ps.foldl (fun acc p => acc + p.countFVar fvar) 0
  | .ann x t => x.countFVar fvar + t.countFVar fvar

/-- Collect every metavariable referenced anywhere inside this expression -/
partial def collectMetas : Expr → Array MetaId
  | .mvar mid => #[mid]
  | .app f a => collectMetas f ++ collectMetas a
  | .lam _ _ d b => collectMetas d ++ collectMetas b
  | .let_ _ t v b => collectMetas t ++ collectMetas v ++ collectMetas b
  | .pi _ _ _ d c => collectMetas d ++ collectMetas c
  | .if_ c t e => collectMetas c ++ collectMetas t ++ collectMetas e
  | .«case» scruts motive arms =>
    let m := scruts.foldl (fun acc s => acc ++ collectMetas s) #[]
    let m := m ++ collectMetas motive
    arms.foldl (fun acc arm => acc ++ collectMetas arm.body) m
  | .rowExtend l t tail => collectMetas l ++ collectMetas t ++ collectMetas tail
  | .recordTy r => collectMetas r
  | .variantTy r => collectMetas r
  | .record fs => fs.foldl (fun acc (_, e) => acc ++ collectMetas e) #[]
  | .recordUpdate b us =>
    us.foldl (fun acc (_, e) => acc ++ collectMetas e) (collectMetas b)
  | .fieldAccess e _ _ => collectMetas e
  | .construct _ _ args _ => args.foldl (fun acc a => acc ++ collectMetas a) #[]
  | .inject _ args _ => args.foldl (fun acc a => acc ++ collectMetas a) #[]
  | .closure _ caps ty =>
    caps.foldl (fun acc c => acc ++ collectMetas c) #[] ++ collectMetas ty
  | .array es _ => es.foldl (fun acc e => acc ++ collectMetas e) #[]
  | .tuple es => es.foldl (fun acc e => acc ++ collectMetas e) #[]
  | .dataTy _ ps => ps.foldl (fun acc p => acc ++ collectMetas p) #[]
  | .fvar _ t | .const _ t | .ann _ t => collectMetas t
  | _ => #[]

end Expr

end Soma.Core
