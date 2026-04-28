import Soma.Syntax.Source
import Soma.Core.Quantity
import Soma.Core.Expr
import Std.Data.HashSet

namespace Soma.Syntax

open Soma.Core (Quantity BinderInfo)

/-- An operator name (wrapped in braces in source: {+}, {>>=}) -/
structure OpName where
  value : String
  span : Span
  deriving Repr, BEq, Inhabited

instance : ToString OpName where
  toString n := s!"\{{n.value}}"

/-- A qualified name (module path + name) -/
structure QualName where
  path : Array String
  name : String
  span : Span
  deriving Repr, BEq, Inhabited

instance : ToString QualName where
  toString qn :=
    if qn.path.isEmpty then qn.name
    else String.intercalate "::" qn.path.toList ++ "::" ++ qn.name

namespace QualName

/-- The fully qualified display string -/
def display (qn : QualName) : String := toString qn

/-- Whether this is an unqualified (simple) name -/
def isSimple (qn : QualName) : Bool := qn.path.isEmpty

/-- All segments as a flat list (path ++ [name]) -/
def segments (qn : QualName) : List String := qn.path.toList ++ [qn.name]

end QualName

/-! ## Literals -/

/-- Literal values -/
inductive Literal where
  | int (value : Int) (span : Span)
  | string (value : String) (span : Span)
  | bool (value : Bool) (span : Span)
  deriving Repr

namespace Literal

def span : Literal → Span
  | .int _ s => s
  | .string _ s => s
  | .bool _ s => s

end Literal

mutual

/-- Patterns for destructuring in case expressions and function definitions -/
inductive Pattern : Type where
  /-- Variable pattern: x -/
  | var (name : QualName)
  /-- Wildcard pattern: _ -/
  | wildcard (span : Span)
  /-- Literal pattern: 42, "hello", true -/
  | lit (lit : Literal)
  /-- Constructor pattern: Some x, Cons h t -/
  | con (name : QualName) (args : Array Pattern) (span : Span)
  /-- Tuple pattern: (a, b, c) -/
  | tuple (elements : Array Pattern) (span : Span)
  /-- List pattern: [a, b, c] -/
  | list (elements : Array Pattern) (span : Span)
  /-- Cons pattern: (x:xs) -/
  | cons (head : Pattern) (tail : Pattern) (span : Span)
  /-- Parenthesized pattern (for precedence) -/
  | parens (inner : Pattern) (span : Span)
  /-- Typed pattern: (x :: Type) -/
  | typed (pat : Pattern) (ty : Expr) (span : Span)
  /-- Variant pattern: .Ok x -/
  | variant (label : QualName) (arg : Option Pattern) (span : Span)

/-- A type-class constraint applied to type arguments -/
structure Constraint where
  className : QualName
  args : Array Expr
  span : Span

/-- A binder -/
inductive TypeVarBinder : Type where
  | mk (name : QualName)        (kind : Option Expr) : TypeVarBinder
  | constraint (name : Option QualName) (cstr : Constraint)  : TypeVarBinder

/-- A match arm -/
inductive MatchArm : Type where
  | mk (patterns : Array Pattern) (guard : Option Expr) (body : Expr) (span : Span)

/-- A statement in a compose block -/
inductive ComposeStmt : Type where
  /-- Expression statement: `action` that desugars to `action >> rest` -/
  | expr (action : Expr) (span : Span)
  /-- Let binding: `let x = value` that desugars to `case value of | x -> rest` -/
  | let_ (name : QualName) (value : Expr) (span : Span)
  /-- Monadic bind: `bind x <- action` that desugars to `action >>= (\x -> rest)` -/
  | bind_ (name : QualName) (action : Expr) (span : Span)

/-- Argument to an explicit type application -/
inductive TypeAppArg : Type where
  /-- A type expression: @Int -/
  | type (ty : Expr)
  /-- A label literal: @fieldName -/
  | label (name : QualName)

/-- AST expressions -/
inductive Expr : Type where
  /-- Variable reference -/
  | var (name : QualName)
  /-- Type constructor shaped reference: `Nat`, `Int32`, `Option` -/
  | con (name : QualName)
  /-- Parenthesised expression -/
  | parens (inner : Expr) (span : Span)
  /-- Function / type application -/
  | app (fn : Expr) (arg : Expr) (span : Span)
  /-- Tuple / tuple-type -/
  | tuple (elements : Array Expr) (span : Span)
  /-- List / list-type -/
  | list (elements : Array Expr) (span : Span)
  /-- Literal -/
  | lit (lit : Literal)
  /-- Infix operator application -/
  | infix (op : OpName) (left : Expr) (right : Expr) (span : Span)
  /-- Lambda expression -/
  | lambda (params : Array (QualName × Option Expr)) (body : Expr) (span : Span)
  /-- If expression -/
  | if_ (cond : Expr) (then_ : Expr) (else_ : Expr) (span : Span)
  /-- Case expression -/
  | case (scrutinees : Array Expr) (arms : Array MatchArm) (span : Span)
  /-- Record value -/
  | record (fields : Array (QualName × Expr)) (span : Span)
  /-- Record update -/
  | recordUpdate (base : Expr) (updates : Array (QualName × Expr)) (span : Span)
  /-- Field access -/
  | fieldAccess (expr : Expr) (field : QualName) (span : Span)
  /-- Projection function -/
  | projection (typeName : QualName) (fieldName : QualName) (span : Span)
  /-- Type annotation at term level -/
  | typeAnnot (expr : Expr) (type_ : Expr) (span : Span)
  /-- Explicit type application -/
  | typeApp (typeArg : TypeAppArg) (span : Span)
  /-- Compose block -/
  | composeBlock (stmts : Array ComposeStmt) (final_ : Expr) (span : Span)
  /-- Variant-value injection -/
  | variant (label : QualName) (arg : Option Expr) (span : Span)
  /-- Non-dependent fn, the elaborator desugars it to `.pi .omega .explicit "_" A B` -/
  | arrow (from_ : Expr) (to : Expr) (span : Span)
  /-- Dependent function type -/
  | pi (qty : Quantity) (binder : BinderInfo) (name : QualName)
       (domain : Expr) (codomain : Expr) (span : Span)
  /-- Dependent pair` -/
  | sigma (qty : Quantity) (name : QualName) (fst : Expr) (snd : Expr) (span : Span)
  /-- Universal quantification shorthand, elaborator also desugars -/
  | forall_ (vars : Array TypeVarBinder) (body : Expr) (span : Span)
  /-- Record type -/
  | recordTy (fields : Array (QualName × Expr)) (tail : Option QualName) (span : Span)
  /-- Variant type -/
  | variantTy (cases : Array (QualName × Expr)) (tail : Option QualName) (span : Span)
  /-- TODO: review design and remove -/
  | listTy (elem : Expr) (span : Span)

end

namespace TypeVarBinder

/-- The binder name -/
def name : TypeVarBinder → QualName
  | .mk n _ => n
  | .constraint (some n) _ => n
  | .constraint none cstr => ⟨#[], "_", cstr.span⟩

/-- The kind/type annotation of a type-variable binder -/
def kind : TypeVarBinder → Option Expr
  | .mk _ k => k
  | .constraint .. => none

/-- The constraint of a `.constraint` binder -/
def constraint? : TypeVarBinder → Option Constraint
  | .mk .. => none
  | .constraint _ cstr => some cstr

/-- Whether this binder introduces a class-dictionary (instance) parameter -/
def isConstraint : TypeVarBinder → Bool
  | .mk .. => false
  | .constraint .. => true

/-- Source span of the binder -/
def span : TypeVarBinder → Span
  | .mk n _ => n.span
  | .constraint (some n) _ => n.span
  | .constraint none cstr => cstr.span

end TypeVarBinder

instance : Inhabited TypeVarBinder := ⟨.mk ⟨#[], "_", Span.uninhabited⟩ none⟩

instance : Nonempty Pattern := ⟨.wildcard Span.uninhabited⟩
instance : Nonempty Expr := ⟨.var ⟨#[], "_", Span.uninhabited⟩⟩
instance : Nonempty TypeVarBinder := ⟨.mk ⟨#[], "_", Span.uninhabited⟩ none⟩
instance : Nonempty MatchArm :=
  ⟨.mk #[] none (.var ⟨#[], "_", Span.uninhabited⟩) Span.uninhabited⟩
instance : Nonempty TypeAppArg := ⟨.label ⟨#[], "_", Span.uninhabited⟩⟩

mutual

partial def Pattern.repr' (p : Pattern) (_ : Nat) : Std.Format :=
  match p with
  | .var name => f!"Pattern.var {Repr.reprPrec name 0}"
  | .wildcard span => f!"Pattern.wildcard {Repr.reprPrec span 0}"
  | .lit lit => f!"Pattern.lit {Repr.reprPrec lit 0}"
  | .con name args span =>
      f!"Pattern.con {Repr.reprPrec name 0} #[...{args.size}] {Repr.reprPrec span 0}"
  | .tuple elems span => f!"Pattern.tuple #[...{elems.size}] {Repr.reprPrec span 0}"
  | .list elems span => f!"Pattern.list #[...{elems.size}] {Repr.reprPrec span 0}"
  | .cons h t span =>
      f!"Pattern.cons ({Pattern.repr' h 0}) ({Pattern.repr' t 0}) {Repr.reprPrec span 0}"
  | .parens inner span =>
      f!"Pattern.parens ({Pattern.repr' inner 0}) {Repr.reprPrec span 0}"
  | .typed pat ty span =>
      f!"Pattern.typed ({Pattern.repr' pat 0}) ({Expr.repr' ty 0}) {Repr.reprPrec span 0}"
  | .variant label arg span =>
      let argRepr := match arg with
        | some p => f!"some ({Pattern.repr' p 0})"
        | none => f!"none"
      f!"Pattern.variant {Repr.reprPrec label 0} {argRepr} {Repr.reprPrec span 0}"

partial def Expr.repr' (e : Expr) (_ : Nat) : Std.Format :=
  match e with
  | .var name => f!"Expr.var {Repr.reprPrec name 0}"
  | .con name => f!"Expr.con {Repr.reprPrec name 0}"
  | .parens inner _ => f!"Expr.parens ({Expr.repr' inner 0})"
  | .app fn arg _ =>
      f!"Expr.app ({Expr.repr' fn 0}) ({Expr.repr' arg 0})"
  | .tuple elems _ => f!"Expr.tuple #[...{elems.size}]"
  | .list elems _ => f!"Expr.list #[...{elems.size}]"
  | .lit l => f!"Expr.lit {Repr.reprPrec l 0}"
  | .infix op l r _ =>
      f!"Expr.infix {Repr.reprPrec op 0} ({Expr.repr' l 0}) ({Expr.repr' r 0})"
  | .lambda params body _ =>
      f!"Expr.lambda #[...{params.size}] ({Expr.repr' body 0})"
  | .if_ c t e _ =>
      f!"Expr.if_ ({Expr.repr' c 0}) ({Expr.repr' t 0}) ({Expr.repr' e 0})"
  | .case scruts arms _ =>
      f!"Expr.case #[...{scruts.size}] #[...{arms.size}]"
  | .record fields _ => f!"Expr.record #[...{fields.size}]"
  | .recordUpdate base updates _ =>
      f!"Expr.recordUpdate ({Expr.repr' base 0}) #[...{updates.size}]"
  | .fieldAccess e f _ =>
      f!"Expr.fieldAccess ({Expr.repr' e 0}) {Repr.reprPrec f 0}"
  | .projection t f _ =>
      f!"Expr.projection {Repr.reprPrec t 0} {Repr.reprPrec f 0}"
  | .typeAnnot e ty _ =>
      f!"Expr.typeAnnot ({Expr.repr' e 0}) ({Expr.repr' ty 0})"
  | .typeApp arg _ =>
      let short := match arg with
        | .type _ => "@<type>"
        | .label n => s!"@{n.name}"
      f!"Expr.typeApp {Repr.reprPrec short 0}"
  | .composeBlock stmts final _ =>
      f!"Expr.composeBlock #[...{stmts.size}] ({Expr.repr' final 0})"
  | .variant label arg _ =>
      let argR := match arg with | some e => f!"some ({Expr.repr' e 0})" | none => f!"none"
      f!"Expr.variant {Repr.reprPrec label 0} {argR}"
  | .arrow a b _ =>
      f!"Expr.arrow ({Expr.repr' a 0}) ({Expr.repr' b 0})"
  | .pi qty binder name dom cod _ =>
      f!"Expr.pi {Repr.reprPrec qty 0} {Repr.reprPrec binder 0} {Repr.reprPrec name 0} ({Expr.repr' dom 0}) ({Expr.repr' cod 0})"
  | .sigma qty name fst snd _ =>
      f!"Expr.sigma {Repr.reprPrec qty 0} {Repr.reprPrec name 0} ({Expr.repr' fst 0}) ({Expr.repr' snd 0})"
  | .forall_ vars body _ =>
      f!"Expr.forall_ #[...{vars.size}] ({Expr.repr' body 0})"
  | .recordTy fields tail _ =>
      f!"Expr.recordTy #[...{fields.size}] {Repr.reprPrec tail 0}"
  | .variantTy cases tail _ =>
      f!"Expr.variantTy #[...{cases.size}] {Repr.reprPrec tail 0}"
  | .listTy elem _ =>
      f!"Expr.listTy ({Expr.repr' elem 0})"

end

instance : Repr Pattern := ⟨Pattern.repr'⟩
instance : Repr Expr := ⟨Expr.repr'⟩
instance : Repr TypeAppArg where
  reprPrec a _ := match a with
    | .type ty => f!"TypeAppArg.type ({Expr.repr' ty 0})"
    | .label n => f!"TypeAppArg.label {Repr.reprPrec n 0}"
instance : Repr Constraint where
  reprPrec c _ :=
    f!"Constraint.mk {Repr.reprPrec c.className 0} #[...{c.args.size}] {Repr.reprPrec c.span 0}"
instance : Repr TypeVarBinder where
  reprPrec v _ := match v with
    | .mk n k =>
        f!"TypeVarBinder.mk {Repr.reprPrec n 0} {Repr.reprPrec k 0}"
    | .constraint n? c =>
        f!"TypeVarBinder.constraint {Repr.reprPrec n? 0} {Repr.reprPrec c 0}"
instance : Repr MatchArm where
  reprPrec m _ := match m with
    | .mk ps guard body span =>
        let g := match guard with | some e => f!"some ({Expr.repr' e 0})" | none => f!"none"
        f!"MatchArm.mk #[...{ps.size}] {g} ({Expr.repr' body 0}) {Repr.reprPrec span 0}"
instance : Repr ComposeStmt where
  reprPrec s _ := match s with
    | .expr a _ => f!"ComposeStmt.expr ({Expr.repr' a 0})"
    | .let_ n v _ => f!"ComposeStmt.let_ {Repr.reprPrec n 0} ({Expr.repr' v 0})"
    | .bind_ n v _ => f!"ComposeStmt.bind_ {Repr.reprPrec n 0} ({Expr.repr' v 0})"

instance : BEq TypeVarBinder where
  beq a b := match a, b with
    | .mk n₁ _, .mk n₂ _ => n₁ == n₂
    | .constraint n₁ c₁, .constraint n₂ c₂ =>
        n₁.map QualName.name == n₂.map QualName.name &&
        c₁.className == c₂.className && c₁.args.size == c₂.args.size
    | _, _ => false

namespace Pattern

def span : Pattern → Span
  | .var name => name.span
  | .wildcard s => s
  | .lit l => l.span
  | .con _ _ s => s
  | .tuple _ s => s
  | .list _ s => s
  | .cons _ _ s => s
  | .parens _ s => s
  | .typed _ _ s => s
  | .variant _ _ s => s

/-- Get all variable names bound by this pattern -/
partial def boundVars : Pattern → Array QualName
  | .var name => #[name]
  | .wildcard _ => #[]
  | .lit _ => #[]
  | .con _ args _ => args.foldl (fun acc p => acc ++ p.boundVars) #[]
  | .tuple elems _ => elems.foldl (fun acc p => acc ++ p.boundVars) #[]
  | .list elems _ => elems.foldl (fun acc p => acc ++ p.boundVars) #[]
  | .cons h t _ => h.boundVars ++ t.boundVars
  | .parens inner _ => inner.boundVars
  | .typed pat _ _ => pat.boundVars
  | .variant _ arg _ => match arg with
    | some p => p.boundVars
    | none => #[]

end Pattern

namespace Expr

def span : Expr → Span
  | .var name => name.span
  | .con name => name.span
  | .parens _ s => s
  | .app _ _ s => s
  | .tuple _ s => s
  | .list _ s => s
  | .lit l => l.span
  | .infix _ _ _ s => s
  | .lambda _ _ s => s
  | .if_ _ _ _ s => s
  | .case _ _ s => s
  | .record _ s => s
  | .recordUpdate _ _ s => s
  | .fieldAccess _ _ s => s
  | .projection _ _ s => s
  | .typeAnnot _ _ s => s
  | .typeApp _ s => s
  | .composeBlock _ _ s => s
  | .variant _ _ s => s
  | .arrow _ _ s => s
  | .pi _ _ _ _ _ s => s
  | .sigma _ _ _ _ s => s
  | .forall_ _ _ s => s
  | .recordTy _ _ s => s
  | .variantTy _ _ s => s
  | .listTy _ s => s

/-- Collect every identifier name that appears in this expression -/
partial def freeVars : Expr → Array QualName
  | .var name => #[name]
  | .con _ => #[]
  | .parens inner _ => inner.freeVars
  | .app fn arg _ => fn.freeVars ++ arg.freeVars
  | .tuple elems _ => elems.foldl (fun acc t => acc ++ t.freeVars) #[]
  | .list elems _ => elems.foldl (fun acc t => acc ++ t.freeVars) #[]
  | .lit _ => #[]
  | .infix _ l r _ => l.freeVars ++ r.freeVars
  | .lambda params body _ =>
      let boundNames := params.map (·.1.name)
      let paramTypeVars := params.foldl (fun acc (_, tyOpt) =>
        match tyOpt with
        | some ty => acc ++ ty.freeVars
        | none => acc) #[]
      paramTypeVars ++ body.freeVars.filter fun v => !boundNames.contains v.name
  | .if_ c t e _ => c.freeVars ++ t.freeVars ++ e.freeVars
  | .case scruts arms _ =>
      let scrutVars := scruts.foldl (fun acc e => acc ++ e.freeVars) #[]
      let armVars := arms.foldl (fun acc arm =>
        match arm with
        | .mk ps g b _ =>
          let boundNames := ps.foldl (fun acc p => acc ++ p.boundVars.map (·.name)) #[]
          let gVars := (g.map (·.freeVars)).getD #[]
          let bVars := b.freeVars
          acc ++ gVars ++ bVars.filter fun v => !boundNames.contains v.name) #[]
      scrutVars ++ armVars
  | .record fields _ => fields.foldl (fun acc (_, e) => acc ++ e.freeVars) #[]
  | .recordUpdate base updates _ =>
      base.freeVars ++ updates.foldl (fun acc (_, e) => acc ++ e.freeVars) #[]
  | .fieldAccess e _ _ => e.freeVars
  | .projection _ _ _ => #[]
  | .typeAnnot e ty _ => e.freeVars ++ ty.freeVars
  | .typeApp arg _ => match arg with
    | .type ty => ty.freeVars
    | .label _ => #[]
  | .composeBlock stmts final _ =>
      let stmtVars := stmts.foldl (fun acc s =>
        match s with
        | .expr e _ => acc ++ e.freeVars
        | .let_ _ v _ => acc ++ v.freeVars
        | .bind_ _ v _ => acc ++ v.freeVars) #[]
      stmtVars ++ final.freeVars
  | .variant _ arg _ => match arg with
    | some e => e.freeVars
    | none => #[]
  | .arrow from_ to _ => from_.freeVars ++ to.freeVars
  | .pi _ _ name dom cod _ =>
      dom.freeVars ++ (cod.freeVars.filter fun v => v.name != name.name)
  | .sigma _ name fst snd _ =>
      fst.freeVars ++ (snd.freeVars.filter fun v => v.name != name.name)
  | .forall_ vars body _ =>
      let (acc, bound) := vars.foldl
        (fun (state : Array QualName × Array String) v =>
          let (acc, bound) := state
          let domVars : Array QualName := match v with
            | .mk _ (some k)     => k.freeVars
            | .mk _ none         => #[]
            | .constraint _ cstr =>
                cstr.args.foldl (fun a e => a ++ e.freeVars) #[]
          let newAcc := acc ++ domVars.filter fun q => !bound.contains q.name
          let bound' := match v with
            | .mk n _              => bound.push n.name
            | .constraint (some n) _ => bound.push n.name
            | .constraint none _   => bound
          (newAcc, bound'))
        (#[], #[])
      acc ++ body.freeVars.filter fun v => !bound.contains v.name
  | .recordTy fields tail _ =>
      let fieldVars := fields.foldl (fun acc (_, t) => acc ++ t.freeVars) #[]
      match tail with
      | some n => fieldVars ++ #[n]
      | none => fieldVars
  | .variantTy cases tail _ =>
      let caseVars := cases.foldl (fun acc (_, t) => acc ++ t.freeVars) #[]
      match tail with
      | some n => caseVars ++ #[n]
      | none => caseVars
  | .listTy elem _ => elem.freeVars

/-- Collect every identifier name (as a string) appearing in the expression -/
partial def collectVarNames (e : Expr) : Std.HashSet String :=
  (freeVars e).foldl (fun acc n => acc.insert n.name) {}

end Expr

namespace TypeAppArg

def span : TypeAppArg → Span
  | .type ty => ty.span
  | .label name => name.span

end TypeAppArg

/-! ## Additional type-level accessors (common lookups used by the elaborator) -/

namespace Expr

/-- When this expression is a bare identifier, return the full qualified name -/
def asVarName? : Expr → Option QualName
  | .var n => some n
  | .con n => some n
  | .parens inner _ => inner.asVarName?
  | _ => none

end Expr

namespace MatchArm

def patterns (m : MatchArm) : Array Pattern := match m with | .mk ps _ _ _ => ps
def guard (m : MatchArm) : Option Expr := match m with | .mk _ g _ _ => g
def body (m : MatchArm) : Expr := match m with | .mk _ _ b _ => b
def span (m : MatchArm) : Span := match m with | .mk _ _ _ s => s

end MatchArm

instance : Nonempty Constraint :=
  ⟨⟨⟨#[], "_", Span.uninhabited⟩, #[], Span.uninhabited⟩⟩

/-- A binder on an instance declaration -/
inductive InstanceBinder where
  /-- Implicit type variable -/
  | typeVar (name : QualName) (kind : Expr) (span : Span)
  /-- Instance dictionary parameter -/
  | dictParam (name : Option QualName) (constraint : Constraint) (span : Span)
  deriving Repr

namespace InstanceBinder

def span : InstanceBinder → Span
  | .typeVar _ _ s => s
  | .dictParam _ _ s => s

end InstanceBinder

instance : Nonempty InstanceBinder :=
  ⟨.typeVar ⟨#[], "_", Span.uninhabited⟩
      (.var ⟨#[], "Type", Span.uninhabited⟩) Span.uninhabited⟩

/-- Attributes on declarations: @[inline], @[specialize], @[wired_in "role"] -/
structure Attribute where
  name : QualName
  args : Array Expr
  span : Span
  deriving Repr

structure DataCon where
  attrs : Array Attribute := #[]
  name : QualName
  fields : Array (Option QualName × Expr)
  /-- Full constructor type signature (for indexed data types).
      When present, `fields` should be empty and this contains the complete type. -/
  sig : Option Expr := none
  span : Span
  deriving Repr

/-- A record field: name :: Type -/
structure RecordField where
  name : Option QualName
  type_ : Expr
  binderInfo : Soma.Core.BinderInfo := .explicit
  quantity : Soma.Core.Quantity := .omega
  span : Span
  deriving Repr

/-- A method signature in a trait -/
structure MethodSig where
  name : QualName
  type_ : Expr
  span : Span
  deriving Repr

/-- A definition clause: | pat1 pat2 => body -/
structure DefClause where
  patterns : Array Pattern
  guard : Option Expr
  body : Expr
  span : Span
  deriving Repr

/-- A named definition parameter from the declaration header -/
structure DefParam where
  name : QualName
  type? : Option Expr
  isImplicit : Bool := false
  isInstance : Bool := false
  quantity? : Option Soma.Core.Quantity := none
  span : Span
  deriving Repr

/-- Top-level declarations -/
inductive Decl where
  /-- Function/value definition -/
  | def_ (attrs : Array Attribute) (name : QualName) (params : Array DefParam)
         (sig : Option Expr) (clauses : Array DefClause) (span : Span)

  /-- Theorem declaration -/
  | theorem_ (attrs : Array Attribute) (name : QualName) (params : Array DefParam)
             (sig : Option Expr) (clauses : Array DefClause) (span : Span)

  /-- Inductive type definition: inductive Option {a : Type} where ... -/
  | inductive (attrs : Array Attribute) (name : QualName) (params : Array TypeVarBinder)
         (constructors : Array DataCon) (kind : Option Expr) (span : Span)

  /-- Record definition: record Point where x : Int, y : Int -/
  | record (attrs : Array Attribute) (name : QualName) (params : Array TypeVarBinder)
           (con : QualName) (fields : Array RecordField) (span : Span)

  /-- Class definition -/
  | trait (attrs : Array Attribute) (name : QualName) (params : Array TypeVarBinder)
          (methods : Array MethodSig) (span : Span)

  /-- Instance definition -/
  | instance_ (instanceName : Option QualName) (binders : Array InstanceBinder)
              (traitName : QualName) (args : Array Expr)
              (methods : Array Decl) (span : Span)

  /-- Import declaration: use / pub use -/
  | use (isPublic : Bool) (path : QualName) (items : Array QualName) (span : Span)

  /-- Type abbreviation: abbrev Foo params = Type -/
  | abbrev (name : QualName) (params : Array QualName) (type_ : Expr) (span : Span)
  deriving Repr

instance : Nonempty Decl := ⟨.use false ⟨#[], "_", Span.uninhabited⟩ #[] Span.uninhabited⟩

namespace Decl

def span : Decl → Span
  | .def_ _ _ _ _ _ s => s
  | .theorem_ _ _ _ _ _ s => s
  | .inductive _ _ _ _ _ s => s
  | .record _ _ _ _ _ s => s
  | .trait _ _ _ _ s => s
  | .instance_ _ _ _ _ _ s => s
  | .use _ _ _ s => s
  | .abbrev _ _ _ s => s

/-- Get the name of a declaration (if it has one) -/
def name? : Decl → Option QualName
  | .def_ _ name _ _ _ _ => some name
  | .theorem_ _ name _ _ _ _ => some name
  | .inductive _ name _ _ _ _ => some name
  | .record _ name _ _ _ _ => some name
  | .trait _ name _ _ _ => some name
  | .instance_ instanceName _ _ _ _ _ => instanceName
  | .use _ _ _ _ => none
  | .abbrev name _ _ _ => some name

end Decl

/-- A complete module (source file) -/
structure Module where
  /-- Module name (derived from file path) -/
  name : String
  /-- All declarations in order -/
  decls : Array Decl
  /-- Span covering the entire file -/
  span : Span
  deriving Repr

namespace Pretty

/-- Indent a string by n spaces -/
def indent (n : Nat) (s : String) : String :=
  let pre := String.ofList (List.replicate n ' ')
  s.splitOn "\n" |>.map (pre ++ ·) |> String.intercalate "\n"

/-- Pretty print a QualName -/
def ppName (n : QualName) : String := n.name

/-- Pretty print a list of Names -/
def ppNames (ns : Array QualName) : String :=
  ns.toList.map ppName |> String.intercalate " "

/-- Pretty print a Literal -/
def ppLiteral : Literal → String
  | .int v _ => toString v
  | .string s _ => s!"\"{s}\""
  | .bool b _ => if b then "true" else "false"

mutual

/-- Pretty print a Pattern -/
partial def ppPattern : Pattern → String
  | .var n => n.name
  | .wildcard _ => "_"
  | .lit l => ppLiteral l
  | .con n args _ =>
      if args.isEmpty then n.name
      else s!"{n.name} {args.toList.map ppPattern |> String.intercalate " "}"
  | .tuple elems _ =>
      s!"({elems.toList.map ppPattern |> String.intercalate ", "})"
  | .list elems _ =>
      s!"[{elems.toList.map ppPattern |> String.intercalate ", "}]"
  | .cons h t _ => s!"({ppPattern h}:{ppPattern t})"
  | .parens p _ => s!"({ppPattern p})"
  | .typed p ty _ => s!"({ppPattern p} :: {ppExpr ty})"
  | .variant label arg _ =>
      match arg with
      | some p => s!".{label.name} {ppPattern p}"
      | none => s!".{label.name}"

/-- Pretty print a TypeVarBinder -/
partial def ppTypeVarBinder : TypeVarBinder → String
  | .mk n (some k) => s!"({n.name} :: {ppExpr k})"
  | .mk n none => n.name
  | .constraint name? cstr =>
      let argsStr :=
        if cstr.args.isEmpty then ""
        else " " ++ (cstr.args.toList.map ppExpr |> String.intercalate " ")
      let body := cstr.className.name ++ argsStr
      match name? with
      | some n => "{{" ++ n.name ++ " : " ++ body ++ "}}"
      | none   => "{{" ++ body ++ "}}"

/-- Pretty print an array of TypeVarBinders -/
partial def ppTypeVarBinders (vs : Array TypeVarBinder) : String :=
  vs.toList.map ppTypeVarBinder |> String.intercalate " "

/-- Pretty print an Expr -/
partial def ppExpr : Expr → String
  | .var n => n.name
  | .con n => n.name
  | .parens e _ => s!"({ppExpr e})"
  | .app fn arg _ => s!"{ppExpr fn} {ppExprAtom arg}"
  | .tuple elems _ =>
      s!"({elems.toList.map ppExpr |> String.intercalate ", "})"
  | .list elems _ =>
      s!"[{elems.toList.map ppExpr |> String.intercalate ", "}]"
  | .lit l => ppLiteral l
  | .infix op l r _ => s!"{ppExprAtom l} {op.value} {ppExprAtom r}"
  | .lambda params body _ =>
      let ps := params.toList.map fun (n, ty) =>
        match ty with
        | some t => s!"({n.name} :: {ppExpr t})"
        | none => n.name
      s!"\\{ps |> String.intercalate " "} -> {ppExpr body}"
  | .if_ c t e _ => s!"if {ppExpr c} then {ppExpr t} else {ppExpr e}"
  | .case scruts arms _ =>
      let scrutStr := scruts.toList.map ppExpr |> String.intercalate ", "
      let armsStr := arms.toList.map ppMatchArm |> String.intercalate "\n"
      s!"case {scrutStr} of\n{indent 2 armsStr}"
  | .record fields _ =>
      let fs := fields.toList.map fun (n, e) => s!"{n.name} = {ppExpr e}"
      "{ " ++ (fs |> String.intercalate ", ") ++ " }"
  | .recordUpdate base updates _ =>
      let us := updates.toList.map fun (n, e) => s!"{n.name} = {ppExpr e}"
      "{ " ++ ppExpr base ++ " | " ++ (us |> String.intercalate ", ") ++ " }"
  | .fieldAccess e f _ => s!"{ppExprAtom e}.{f.name}"
  | .projection t f _ => s!"{t.name}.{f.name}"
  | .typeAnnot e t _ => s!"{ppExprAtom e} :: {ppExpr t}"
  | .typeApp arg _ => match arg with
    | .type ty => s!"@{ppExpr ty}"
    | .label name => s!"@{name.name}"
  | .composeBlock stmts final_ _ =>
      let stmtStrs := stmts.map fun
        | .expr action _ => ppExpr action
        | .let_ name value _ => s!"let {name.name} = {ppExpr value}"
        | .bind_ name action _ => s!"bind {name.name} <- {ppExpr action}"
      let body := String.intercalate "; " stmtStrs.toList
      s!"compose ( {body}; {ppExpr final_} )"
  | .variant label arg _ =>
      match arg with
      | some e => s!".{label.name} {ppExprAtom e}"
      | none => s!".{label.name}"
  | .arrow from_ to _ => s!"{ppExprAtom from_} -> {ppExpr to}"
  | .pi qty binder name domain codomain _ =>
      let qtyStr := match qty with
        | .zero => "0 "
        | .one => "1 "
        | .omega => ""
      let (lparen, rparen) := match binder with
        | .implicit => ("{", "}")
        | .instance_ => ("{{", "}}")
        | .strictImplicit => ("{", "}")
        | .explicit => ("(", ")")
      s!"{lparen}{qtyStr}{name.name} : {ppExpr domain}{rparen} -> {ppExpr codomain}"
  | .sigma qty name fst snd _ =>
      let qtyStr := match qty with
        | .zero => "0 "
        | .one => "1 "
        | .omega => ""
      s!"({qtyStr}{name.name} : {ppExpr fst}) × {ppExpr snd}"
  | .forall_ vars body _ =>
      s!"forall {vars.toList.map ppTypeVarBinder |> String.intercalate " "}. {ppExpr body}"
  | .recordTy fields tail _ =>
      let fieldsStr := fields.toList.map (fun (n, t) => s!"{n.name} :: {ppExpr t}")
        |> String.intercalate ", "
      match tail with
      | some name => "{ " ++ fieldsStr ++ " | " ++ name.name ++ " }"
      | none => "{ " ++ fieldsStr ++ " }"
  | .variantTy cases tail _ =>
      let casesStr := cases.toList.map (fun (n, t) => s!"{n.name} :: {ppExpr t}")
        |> String.intercalate " | "
      match tail with
      | some name => "< " ++ casesStr ++ " | " ++ name.name ++ " >"
      | none => "< " ++ casesStr ++ " >"
  | .listTy elem _ => s!"[{ppExpr elem}]"

/-- Atomic-context pretty printing (adds parens around composite exprs) -/
partial def ppExprAtom : Expr → String
  | .var n => n.name
  | .con n => n.name
  | .lit l => ppLiteral l
  | .parens e _ => s!"({ppExpr e})"
  | .tuple elems _ => s!"({elems.toList.map ppExpr |> String.intercalate ", "})"
  | .list elems _ => s!"[{elems.toList.map ppExpr |> String.intercalate ", "}]"
  | e => s!"({ppExpr e})"

/-- Pretty print a MatchArm -/
partial def ppMatchArm (arm : MatchArm) : String :=
  let pats := arm.patterns.toList.map ppPattern |> String.intercalate " "
  let guardStr := match arm.guard with
    | some g => s!" if {ppExpr g}"
    | none => ""
  s!"| {pats}{guardStr} => {ppExpr arm.body}"

end

/-- Pretty print a Constraint -/
def ppConstraint (c : Constraint) : String :=
  if c.args.isEmpty then c.className.name
  else s!"{c.className.name} {c.args.toList.map ppExpr |> String.intercalate " "}"

/-- Pretty print a DefClause -/
def ppDefClause (clause : DefClause) : String :=
  let pats := clause.patterns.toList.map ppPattern |> String.intercalate " "
  let guardStr := match clause.guard with
    | some g => s!" if {ppExpr g}"
    | none => ""
  s!"| {pats}{guardStr} => {ppExpr clause.body}"

/-- Pretty print a DataCon -/
def ppDataCon (con : DataCon) : String :=
  let fieldsStr := con.fields.toList.map (fun (optName, ty) =>
    match optName with
    | some n => s!"{n.name} :: {ppExpr ty}"
    | none => ppExpr ty
  ) |> String.intercalate ", "
  if fieldsStr.isEmpty then s!"| {con.name.name}"
  else s!"| {con.name.name} " ++ "{ " ++ fieldsStr ++ " }"

/-- Pretty print a MethodSig -/
def ppMethodSig (m : MethodSig) : String :=
  s!"def {m.name.name} :: {ppExpr m.type_}"

/-- Pretty print a Decl -/
partial def ppDecl : Decl → String
  | .def_ attrs name params sig clauses _ =>
      let attrStr := if attrs.isEmpty then ""
        else s!"@[{attrs.toList.map (·.name.name) |> String.intercalate ", "}]\n"
      let paramsStr := if params.isEmpty then "" else
        let ppParam (p : DefParam) := match p.type? with
          | some ty => s!"({p.name.name} : {ppExpr ty})"
          | none => p.name.name
        " " ++ (params.toList.map ppParam |> String.intercalate " ")
      let sigStr := match sig with
        | some t => s!" :: {ppExpr t}"
        | none => ""
      let clausesStr := clauses.toList.map ppDefClause |> String.intercalate "\n"
      if clauses.isEmpty then
        s!"{attrStr}def {name.name}{paramsStr}{sigStr}"
      else
        s!"{attrStr}def {name.name}{paramsStr}{sigStr}\n{indent 2 clausesStr}"

  | .theorem_ attrs name params sig clauses _ =>
      let attrStr := if attrs.isEmpty then ""
        else s!"@[{attrs.toList.map (·.name.name) |> String.intercalate ", "}]\n"
      let paramsStr := if params.isEmpty then "" else
        let ppParam (p : DefParam) := match p.type? with
          | some ty => s!"({p.name.name} : {ppExpr ty})"
          | none => p.name.name
        " " ++ (params.toList.map ppParam |> String.intercalate " ")
      let sigStr := match sig with
        | some t => s!" :: {ppExpr t}"
        | none => ""
      let clausesStr := clauses.toList.map ppDefClause |> String.intercalate "\n"
      if clauses.isEmpty then
        s!"{attrStr}theorem {name.name}{paramsStr}{sigStr}"
      else
        s!"{attrStr}theorem {name.name}{paramsStr}{sigStr}\n{indent 2 clausesStr}"

  | .inductive attrs name params cons kind _ =>
      let attrStr := if attrs.isEmpty then ""
        else s!"@[{attrs.toList.map (·.name.name) |> String.intercalate ", "}]\n"
      let paramsStr := if params.isEmpty then "" else s!" {ppTypeVarBinders params}"
      let kindStr := match kind with
        | some k => s!" :: {ppExpr k}"
        | none => ""
      let consStr := cons.toList.map ppDataCon |> String.intercalate "\n"
      s!"{attrStr}inductive {name.name}{paramsStr}{kindStr} where\n{indent 2 consStr}"

  | .record attrs name params con fields _ =>
      let attrStr := if attrs.isEmpty then ""
        else s!"@[{attrs.toList.map (·.name.name) |> String.intercalate ", "}]\n"
      let paramsStr := if params.isEmpty then "" else s!" {ppTypeVarBinders params}"
      let qtyStr (q : Quantity) : String :=
        match q with | .omega => "" | .zero => "0 " | .one => "1 "
      let wrap (bi : BinderInfo) (inner : String) : String :=
        match bi with
        | .explicit => s!"({inner})"
        | .implicit => s!"\{{inner}}"
        | .instance_ => s!"\{\{{inner}}}"
        | .strictImplicit => s!"\{\{{inner}}}"
      let fieldsStr := fields.toList.map (fun f =>
        let nameStr := match f.name with | some n => s!"{n.name} :: " | none => ""
        wrap f.binderInfo s!"{qtyStr f.quantity}{nameStr}{ppExpr f.type_}"
      ) |> String.intercalate ", "
      s!"{attrStr}record " ++ name.name ++ paramsStr ++ " = " ++ con.name ++ " { " ++ fieldsStr ++ " }"

  | .trait attrs name params methods _ =>
      let attrStr := if attrs.isEmpty then ""
        else s!"@[{attrs.toList.map (·.name.name) |> String.intercalate ", "}]\n"
      let paramsStr := if params.isEmpty then "" else s!" {ppTypeVarBinders params}"
      let methodsStr := methods.toList.map ppMethodSig |> String.intercalate "\n"
      s!"{attrStr}trait {name.name}{paramsStr} where\n{indent 2 methodsStr}"

  | .instance_ instanceName binders traitName args methods _ =>
      let nameStr := match instanceName with
        | some n => s!"{n.name} : "
        | none => ""
      let bindersStr := if binders.isEmpty then "" else
        let bs := binders.toList.map fun
          | .typeVar name kind _ =>
            "{" ++ name.name ++ " : " ++ ppExpr kind ++ "}"
          | .dictParam name constraint _ =>
            let nameStr := match name with
              | some n => s!"{n.name} : "
              | none => ""
            "{{" ++ nameStr ++ ppConstraint constraint ++ "}}"
        (bs |> String.intercalate " ") ++ " "
      let argsStr := args.toList.map ppExpr |> String.intercalate " "
      let methodsStr := methods.toList.map ppDecl |> String.intercalate "\n\n"
      s!"instance {bindersStr}{nameStr}: {traitName.name} {argsStr} where\n{indent 2 methodsStr}"

  | .use isPublic path items _ =>
      let pubStr := if isPublic then "pub " else ""
      let itemsStr := if items.isEmpty then ""
        else "::{" ++ (items.toList.map (·.name) |> String.intercalate ", ") ++ "}"
      s!"{pubStr}use {path}{itemsStr}"

  | .abbrev name params ty _ =>
      let paramsStr := if params.isEmpty then "" else s!" {ppNames params}"
      s!"abbrev {name.name}{paramsStr} = {ppExpr ty}"

/-- Pretty print a Module -/
def ppModule (m : Module) : String :=
  let declsStr := m.decls.toList.map ppDecl |> String.intercalate "\n\n"
  s!"-- Module: {m.name}\n\n{declsStr}"

end Pretty

end Soma.Syntax
