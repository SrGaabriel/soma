import Soma.Syntax.Source
import Soma.Core.Quantity
import Std.Data.HashSet

namespace Soma.Syntax

open Soma.Core (Quantity)

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

/-! ## Patterns, Type Expressions, and Type Variable Binders (mutually recursive) -/

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
  | typed (pat : Pattern) (ty : TypeExpr) (span : Span)
  /-- Variant pattern: .Ok x -/
  | variant (label : QualName) (arg : Option Pattern) (span : Span)

/-- A type variable binder, optionally with a type/kind annotation -/
inductive TypeVarBinder : Type where
  | mk (name : QualName) (kind : Option TypeExpr) : TypeVarBinder

/-- Type expressions -/
inductive TypeExpr : Type where
  /-- Type variable: a, b -/
  | var (name : QualName)
  /-- Type constructor: Int, String, Option -/
  | con (name : QualName)
  /-- Type application: Option a, Either e a -/
  | app (fn : TypeExpr) (arg : TypeExpr) (span : Span)
  /-- Function type: a -> b -/
  | arrow (from_ : TypeExpr) (to : TypeExpr) (span : Span)
  /-- Tuple type: (a, b, c) -/
  | tuple (elements : Array TypeExpr) (span : Span)
  /-- List type: [a] -/
  | list (elem : TypeExpr) (span : Span)
  /-- Universal quantification: forall a (r :: Row). Type -/
  | forall_ (vars : Array TypeVarBinder) (body : TypeExpr) (span : Span)
  /-- Constrained type: Type with (Constraint1, Constraint2) -/
  | constrained (constraints : Array (QualName × Array TypeExpr × Span)) (body : TypeExpr) (span : Span)
  /-- Parenthesized type -/
  | parens (inner : TypeExpr) (span : Span)
  /-- Kind annotation: Type :: * -> * -/
  | kinded (ty : TypeExpr) (kind : TypeExpr) (span : Span)
  /-- Record type: { x :: Int, y :: Bool } or { x :: Int | r } -/
  | record (fields : Array (QualName × TypeExpr)) (tail : Option QualName) (span : Span)
  /-- Variant type: < Ok :: Int | Err :: String > or < Ok :: Int | r > -/
  | variant (cases : Array (QualName × TypeExpr)) (tail : Option QualName) (span : Span)
  /-- Dependent function type (Pi): (q x : A) -> B -/
  | pi (qty : Quantity) (name : QualName) (domain : TypeExpr) (codomain : TypeExpr) (span : Span)
  /-- Dependent pair type (Sigma): (x : A) × B -/
  | sigma (qty : Quantity) (name : QualName) (fst : TypeExpr) (snd : TypeExpr) (span : Span)
  /-- Implicit parameter type: {{x : A}} -> B -/
  | implicit (name : Option QualName) (domain : TypeExpr) (codomain : TypeExpr) (span : Span)

end

namespace TypeVarBinder

def name : TypeVarBinder → QualName
  | .mk n _ => n

def kind : TypeVarBinder → Option TypeExpr
  | .mk _ k => k

end TypeVarBinder

instance : Inhabited TypeVarBinder := ⟨.mk ⟨#[], "_", Span.uninhabited⟩ none⟩

namespace TypeExpr

/-- Collect all type variable names from a TypeExpr.
    Returns a HashSet of all variable names appearing in the type. -/
partial def collectVarNames (ty : TypeExpr) : Std.HashSet String :=
  go ty {}
where
  go (ty : TypeExpr) (acc : Std.HashSet String) : Std.HashSet String :=
    match ty with
    | .var name => acc.insert name.name
    | .con _ => acc
    | .arrow from_ to _ => go to (go from_ acc)
    | .tuple elems _ => elems.foldl (fun a e => go e a) acc
    | .list elem _ => go elem acc
    | .app fn arg _ => go arg (go fn acc)
    | .forall_ _ body _ => go body acc
    | .constrained _ body _ => go body acc
    | .parens inner _ => go inner acc
    | .kinded inner _ _ => go inner acc
    | .record fields tail _ =>
      let acc' := fields.foldl (fun a (_, t) => go t a) acc
      match tail with
      | some tailName => acc'.insert tailName.name
      | none => acc'
    | .variant cases tail _ =>
      let acc' := cases.foldl (fun a (_, t) => go t a) acc
      match tail with
      | some tailName => acc'.insert tailName.name
      | none => acc'
    | .pi _ _ domain codomain _ => go codomain (go domain acc)
    | .sigma _ _ fst snd _ => go snd (go fst acc)
    | .implicit _ domain codomain _ => go codomain (go domain acc)

end TypeExpr

-- Nonempty instances (needed for partial recursive functions)
instance : Nonempty Pattern := ⟨.wildcard Span.uninhabited⟩
instance : Nonempty TypeExpr := ⟨.var ⟨#[], "_", Span.uninhabited⟩⟩
instance : Nonempty TypeVarBinder := ⟨.mk ⟨#[], "_", Span.uninhabited⟩ none⟩

-- Manually derive Repr for mutually recursive types
mutual

partial def Pattern.repr' (p : Pattern) (_ : Nat) : Std.Format :=
  match p with
  | .var name => f!"Pattern.var {Repr.reprPrec name 0}"
  | .wildcard span => f!"Pattern.wildcard {Repr.reprPrec span 0}"
  | .lit lit => f!"Pattern.lit {Repr.reprPrec lit 0}"
  | .con name args span => f!"Pattern.con {Repr.reprPrec name 0} #[...{args.size}] {Repr.reprPrec span 0}"
  | .tuple elems span => f!"Pattern.tuple #[...{elems.size}] {Repr.reprPrec span 0}"
  | .list elems span => f!"Pattern.list #[...{elems.size}] {Repr.reprPrec span 0}"
  | .cons h t span => f!"Pattern.cons ({Pattern.repr' h 0}) ({Pattern.repr' t 0}) {Repr.reprPrec span 0}"
  | .parens inner span => f!"Pattern.parens ({Pattern.repr' inner 0}) {Repr.reprPrec span 0}"
  | .typed pat ty span => f!"Pattern.typed ({Pattern.repr' pat 0}) ({TypeExpr.repr' ty 0}) {Repr.reprPrec span 0}"
  | .variant label arg span =>
      let argRepr := match arg with
        | some p => f!"some ({Pattern.repr' p 0})"
        | none => f!"none"
      f!"Pattern.variant {Repr.reprPrec label 0} {argRepr} {Repr.reprPrec span 0}"

partial def TypeExpr.repr' (t : TypeExpr) (_ : Nat) : Std.Format :=
  match t with
  | .var name => f!"TypeExpr.var {Repr.reprPrec name 0}"
  | .con name => f!"TypeExpr.con {Repr.reprPrec name 0}"
  | .app fn arg span => f!"TypeExpr.app ({TypeExpr.repr' fn 0}) ({TypeExpr.repr' arg 0}) {Repr.reprPrec span 0}"
  | .arrow from_ to span => f!"TypeExpr.arrow ({TypeExpr.repr' from_ 0}) ({TypeExpr.repr' to 0}) {Repr.reprPrec span 0}"
  | .tuple elems span => f!"TypeExpr.tuple #[...{elems.size}] {Repr.reprPrec span 0}"
  | .list elem span => f!"TypeExpr.list ({TypeExpr.repr' elem 0}) {Repr.reprPrec span 0}"
  | .forall_ vars body span => f!"TypeExpr.forall_ #[...{vars.size}] ({TypeExpr.repr' body 0}) {Repr.reprPrec span 0}"
  | .constrained cs body span => f!"TypeExpr.constrained #[...{cs.size}] ({TypeExpr.repr' body 0}) {Repr.reprPrec span 0}"
  | .parens inner span => f!"TypeExpr.parens ({TypeExpr.repr' inner 0}) {Repr.reprPrec span 0}"
  | .kinded ty kind span => f!"TypeExpr.kinded ({TypeExpr.repr' ty 0}) ({TypeExpr.repr' kind 0}) {Repr.reprPrec span 0}"
  | .record fields tail span => f!"TypeExpr.record #[...{fields.size}] {Repr.reprPrec tail 0} {Repr.reprPrec span 0}"
  | .variant cases tail span => f!"TypeExpr.variant #[...{cases.size}] {Repr.reprPrec tail 0} {Repr.reprPrec span 0}"
  | .pi qty name domain codomain span => f!"TypeExpr.pi {Repr.reprPrec qty 0} {Repr.reprPrec name 0} ({TypeExpr.repr' domain 0}) ({TypeExpr.repr' codomain 0}) {Repr.reprPrec span 0}"
  | .sigma qty name fst snd span => f!"TypeExpr.sigma {Repr.reprPrec qty 0} {Repr.reprPrec name 0} ({TypeExpr.repr' fst 0}) ({TypeExpr.repr' snd 0}) {Repr.reprPrec span 0}"
  | .implicit name domain codomain span => f!"TypeExpr.implicit {Repr.reprPrec name 0} ({TypeExpr.repr' domain 0}) ({TypeExpr.repr' codomain 0}) {Repr.reprPrec span 0}"

end

instance : Repr Pattern := ⟨Pattern.repr'⟩
instance : Repr TypeExpr := ⟨TypeExpr.repr'⟩

instance : Repr TypeVarBinder where
  reprPrec v _ := f!"TypeVarBinder.mk {Repr.reprPrec v.name 0} {Repr.reprPrec v.kind 0}"

instance : BEq TypeVarBinder where
  beq a b := a.name == b.name

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

/-- Type class constraint: Show a, Functor f -/
structure Constraint where
  className : QualName
  args : Array TypeExpr
  span : Span
  deriving Repr

instance : Nonempty Constraint := ⟨⟨⟨#[], "_", Span.uninhabited⟩, #[], Span.uninhabited⟩⟩

/-- A binder on an instance declaration -/
inductive InstanceBinder where
  /-- Implicit type variable -/
  | typeVar (name : QualName) (kind : TypeExpr) (span : Span)
  /-- Instance dictionary parameter -/
  | dictParam (name : Option QualName) (constraint : Constraint) (span : Span)
  deriving Repr

namespace InstanceBinder

def span : InstanceBinder → Span
  | .typeVar _ _ s => s
  | .dictParam _ _ s => s

end InstanceBinder

instance : Nonempty InstanceBinder :=
  ⟨.typeVar ⟨#[], "_", Span.uninhabited⟩ (.var ⟨#[], "Type", Span.uninhabited⟩) Span.uninhabited⟩

namespace TypeExpr

def span : TypeExpr → Span
  | .var name => name.span
  | .con name => name.span
  | .app _ _ s => s
  | .arrow _ _ s => s
  | .tuple _ s => s
  | .list _ s => s
  | .forall_ _ _ s => s
  | .constrained _ _ s => s
  | .parens _ s => s
  | .kinded _ _ s => s
  | .record _ _ s => s
  | .variant _ _ s => s
  | .pi _ _ _ _ s => s
  | .sigma _ _ _ _ s => s
  | .implicit _ _ _ s => s

end TypeExpr

/-- Argument to an explicit type application -/
inductive TypeAppArg : Type where
  /-- A type expression: @Int -/
  | type (ty : TypeExpr)
  /-- A label literal: @fieldName -/
  | label (name : QualName)

namespace TypeAppArg

def span : TypeAppArg → Span
  | .type ty => ty.span
  | .label name => name.span

def repr' : TypeAppArg → Nat → Std.Format
  | .type ty, _ => f!"TypeAppArg.type ({TypeExpr.repr' ty 0})"
  | .label name, _ => f!"TypeAppArg.label {Repr.reprPrec name 0}"

end TypeAppArg

instance : Repr TypeAppArg := ⟨TypeAppArg.repr'⟩

namespace TypeExpr

/-- Get all free type variables in this type -/
partial def freeVars : TypeExpr → Array QualName
  | .var name => #[name]
  | .con _ => #[]
  | .app fn arg _ => fn.freeVars ++ arg.freeVars
  | .arrow from_ to _ => from_.freeVars ++ to.freeVars
  | .tuple elems _ => elems.foldl (fun acc t => acc ++ t.freeVars) #[]
  | .list elem _ => elem.freeVars
  | .forall_ vars body _ =>
      let bound := vars.map (·.name.name)
      body.freeVars.filter fun v => !bound.contains v.name
  | .constrained _ body _ => body.freeVars
  | .parens inner _ => inner.freeVars
  | .kinded ty _ _ => ty.freeVars
  | .record fields tail _ =>
      let fieldVars := fields.foldl (fun acc (_, t) => acc ++ t.freeVars) #[]
      match tail with
      | some name => fieldVars ++ #[name]
      | none => fieldVars
  | .variant cases tail _ =>
      let caseVars := cases.foldl (fun acc (_, t) => acc ++ t.freeVars) #[]
      match tail with
      | some name => caseVars ++ #[name]
      | none => caseVars
  | .pi _ name domain codomain _ =>
      -- The bound variable is not free in the codomain
      domain.freeVars ++ (codomain.freeVars.filter fun v => v.name != name.name)
  | .sigma _ name fst snd _ =>
      -- The bound variable is not free in the second component
      fst.freeVars ++ (snd.freeVars.filter fun v => v.name != name.name)
  | .implicit name domain codomain _ =>
      let codomainVars := match name with
        | some n => codomain.freeVars.filter fun v => v.name != n.name
        | none => codomain.freeVars
      domain.freeVars ++ codomainVars

end TypeExpr

/-! ## Expressions -/

-- Forward declaration for MatchArm - use mutual block
mutual

/-- A match arm: | pattern => body or | pattern if guard => body -/
inductive MatchArm where
  | mk (patterns : Array Pattern) (guard : Option Expr) (body : Expr) (span : Span)

/-- A statement in a compose block -/
inductive ComposeStmt where
  /-- Expression statement: `action` that desugars to `action >> rest` -/
  | expr (action : Expr) (span : Span)
  /-- Let binding: `let x = value` that desugars to `case value of | x -> rest` -/
  | let_ (name : QualName) (value : Expr) (span : Span)
  /-- Monadic bind: `bind x <- action` that desugars to `action >>= (\x -> rest)` -/
  | bind_ (name : QualName) (action : Expr) (span : Span)

/-- Expressions - the core of the AST -/
inductive Expr where
  /-- Variable reference: name -/
  | var (name : QualName)
  /-- Literal: 42, "hello", true -/
  | lit (lit : Literal)
  /-- Function application: f x -/
  | app (fn : Expr) (arg : Expr) (span : Span)
  /-- Infix operator application: a + b -/
  | infix (op : OpName) (left : Expr) (right : Expr) (span : Span)
  /-- Lambda expression: \x y -> body -/
  | lambda (params : Array (QualName × Option TypeExpr)) (body : Expr) (span : Span)
  /-- If expression: if cond then e1 else e2 -/
  | if_ (cond : Expr) (then_ : Expr) (else_ : Expr) (span : Span)
  /-- Case expression: case e of | pat => body ... -/
  | case (scrutinees : Array Expr) (arms : Array MatchArm) (span : Span)
  /-- Tuple: (a, b, c) -/
  | tuple (elements : Array Expr) (span : Span)
  /-- List literal: [1, 2, 3] -/
  | list (elements : Array Expr) (span : Span)
  /-- Record literal: { field1 = val1, field2 = val2 } -/
  | record (fields : Array (QualName × Expr)) (span : Span)
  /-- Record update: { baseExpr | field1 = val1, field2 = val2 } -/
  | recordUpdate (base : Expr) (updates : Array (QualName × Expr)) (span : Span)
  /-- Field access: expr.field -/
  | fieldAccess (expr : Expr) (field : QualName) (span : Span)
  /-- Projection function: Type.field (first-class accessor) -/
  | projection (typeName : QualName) (fieldName : QualName) (span : Span)
  /-- Parenthesized expression -/
  | parens (inner : Expr) (span : Span)
  /-- Type annotation: expr :: Type -/
  | typeAnnot (expr : Expr) (type_ : TypeExpr) (span : Span)
  /-- Explicit type application: @Type or @label -/
  | typeApp (typeArg : TypeAppArg) (span : Span)
  /-- Compose block -/
  | composeBlock (stmts : Array ComposeStmt) (final_ : Expr) (span : Span)
  /-- Variant injection: .Ok value -/
  | variant (label : QualName) (arg : Option Expr) (span : Span)

end

-- Derive Repr after mutual block
deriving instance Repr for ComposeStmt
deriving instance Repr for MatchArm
deriving instance Repr for Expr

-- Inhabited instances for array indexing, should never be used in practice
instance : Inhabited ComposeStmt := ⟨.expr (.var ⟨#[], "_", Span.uninhabited⟩) Span.uninhabited⟩
instance : Inhabited Expr := ⟨.var ⟨#[], "_", Span.uninhabited⟩⟩
instance : Inhabited MatchArm := ⟨.mk #[] none (.var ⟨#[], "_", Span.uninhabited⟩) Span.uninhabited⟩

namespace MatchArm

def patterns (m : MatchArm) : Array Pattern := match m with | .mk ps _ _ _ => ps
def guard (m : MatchArm) : Option Expr := match m with | .mk _ g _ _ => g
def body (m : MatchArm) : Expr := match m with | .mk _ _ b _ => b
def span (m : MatchArm) : Span := match m with | .mk _ _ _ s => s

end MatchArm

namespace Expr

def span : Expr → Span
  | .var name => name.span
  | .lit l => l.span
  | .app _ _ s => s
  | .infix _ _ _ s => s
  | .lambda _ _ s => s
  | .if_ _ _ _ s => s
  | .case _ _ s => s
  | .tuple _ s => s
  | .list _ s => s
  | .record _ s => s
  | .recordUpdate _ _ s => s
  | .fieldAccess _ _ s => s
  | .projection _ _ s => s
  | .parens _ s => s
  | .typeAnnot _ _ s => s
  | .typeApp _ s => s
  | .composeBlock _ _ s => s
  | .variant _ _ s => s

end Expr

/-- Attributes on declarations: @[inline], @[specialize], @[wired_in "role"] -/
structure Attribute where
  name : QualName
  args : Array Expr
  span : Span
  deriving Repr

/-- A data constructor: | ConName field1 :: T1 field2 :: T2
    For indexed types, includes a full type signature:
    | Cons :: a -> Vec n a -> Vec (n + 1) a -/
structure DataCon where
  attrs : Array Attribute := #[]
  name : QualName
  fields : Array (Option QualName × TypeExpr)  -- Named or positional fields (for simple constructors)
  /-- Full constructor type signature (for indexed data types).
      When present, `fields` should be empty and this contains the complete type. -/
  sig : Option TypeExpr := none
  span : Span
  deriving Repr

/-- A record field: name :: Type -/
structure RecordField where
  name : Option QualName
  type_ : TypeExpr
  span : Span
  deriving Repr

/-- A method signature in a trait -/
structure MethodSig where
  name : QualName
  type_ : TypeExpr
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
  type? : Option TypeExpr
  isImplicit : Bool := false
  span : Span
  deriving Repr

/-- Top-level declarations -/
inductive Decl where
  /-- Function/value definition -/
  | def_ (attrs : Array Attribute) (name : QualName) (params : Array DefParam) (sig : Option TypeExpr)
         (clauses : Array DefClause) (span : Span)

  /-- Inductive type definition: inductive Option {a : Type} where ... -/
  | inductive (attrs : Array Attribute) (name : QualName) (params : Array TypeVarBinder)
         (constructors : Array DataCon) (kind : Option TypeExpr) (span : Span)

  /-- Record definition: record Point where x : Int, y : Int -/
  | record (attrs : Array Attribute) (name : QualName) (params : Array TypeVarBinder)
           (con : QualName) (fields : Array RecordField) (span : Span)

  /-- Trait definition -/
  | trait (attrs : Array Attribute) (name : QualName) (params : Array TypeVarBinder)
          (constraints : Array Constraint) (methods : Array MethodSig) (span : Span)

  /-- Instance definition -/
  | instance_ (instanceName : Option QualName) (binders : Array InstanceBinder)
              (traitName : QualName) (args : Array TypeExpr)
              (methods : Array Decl) (span : Span)

  /-- Import declaration: use / pub use -/
  | use (isPublic : Bool) (path : QualName) (items : Array QualName) (span : Span)

  /-- Type abbreviation: abbrev Foo params = Type -/
  | abbrev (name : QualName) (params : Array QualName) (type_ : TypeExpr) (span : Span)
  deriving Repr

instance : Nonempty Decl := ⟨.use false ⟨#[], "_", Span.uninhabited⟩ #[] Span.uninhabited⟩

namespace Decl

def span : Decl → Span
  | .def_ _ _ _ _ _ s => s
  | .inductive _ _ _ _ _ s => s
  | .record _ _ _ _ _ s => s
  | .trait _ _ _ _ _ s => s
  | .instance_ _ _ _ _ _ s => s
  | .use _ _ _ s => s
  | .abbrev _ _ _ s => s

/-- Get the name of a declaration (if it has one) -/
def name? : Decl → Option QualName
  | .def_ _ name _ _ _ _ => some name
  | .inductive _ name _ _ _ _ => some name
  | .record _ name _ _ _ _ => some name
  | .trait _ name _ _ _ _ => some name
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
  | .typed p ty _ => s!"({ppPattern p} :: {ppTypeExpr ty})"
  | .variant label arg _ =>
      match arg with
      | some p => s!".{label.name} {ppPattern p}"
      | none => s!".{label.name}"

/-- Pretty print a TypeVarBinder -/
partial def ppTypeVarBinder (v : TypeVarBinder) : String := match v.kind with
  | some k => s!"({v.name.name} :: {ppTypeExpr k})"
  | none => v.name.name

/-- Pretty print an array of TypeVarBinders -/
partial def ppTypeVarBinders (vs : Array TypeVarBinder) : String :=
  vs.toList.map ppTypeVarBinder |> String.intercalate " "

/-- Pretty print a TypeExpr -/
partial def ppTypeExpr : TypeExpr → String
  | .var n => n.name
  | .con n => n.name
  | .app fn arg _ => s!"{ppTypeExpr fn} {ppTypeAtom arg}"
  | .arrow from_ to _ => s!"{ppTypeAtom from_} -> {ppTypeExpr to}"
  | .tuple elems _ =>
      s!"({elems.toList.map ppTypeExpr |> String.intercalate ", "})"
  | .list elem _ => s!"[{ppTypeExpr elem}]"
  | .forall_ vars body _ =>
      s!"forall {vars.toList.map ppTypeVarBinder |> String.intercalate " "}. {ppTypeExpr body}"
  | .constrained cs body _ =>
      let csStr := cs.toList.map (fun (n, args, _) =>
        if args.isEmpty then n.name
        else s!"{n.name} {args.toList.map ppTypeExpr |> String.intercalate " "}"
      ) |> String.intercalate ", "
      s!"{ppTypeExpr body} with ({csStr})"
  | .parens t _ => s!"({ppTypeExpr t})"
  | .kinded t k _ => s!"{ppTypeExpr t} :: {ppTypeExpr k}"
  | .record fields tail _ =>
      let fieldsStr := fields.toList.map (fun (n, t) => s!"{n.name} :: {ppTypeExpr t}") |> String.intercalate ", "
      match tail with
      | some name => "{ " ++ fieldsStr ++ " | " ++ name.name ++ " }"
      | none => "{ " ++ fieldsStr ++ " }"
  | .variant cases tail _ =>
      let casesStr := cases.toList.map (fun (n, t) => s!"{n.name} :: {ppTypeExpr t}") |> String.intercalate " | "
      match tail with
      | some name => "< " ++ casesStr ++ " | " ++ name.name ++ " >"
      | none => "< " ++ casesStr ++ " >"
  | .pi qty name domain codomain _ =>
      let qtyStr := match qty with
        | .zero => "0 "
        | .one => "1 "
        | .omega => ""
      s!"({qtyStr}{name.name} : {ppTypeExpr domain}) -> {ppTypeExpr codomain}"
  | .sigma qty name fst snd _ =>
      let qtyStr := match qty with
        | .zero => "0 "
        | .one => "1 "
        | .omega => ""
      s!"({qtyStr}{name.name} : {ppTypeExpr fst}) × {ppTypeExpr snd}"
  | .implicit name domain codomain _ =>
      let nameStr := match name with
        | some n => s!"{n.name} : "
        | none => ""
      "{{" ++ nameStr ++ ppTypeExpr domain ++ "}} -> " ++ ppTypeExpr codomain
where
  ppTypeAtom : TypeExpr → String
    | .var n => n.name
    | .con n => n.name
    | .tuple elems _ => s!"({elems.toList.map ppTypeExpr |> String.intercalate ", "})"
    | .list elem _ => s!"[{ppTypeExpr elem}]"
    | .parens t _ => s!"({ppTypeExpr t})"
    | .record fields tail _ =>
        let fieldsStr := fields.toList.map (fun (n, t) => s!"{n.name} :: {ppTypeExpr t}") |> String.intercalate ", "
        match tail with
        | some name => "{ " ++ fieldsStr ++ " | " ++ name.name ++ " }"
        | none => "{ " ++ fieldsStr ++ " }"
    | .variant cases tail _ =>
        let casesStr := cases.toList.map (fun (n, t) => s!"{n.name} :: {ppTypeExpr t}") |> String.intercalate " | "
        match tail with
        | some name => "< " ++ casesStr ++ " | " ++ name.name ++ " >"
        | none => "< " ++ casesStr ++ " >"
    | t => s!"({ppTypeExpr t})"

end

/-- Pretty print a Constraint -/
def ppConstraint (c : Constraint) : String :=
  if c.args.isEmpty then c.className.name
  else s!"{c.className.name} {c.args.toList.map ppTypeExpr |> String.intercalate " "}"

mutual

/-- Pretty print an Expr -/
partial def ppExpr : Expr → String
  | .var n => n.name
  | .lit l => ppLiteral l
  | .app fn arg _ => s!"{ppExpr fn} {ppExprAtom arg}"
  | .infix op l r _ => s!"{ppExprAtom l} {op.value} {ppExprAtom r}"
  | .lambda params body _ =>
      let ps := params.toList.map fun (n, ty) =>
        match ty with
        | some t => s!"({n.name} :: {ppTypeExpr t})"
        | none => n.name
      s!"\\{ps |> String.intercalate " "} -> {ppExpr body}"
  | .if_ c t e _ => s!"if {ppExpr c} then {ppExpr t} else {ppExpr e}"
  | .case scruts arms _ =>
      let scrutStr := scruts.toList.map ppExpr |> String.intercalate ", "
      let armsStr := arms.toList.map ppMatchArm |> String.intercalate "\n"
      s!"case {scrutStr} of\n{indent 2 armsStr}"
  | .tuple elems _ =>
      s!"({elems.toList.map ppExpr |> String.intercalate ", "})"
  | .list elems _ =>
      s!"[{elems.toList.map ppExpr |> String.intercalate ", "}]"
  | .record fields _ =>
      let fs := fields.toList.map fun (n, e) => s!"{n.name} = {ppExpr e}"
      "{ " ++ (fs |> String.intercalate ", ") ++ " }"
  | .recordUpdate base updates _ =>
      let us := updates.toList.map fun (n, e) => s!"{n.name} = {ppExpr e}"
      "{ " ++ ppExpr base ++ " | " ++ (us |> String.intercalate ", ") ++ " }"
  | .fieldAccess e f _ => s!"{ppExprAtom e}.{f.name}"
  | .projection typeName fieldName _ => s!"{typeName.name}.{fieldName.name}"
  | .parens e _ => s!"({ppExpr e})"
  | .typeAnnot e t _ => s!"{ppExprAtom e} :: {ppTypeExpr t}"
  | .typeApp arg _ => match arg with
    | .type ty => s!"@{ppTypeExpr ty}"
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
where
  ppExprAtom : Expr → String
    | .var n => n.name
    | .lit l => ppLiteral l
    | .tuple elems _ => s!"({elems.toList.map ppExpr |> String.intercalate ", "})"
    | .list elems _ => s!"[{elems.toList.map ppExpr |> String.intercalate ", "}]"
    | .parens e _ => s!"({ppExpr e})"
    | e => s!"({ppExpr e})"

/-- Pretty print a MatchArm -/
partial def ppMatchArm (arm : MatchArm) : String :=
  let pats := arm.patterns.toList.map ppPattern |> String.intercalate " "
  let guardStr := match arm.guard with
    | some g => s!" if {ppExpr g}"
    | none => ""
  s!"| {pats}{guardStr} => {ppExpr arm.body}"

end

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
    | some n => s!"{n.name} :: {ppTypeExpr ty}"
    | none => ppTypeExpr ty
  ) |> String.intercalate ", "
  if fieldsStr.isEmpty then s!"| {con.name.name}"
  else s!"| {con.name.name} " ++ "{ " ++ fieldsStr ++ " }"

/-- Pretty print a MethodSig -/
def ppMethodSig (m : MethodSig) : String :=
  s!"def {m.name.name} :: {ppTypeExpr m.type_}"

/-- Pretty print a Decl -/
partial def ppDecl : Decl → String
  | .def_ attrs name params sig clauses _ =>
      let attrStr := if attrs.isEmpty then ""
        else s!"@[{attrs.toList.map (·.name.name) |> String.intercalate ", "}]\n"
      let paramsStr := if params.isEmpty then "" else
        let ppParam (p : DefParam) := match p.type? with
          | some ty => s!"({p.name.name} : {ppTypeExpr ty})"
          | none => p.name.name
        " " ++ (params.toList.map ppParam |> String.intercalate " ")
      let sigStr := match sig with
        | some t => s!" :: {ppTypeExpr t}"
        | none => ""
      let clausesStr := clauses.toList.map ppDefClause |> String.intercalate "\n"
      if clauses.isEmpty then
        s!"{attrStr}def {name.name}{paramsStr}{sigStr}"
      else
        s!"{attrStr}def {name.name}{paramsStr}{sigStr}\n{indent 2 clausesStr}"

  | .inductive attrs name params cons kind _ =>
      let attrStr := if attrs.isEmpty then ""
        else s!"@[{attrs.toList.map (·.name.name) |> String.intercalate ", "}]\n"
      let paramsStr := if params.isEmpty then "" else s!" {ppTypeVarBinders params}"
      let kindStr := match kind with
        | some k => s!" :: {ppTypeExpr k}"
        | none => ""
      let consStr := cons.toList.map ppDataCon |> String.intercalate "\n"
      s!"{attrStr}inductive {name.name}{paramsStr}{kindStr} where\n{indent 2 consStr}"

  | .record attrs name params con fields _ =>
      let attrStr := if attrs.isEmpty then ""
        else s!"@[{attrs.toList.map (·.name.name) |> String.intercalate ", "}]\n"
      let paramsStr := if params.isEmpty then "" else s!" {ppTypeVarBinders params}"
      let fieldsStr := fields.toList.map (fun f =>
        match f.name with
        | some n => s!"{n.name} :: {ppTypeExpr f.type_}"
        | none => ppTypeExpr f.type_
      ) |> String.intercalate ", "
      s!"{attrStr}record " ++ name.name ++ paramsStr ++ " = " ++ con.name ++ " { " ++ fieldsStr ++ " }"

  | .trait attrs name params constraints methods _ =>
      let attrStr := if attrs.isEmpty then ""
        else s!"@[{attrs.toList.map (·.name.name) |> String.intercalate ", "}]\n"
      let paramsStr := if params.isEmpty then "" else s!" {ppTypeVarBinders params}"
      let consStr := if constraints.isEmpty then ""
        else s!" with ({constraints.toList.map ppConstraint |> String.intercalate ", "})"
      let methodsStr := methods.toList.map ppMethodSig |> String.intercalate "\n"
      s!"{attrStr}trait {name.name}{paramsStr}{consStr} where\n{indent 2 methodsStr}"

  | .instance_ instanceName binders traitName args methods _ =>
      let nameStr := match instanceName with
        | some n => s!"{n.name} : "
        | none => ""
      let bindersStr := if binders.isEmpty then "" else
        let bs := binders.toList.map fun
          | .typeVar name kind _ =>
            "{" ++ name.name ++ " : " ++ ppTypeExpr kind ++ "}"
          | .dictParam name constraint _ =>
            let nameStr := match name with
              | some n => s!"{n.name} : "
              | none => ""
            "{{" ++ nameStr ++ ppConstraint constraint ++ "}}"
        (bs |> String.intercalate " ") ++ " "
      let argsStr := args.toList.map ppTypeExpr |> String.intercalate " "
      let methodsStr := methods.toList.map ppDecl |> String.intercalate "\n\n"
      s!"instance {bindersStr}{nameStr}: {traitName.name} {argsStr} where\n{indent 2 methodsStr}"

  | .use isPublic path items _ =>
      let pubStr := if isPublic then "pub " else ""
      let itemsStr := if items.isEmpty then ""
        else "::{" ++ (items.toList.map (·.name) |> String.intercalate ", ") ++ "}"
      s!"{pubStr}use {path}{itemsStr}"

  | .abbrev name params ty _ =>
      let paramsStr := if params.isEmpty then "" else s!" {ppNames params}"
      s!"abbrev {name.name}{paramsStr} = {ppTypeExpr ty}"

/-- Pretty print a Module -/
def ppModule (m : Module) : String :=
  let declsStr := m.decls.toList.map ppDecl |> String.intercalate "\n\n"
  s!"-- Module: {m.name}\n\n{declsStr}"

end Pretty

end Soma.Syntax
