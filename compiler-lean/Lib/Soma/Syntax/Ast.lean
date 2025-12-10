import Soma.Syntax.Source

namespace Soma.Syntax

/-! ## Names -/

/-- A simple name (identifier) -/
structure Name where
  value : String
  span : Span
  deriving Repr, BEq, Inhabited

instance : ToString Name where
  toString n := n.value

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
    else String.intercalate "/" qn.path.toList ++ "." ++ qn.name

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

/-! ## Patterns and Type Expressions (mutually recursive) -/

mutual

/-- Patterns for destructuring in case expressions and function definitions -/
inductive Pattern : Type where
  /-- Variable pattern: x -/
  | var (name : Name)
  /-- Wildcard pattern: _ -/
  | wildcard (span : Span)
  /-- Literal pattern: 42, "hello", true -/
  | lit (lit : Literal)
  /-- Constructor pattern: Some x, Cons h t -/
  | con (name : Name) (args : Array Pattern) (span : Span)
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

/-- Type expressions -/
inductive TypeExpr : Type where
  /-- Type variable: a, b -/
  | var (name : Name)
  /-- Type constructor: Int, String, Option -/
  | con (name : Name)
  /-- Type application: Option a, Either e a -/
  | app (fn : TypeExpr) (arg : TypeExpr) (span : Span)
  /-- Function type: a -> b -/
  | arrow (from_ : TypeExpr) (to : TypeExpr) (span : Span)
  /-- Tuple type: (a, b, c) -/
  | tuple (elements : Array TypeExpr) (span : Span)
  /-- List type: [a] -/
  | list (elem : TypeExpr) (span : Span)
  /-- Universal quantification: forall a b. Type -/
  | forall_ (vars : Array Name) (body : TypeExpr) (span : Span)
  /-- Constrained type: Type with (Constraint1, Constraint2) -/
  | constrained (constraints : Array (Name × Array TypeExpr × Span)) (body : TypeExpr) (span : Span)
  /-- Parenthesized type -/
  | parens (inner : TypeExpr) (span : Span)
  /-- Kind annotation: Type :: * -> * -/
  | kinded (ty : TypeExpr) (kind : TypeExpr) (span : Span)

end

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

end

instance : Repr Pattern := ⟨Pattern.repr'⟩
instance : Repr TypeExpr := ⟨TypeExpr.repr'⟩

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

/-- Get all variable names bound by this pattern -/
partial def boundVars : Pattern → Array Name
  | .var name => #[name]
  | .wildcard _ => #[]
  | .lit _ => #[]
  | .con _ args _ => args.foldl (fun acc p => acc ++ p.boundVars) #[]
  | .tuple elems _ => elems.foldl (fun acc p => acc ++ p.boundVars) #[]
  | .list elems _ => elems.foldl (fun acc p => acc ++ p.boundVars) #[]
  | .cons h t _ => h.boundVars ++ t.boundVars
  | .parens inner _ => inner.boundVars
  | .typed pat _ _ => pat.boundVars

end Pattern

/-- Type class constraint: Show a, Functor f -/
structure Constraint where
  className : Name
  args : Array TypeExpr
  span : Span
  deriving Repr

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

/-- Get all free type variables in this type -/
partial def freeVars : TypeExpr → Array Name
  | .var name => #[name]
  | .con _ => #[]
  | .app fn arg _ => fn.freeVars ++ arg.freeVars
  | .arrow from_ to _ => from_.freeVars ++ to.freeVars
  | .tuple elems _ => elems.foldl (fun acc t => acc ++ t.freeVars) #[]
  | .list elem _ => elem.freeVars
  | .forall_ vars body _ =>
      let bound := vars.map (·.value)
      body.freeVars.filter fun v => !bound.contains v.value
  | .constrained _ body _ => body.freeVars
  | .parens inner _ => inner.freeVars
  | .kinded ty _ _ => ty.freeVars

end TypeExpr

/-! ## Expressions -/

-- Forward declaration for MatchArm - use mutual block
mutual

/-- A match arm: | pattern => body or | pattern if guard => body -/
inductive MatchArm where
  | mk (patterns : Array Pattern) (guard : Option Expr) (body : Expr) (span : Span)

/-- Expressions - the core of the AST -/
inductive Expr where
  /-- Variable reference: name -/
  | var (name : Name)
  /-- Literal: 42, "hello", true -/
  | lit (lit : Literal)
  /-- Function application: f x -/
  | app (fn : Expr) (arg : Expr) (span : Span)
  /-- Infix operator application: a + b -/
  | infix (op : OpName) (left : Expr) (right : Expr) (span : Span)
  /-- Lambda expression: \x y -> body -/
  | lambda (params : Array (Name × Option TypeExpr)) (body : Expr) (span : Span)
  /-- Let binding: let x = e1 in e2 -/
  | let_ (name : Name) (type_ : Option TypeExpr) (value : Expr) (body : Expr) (span : Span)
  /-- If expression: if cond then e1 else e2 -/
  | if_ (cond : Expr) (then_ : Expr) (else_ : Expr) (span : Span)
  /-- Case expression: case e of | pat => body ... -/
  | case (scrutinees : Array Expr) (arms : Array MatchArm) (span : Span)
  /-- Tuple: (a, b, c) -/
  | tuple (elements : Array Expr) (span : Span)
  /-- List literal: [1, 2, 3] -/
  | list (elements : Array Expr) (span : Span)
  /-- Record literal: { field1 = val1, field2 = val2 } -/
  | record (fields : Array (Name × Expr)) (span : Span)
  /-- Field access: expr.field -/
  | fieldAccess (expr : Expr) (field : Name) (span : Span)
  /-- Parenthesized expression -/
  | parens (inner : Expr) (span : Span)
  /-- Type annotation: expr :: Type -/
  | typeAnnot (expr : Expr) (type_ : TypeExpr) (span : Span)
  /-- Compose block: compose ... -/
  | compose (body : Expr) (span : Span)
  /-- Bind block: bind ... -/
  | bind (body : Expr) (span : Span)

end

-- Derive Repr after mutual block
deriving instance Repr for MatchArm
deriving instance Repr for Expr

-- Inhabited instances for array indexing, should never be used in practice
instance : Inhabited Expr := ⟨.var ⟨"_", Span.uninhabited⟩⟩
instance : Inhabited MatchArm := ⟨.mk #[] none (.var ⟨"_", Span.uninhabited⟩) Span.uninhabited⟩

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
  | .let_ _ _ _ _ s => s
  | .if_ _ _ _ s => s
  | .case _ _ s => s
  | .tuple _ s => s
  | .list _ s => s
  | .record _ s => s
  | .fieldAccess _ _ s => s
  | .parens _ s => s
  | .typeAnnot _ _ s => s
  | .compose _ s => s
  | .bind _ s => s

end Expr

/-- A data constructor: | ConName field1 :: T1 field2 :: T2 -/
structure DataCon where
  name : Name
  fields : Array (Option Name × TypeExpr)  -- Named or positional fields
  span : Span
  deriving Repr

/-- A struct field: name :: Type -/
structure StructField where
  name : Option Name
  type_ : TypeExpr
  span : Span
  deriving Repr

/-- A method signature in a trait -/
structure MethodSig where
  name : Name
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

/-- Attributes on declarations: @[inline], @[specialize] -/
structure Attribute where
  name : Name
  args : Array Expr  -- Optional arguments
  span : Span
  deriving Repr

/-- Top-level declarations -/
inductive Decl where
  /-- Function/value definition -/
  | def_ (attrs : Array Attribute) (name : Name) (sig : Option TypeExpr)
         (clauses : Array DefClause) (span : Span)

  /-- Data type definition: data Option a | Some value :: a | None -/
  | data (name : Name) (params : Array Name) (constructors : Array DataCon) (span : Span)

  /-- Struct definition: struct Path = Path String -/
  | struct (name : Name) (params : Array Name) (con : Name) (fields : Array StructField) (span : Span)

  /-- Trait definition -/
  | trait (name : Name) (params : Array Name) (constraints : Array Constraint)
          (methods : Array MethodSig) (span : Span)

  /-- Instance definition -/
  | instance_ (traitName : Name) (args : Array TypeExpr) (constraints : Array Constraint)
              (methods : Array Decl) (span : Span)

  /-- Import declaration: use base/core.{Option, Some, None} -/
  | use (path : QualName) (items : Array Name) (span : Span)

  /-- Export declaration: export { items } -/
  | export_ (items : Array Name) (span : Span)

  /-- Intrinsic declaration -/
  | intrinsic (inner : Decl) (span : Span)
  deriving Repr

namespace Decl

def span : Decl → Span
  | .def_ _ _ _ _ s => s
  | .data _ _ _ s => s
  | .struct _ _ _ _ s => s
  | .trait _ _ _ _ s => s
  | .instance_ _ _ _ _ s => s
  | .use _ _ s => s
  | .export_ _ s => s
  | .intrinsic _ s => s

/-- Get the name of a declaration (if it has one) -/
def name? : Decl → Option Name
  | .def_ _ name _ _ _ => some name
  | .data name _ _ _ => some name
  | .struct name _ _ _ _ => some name
  | .trait name _ _ _ _ => some name
  | .instance_ _ _ _ _ _ => none
  | .use _ _ _ => none
  | .export_ _ _ => none
  | .intrinsic inner _ => inner.name?

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
  let pre := String.mk (List.replicate n ' ')
  s.splitOn "\n" |>.map (pre ++ ·) |> String.intercalate "\n"

/-- Pretty print a Name -/
def ppName (n : Name) : String := n.value

/-- Pretty print a list of Names -/
def ppNames (ns : Array Name) : String :=
  ns.toList.map ppName |> String.intercalate " "

/-- Pretty print a Literal -/
def ppLiteral : Literal → String
  | .int v _ => toString v
  | .string s _ => s!"\"{s}\""
  | .bool b _ => if b then "true" else "false"

mutual

/-- Pretty print a Pattern -/
partial def ppPattern : Pattern → String
  | .var n => n.value
  | .wildcard _ => "_"
  | .lit l => ppLiteral l
  | .con n args _ =>
      if args.isEmpty then n.value
      else s!"{n.value} {args.toList.map ppPattern |> String.intercalate " "}"
  | .tuple elems _ =>
      s!"({elems.toList.map ppPattern |> String.intercalate ", "})"
  | .list elems _ =>
      s!"[{elems.toList.map ppPattern |> String.intercalate ", "}]"
  | .cons h t _ => s!"({ppPattern h}:{ppPattern t})"
  | .parens p _ => s!"({ppPattern p})"
  | .typed p ty _ => s!"({ppPattern p} :: {ppTypeExpr ty})"

/-- Pretty print a TypeExpr -/
partial def ppTypeExpr : TypeExpr → String
  | .var n => n.value
  | .con n => n.value
  | .app fn arg _ => s!"{ppTypeExpr fn} {ppTypeAtom arg}"
  | .arrow from_ to _ => s!"{ppTypeAtom from_} -> {ppTypeExpr to}"
  | .tuple elems _ =>
      s!"({elems.toList.map ppTypeExpr |> String.intercalate ", "})"
  | .list elem _ => s!"[{ppTypeExpr elem}]"
  | .forall_ vars body _ =>
      s!"forall {vars.toList.map (·.value) |> String.intercalate " "}. {ppTypeExpr body}"
  | .constrained cs body _ =>
      let csStr := cs.toList.map (fun (n, args, _) =>
        if args.isEmpty then n.value
        else s!"{n.value} {args.toList.map ppTypeExpr |> String.intercalate " "}"
      ) |> String.intercalate ", "
      s!"{ppTypeExpr body} with ({csStr})"
  | .parens t _ => s!"({ppTypeExpr t})"
  | .kinded t k _ => s!"{ppTypeExpr t} :: {ppTypeExpr k}"
where
  ppTypeAtom : TypeExpr → String
    | .var n => n.value
    | .con n => n.value
    | .tuple elems _ => s!"({elems.toList.map ppTypeExpr |> String.intercalate ", "})"
    | .list elem _ => s!"[{ppTypeExpr elem}]"
    | .parens t _ => s!"({ppTypeExpr t})"
    | t => s!"({ppTypeExpr t})"

end

/-- Pretty print a Constraint -/
def ppConstraint (c : Constraint) : String :=
  if c.args.isEmpty then c.className.value
  else s!"{c.className.value} {c.args.toList.map ppTypeExpr |> String.intercalate " "}"

mutual

/-- Pretty print an Expr -/
partial def ppExpr : Expr → String
  | .var n => n.value
  | .lit l => ppLiteral l
  | .app fn arg _ => s!"{ppExpr fn} {ppExprAtom arg}"
  | .infix op l r _ => s!"{ppExprAtom l} {op.value} {ppExprAtom r}"
  | .lambda params body _ =>
      let ps := params.toList.map fun (n, ty) =>
        match ty with
        | some t => s!"({n.value} :: {ppTypeExpr t})"
        | none => n.value
      s!"\\{ps |> String.intercalate " "} -> {ppExpr body}"
  | .let_ n ty v b _ =>
      let tyStr := match ty with | some t => s!" :: {ppTypeExpr t}" | none => ""
      s!"let {n.value}{tyStr} = {ppExpr v} in {ppExpr b}"
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
      let fs := fields.toList.map fun (n, e) => s!"{n.value} = {ppExpr e}"
      "{ " ++ (fs |> String.intercalate ", ") ++ " }"
  | .fieldAccess e f _ => s!"{ppExprAtom e}.{f.value}"
  | .parens e _ => s!"({ppExpr e})"
  | .typeAnnot e t _ => s!"{ppExprAtom e} :: {ppTypeExpr t}"
  | .compose body _ => s!"compose {ppExpr body}"
  | .bind body _ => s!"bind {ppExpr body}"
where
  ppExprAtom : Expr → String
    | .var n => n.value
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
    | some n => s!"{n.value} :: {ppTypeExpr ty}"
    | none => ppTypeExpr ty
  ) |> String.intercalate ", "
  if fieldsStr.isEmpty then s!"| {con.name.value}"
  else s!"| {con.name.value} " ++ "{ " ++ fieldsStr ++ " }"

/-- Pretty print a MethodSig -/
def ppMethodSig (m : MethodSig) : String :=
  s!"def {m.name.value} :: {ppTypeExpr m.type_}"

/-- Pretty print a Decl -/
partial def ppDecl : Decl → String
  | .def_ attrs name sig clauses _ =>
      let attrStr := if attrs.isEmpty then ""
        else s!"@[{attrs.toList.map (·.name.value) |> String.intercalate ", "}]\n"
      let sigStr := match sig with
        | some t => s!" :: {ppTypeExpr t}"
        | none => ""
      let clausesStr := clauses.toList.map ppDefClause |> String.intercalate "\n"
      if clauses.isEmpty then
        s!"{attrStr}def {name.value}{sigStr}"
      else
        s!"{attrStr}def {name.value}{sigStr}\n{indent 2 clausesStr}"

  | .data name params cons _ =>
      let paramsStr := if params.isEmpty then "" else s!" {ppNames params}"
      let consStr := cons.toList.map ppDataCon |> String.intercalate "\n"
      s!"data {name.value}{paramsStr}\n{indent 2 consStr}"

  | .struct name params con fields _ =>
      let paramsStr := if params.isEmpty then "" else s!" {ppNames params}"
      let fieldsStr := fields.toList.map (fun f =>
        match f.name with
        | some n => s!"{n.value} :: {ppTypeExpr f.type_}"
        | none => ppTypeExpr f.type_
      ) |> String.intercalate ", "
      "struct " ++ name.value ++ paramsStr ++ " = " ++ con.value ++ " { " ++ fieldsStr ++ " }"

  | .trait name params constraints methods _ =>
      let paramsStr := if params.isEmpty then "" else s!" {ppNames params}"
      let consStr := if constraints.isEmpty then ""
        else s!" with ({constraints.toList.map ppConstraint |> String.intercalate ", "})"
      let methodsStr := methods.toList.map ppMethodSig |> String.intercalate "\n"
      s!"trait {name.value}{paramsStr}{consStr} where\n{indent 2 methodsStr}"

  | .instance_ traitName args constraints methods _ =>
      let argsStr := args.toList.map ppTypeExpr |> String.intercalate " "
      let consStr := if constraints.isEmpty then ""
        else s!" with ({constraints.toList.map ppConstraint |> String.intercalate ", "})"
      let methodsStr := methods.toList.map ppDecl |> String.intercalate "\n\n"
      s!"instance {traitName.value} {argsStr}{consStr} where\n{indent 2 methodsStr}"

  | .use path items _ =>
      let itemsStr := if items.isEmpty then ""
        else ".{" ++ (items.toList.map (·.value) |> String.intercalate ", ") ++ "}"
      s!"use {path}{itemsStr}"

  | .export_ items _ =>
      "export {" ++ (items.toList.map (·.value) |> String.intercalate ", ") ++ "}"

  | .intrinsic inner _ =>
      s!"intrinsic {ppDecl inner}"

/-- Pretty print a Module -/
def ppModule (m : Module) : String :=
  let declsStr := m.decls.toList.map ppDecl |> String.intercalate "\n\n"
  s!"-- Module: {m.name}\n\n{declsStr}"

end Pretty

end Soma.Syntax
