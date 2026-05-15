import Soma.Dependent.Totality.Core
import Soma.Core.Expr

namespace Soma.Dependent.Totality

open Soma.Core
open Soma (Unique)

/-- Collect the application spine: (app (app f a1) a2) -> (f, [a1, a2]) -/
private partial def collectAppSpine (e : Expr) : Expr × List Expr :=
  match e with
  | .app fn arg =>
    let (head, args) := collectAppSpine fn
    (head, args ++ [arg])
  | _ => (e, [])

/-- Get a display name from an Expr (for variable tracking) -/
private def exprName? : Expr → Option String
  | .fvar id _ => some id.original
  | .const name _ => some name.display
  | .bvar idx => some s!"_bvar{idx}"
  | _ => none

/-- The structural shape of a term (for termination comparison) -/
inductive TermShape where
  | var (name : String)                              -- Variable reference
  | ctor (name : String) (args : Array TermShape)   -- Constructor application
  | fieldProj (inner : TermShape) (field : String)   -- Field access
  | lit (l : Literal)                                -- Literal value
  | app (fn : TermShape) (args : Array TermShape)   -- Application (opaque)
  | unknown                                          -- Unanalyzable term
  deriving Repr, Inhabited

namespace TermShape

/-- Collect all variable names used in a term shape -/
partial def collectVars : TermShape → List String
  | .var name => [name]
  | .ctor _ args => args.toList.flatMap collectVars
  | .fieldProj inner _ => collectVars inner
  | .lit _ => []
  | .app fn args => collectVars fn ++ args.toList.flatMap collectVars
  | .unknown => []

/-- Check if this shape is a simple variable -/
def asVar? : TermShape → Option String
  | .var name => some name
  | _ => none

end TermShape

/-- Collect all variable names used in an Expr (standalone function for termination) -/
partial def collectExprVars : Expr → List String
  | .fvar id _ => [id.original]
  | .const name _ => [name.display]
  | .bvar idx => [s!"_bvar{idx}"]
  | .app fn arg => collectExprVars fn ++ collectExprVars arg
  | .lam _ _ dom body => collectExprVars dom ++ collectExprVars body
  | .let_ _ ty val body => collectExprVars ty ++ collectExprVars val ++ collectExprVars body
  | .if_ c t e => collectExprVars c ++ collectExprVars t ++ collectExprVars e
  | .construct _ _ args _ => args.toList.flatMap collectExprVars
  | .«case» scruts _ arms =>
    scruts.toList.flatMap collectExprVars ++
      arms.toList.flatMap fun arm => collectExprVars arm.body
  | .record fields => fields.toList.flatMap fun (_, t) => collectExprVars t
  | .recordUpdate base updates =>
    collectExprVars base ++ updates.toList.flatMap fun (_, t) => collectExprVars t
  | .fieldAccess e _ _ => collectExprVars e
  | .inject _ args _ => args.toList.flatMap collectExprVars
  | .pi _ _ _ d c => collectExprVars d ++ collectExprVars c
  | .rowExtend l t tail => collectExprVars l ++ collectExprVars t ++ collectExprVars tail
  | .recordTy r => collectExprVars r
  | .variantTy r => collectExprVars r
  | .dataTy _ ps => ps.toList.flatMap collectExprVars
  | .closure _ caps ty => caps.toList.flatMap collectExprVars ++ collectExprVars ty
  | .array es _ => es.toList.flatMap collectExprVars
  | .tuple es => es.toList.flatMap collectExprVars
  | .ann e _ => collectExprVars e
  | _ => []

/-- Convert an Expr to its structural shape for analysis -/
partial def analyzeExprShape : Expr → TermShape
  | .fvar id _ => .var id.original
  | .const name _ => .var name.display
  | .bvar idx => .var s!"_bvar{idx}"
  | .lit l => .lit l
  | .construct name _ args _ =>
    .ctor name.display (args.map analyzeExprShape)
  | .fieldAccess e field _ => .fieldProj (analyzeExprShape e) field
  | e =>
    let (head, args) := collectAppSpine e
    if args.isEmpty then
      match exprName? e with
      | some name => .var name
      | none => .unknown
    else
      .app (analyzeExprShape head) (args.map analyzeExprShape |>.toArray)

/-- The structural shape of a pattern -/
inductive PatternShape where
  | var (name : String) -- Variable binding
  | wildcard -- Wildcard _
  | ctor (name : String) (args : Array PatternShape) -- Constructor pattern
  | lit (l : Literal) -- Literal pattern
  deriving Repr, Inhabited

/-- A pattern for analysis -/
inductive Pattern where
  | var (name : String)
  | wildcard
  | ctor (name : String) (args : Array Pattern)
  | lit (l : Literal)
  | record (fields : Array (String × Pattern))
  deriving Repr, Inhabited

/-- Extract a Pattern from an Expr -/
partial def exprToPattern : Expr → Pattern
  | .fvar id _ => .var id.original
  | .const name _ => .var name.display
  | .bvar idx => .var s!"_bvar{idx}"
  | .lit l => .lit l
  | .construct name _ args _ =>
    .ctor name.display (args.map exprToPattern)
  | .record fields =>
    .record (fields.map fun (n, t) => (n, exprToPattern t))
  | _ => .wildcard

abbrev termToPattern := exprToPattern

/-- Analyze an Expr that represents a pattern and extract bindings. -/
partial def extractPatternBindings (t : Expr) (paramIdx : Nat) (paramName : String)
    (path : StructurePath := .root) : Array BindingInfo :=
  match t with
  | .fvar id _ =>
    -- A free variable in a pattern = a binding
    #[{
      name := id.original
      paramIdx := paramIdx
      paramName := paramName
      path := path
      depth := path.depth
    }]

  | .bvar idx =>
    -- A bound variable in a pattern = a binding (use index-based name)
    #[{
      name := s!"_bvar{idx}"
      paramIdx := paramIdx
      paramName := paramName
      path := path
      depth := path.depth
    }]

  | .construct ctorName _ args _ =>
    -- Constructor pattern: each argument is deeper
    args.foldl (init := (#[], 0)) (fun (acc, idx) arg =>
      let argPath := .ctorArg path ctorName.display idx
      let bindings := extractPatternBindings arg paramIdx paramName argPath
      (acc ++ bindings, idx + 1)
    ) |>.1

  | .record fields =>
    fields.foldl (init := #[]) fun acc (fieldName, fieldVal) =>
      let fieldPath := .field path fieldName
      acc ++ extractPatternBindings fieldVal paramIdx paramName fieldPath

  | _ =>
    -- Literals, wildcards, etc. don't introduce bindings
    #[]

/-- Extract bindings from a pattern with accurate depth tracking -/
partial def extractPatternBindingsAccurate (pat : Pattern) (paramIdx : Nat) (paramName : String)
    (path : StructurePath := .root) : Array BindingInfo :=
  match pat with
  | .var name =>
    #[{
      name := name
      paramIdx := paramIdx
      paramName := paramName
      path := path
      depth := path.depth
    }]

  | .wildcard => #[]

  | .ctor ctorName args =>
    args.foldl (init := (#[], 0)) (fun (acc, idx) arg =>
      let argPath := StructurePath.ctorArg path ctorName idx
      let bindings := extractPatternBindingsAccurate arg paramIdx paramName argPath
      (acc ++ bindings, idx + 1)
    ) |>.1

  | .lit _ => #[]

  | .record fields =>
    fields.foldl (init := #[]) fun acc (fieldName, fieldPat) =>
      let fieldPath := StructurePath.field path fieldName
      acc ++ extractPatternBindingsAccurate fieldPat paramIdx paramName fieldPath

end Soma.Dependent.Totality
