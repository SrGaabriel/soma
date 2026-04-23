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

/-- The structural shape of a term (for comparison purposes) -/
inductive TermShape where
  | var (name : String)                              -- Variable reference
  | ctor (name : String) (args : Array TermShape)   -- Constructor application
  | pair (fst snd : TermShape)                       -- Pair construction
  | fstProj (inner : TermShape)                      -- First projection
  | sndProj (inner : TermShape)                      -- Second projection
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
  | .pair fst snd => collectVars fst ++ collectVars snd
  | .fstProj inner => collectVars inner
  | .sndProj inner => collectVars inner
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
  | .pair a b => collectExprVars a ++ collectExprVars b
  | .projFst e => collectExprVars e
  | .projSnd e => collectExprVars e
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
  | .sigma _ _ _ f s => collectExprVars f ++ collectExprVars s
  | .eqTy _ ty l r => collectExprVars ty ++ collectExprVars l ++ collectExprVars r
  | .refl ty x => collectExprVars ty ++ collectExprVars x
  | .transport _ ty m l r eq b =>
      collectExprVars ty ++ collectExprVars m ++ collectExprVars l ++
      collectExprVars r ++ collectExprVars eq ++ collectExprVars b
  | .rowExtend l t tail => collectExprVars l ++ collectExprVars t ++ collectExprVars tail
  | .recordTy r => collectExprVars r
  | .variantTy r => collectExprVars r
  | .dataTy _ ps => ps.toList.flatMap collectExprVars
  | .closure _ caps => caps.toList.flatMap collectExprVars
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
  | .pair fst snd => .pair (analyzeExprShape fst) (analyzeExprShape snd)
  | .projFst e => .fstProj (analyzeExprShape e)
  | .projSnd e => .sndProj (analyzeExprShape e)
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
  | pair (fst snd : PatternShape) -- Pair pattern
  | lit (l : Literal) -- Literal pattern
  deriving Repr, Inhabited

/-- A pattern for analysis -/
inductive Pattern where
  | var (name : String)
  | wildcard
  | ctor (name : String) (args : Array Pattern)
  | pair (fst snd : Pattern)
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
  | .pair a b => .pair (exprToPattern a) (exprToPattern b)
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

  | .pair fst snd =>
    let fstBindings := extractPatternBindings fst paramIdx paramName (.fst path)
    let sndBindings := extractPatternBindings snd paramIdx paramName (.snd path)
    fstBindings ++ sndBindings

  | .record fields =>
    fields.foldl (init := #[]) fun acc (fieldName, fieldVal) =>
      let fieldPath := .field path fieldName
      acc ++ extractPatternBindings fieldVal paramIdx paramName fieldPath

  | _ =>
    -- Literals, wildcards, etc. don't introduce bindings
    #[]

/-- Analyze a case arm and extract all bindings introduced by the pattern. -/
def analyzePatternFromArm (patternName : String) (scrutineeParam : Option (Nat × String))
    (armBody : Expr) (existingParams : Array String) : Array BindingInfo :=
  match scrutineeParam with
  | none => #[]  -- Scrutinee isn't a parameter, can't track size
  | some (paramIdx, paramName) =>
    -- Collect variables used in the arm body that aren't existing parameters
    let usedVars := collectExprVars armBody
    let newVars := usedVars.filter fun v => !existingParams.contains v
    -- Each new variable is a pattern binding, mark as smaller
    newVars.toArray.map fun name => {
      name := name
      paramIdx := paramIdx
      paramName := paramName
      path := .ctorArg .root patternName 0
      depth := 1  -- Conservative: all pattern bindings are at least depth 1
    }

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

  | .pair fst snd =>
    let fstBindings := extractPatternBindingsAccurate fst paramIdx paramName (.fst path)
    let sndBindings := extractPatternBindingsAccurate snd paramIdx paramName (.snd path)
    fstBindings ++ sndBindings

  | .lit _ => #[]

  | .record fields =>
    fields.foldl (init := #[]) fun acc (fieldName, fieldPat) =>
      let fieldPath := StructurePath.field path fieldName
      acc ++ extractPatternBindingsAccurate fieldPat paramIdx paramName fieldPath

/-- Analyze a case arm pattern (as an Expr) and extract bindings with accurate depths -/
def analyzePatternFromArmAccurate (patternExpr : Expr) (scrutineeParam : Option (Nat × String))
    : Array BindingInfo :=
  match scrutineeParam with
  | none => #[]
  | some (paramIdx, paramName) =>
    let pattern := exprToPattern patternExpr
    extractPatternBindingsAccurate pattern paramIdx paramName

/-- Enhanced pattern analysis that handles nested constructors properly. -/
def analyzeNestedPattern (scrutinee : Expr) (patternCtor : String)
    (patternArgs : List Expr) (params : Array String) : Array BindingInfo :=
  match exprName? scrutinee with
  | some name =>
    match params.findIdx? (· == name) with
    | some paramIdx =>
      let (bindings, _) := patternArgs.foldl (init := (#[], 0)) fun (acc, idx) arg =>
        let argPath := StructurePath.ctorArg .root patternCtor idx
        let pat := exprToPattern arg
        let argBindings := extractPatternBindingsAccurate pat paramIdx name argPath
        (acc ++ argBindings, idx + 1)
      bindings
    | none => #[]
  | none => #[]

end Soma.Dependent.Totality
