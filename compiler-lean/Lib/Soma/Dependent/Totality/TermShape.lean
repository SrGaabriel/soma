import Soma.Dependent.Totality.Core

namespace Soma.Dependent.Totality

open Soma.Core
open Soma.Metal (Literal Name)

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

/-- Collect all variable names used in a term (standalone function for termination) -/
partial def collectTermVars : Term → List String
  | .var _ name => [name]
  | .app fn args => collectTermVars fn ++ args.flatMap collectTermVars
  | .lam _ body => collectTermVars body
  | .if_ c t e => collectTermVars c ++ collectTermVars t ++ collectTermVars e
  | .pair a b => collectTermVars a ++ collectTermVars b
  | .fst e => collectTermVars e
  | .snd e => collectTermVars e
  | .construct _ _ args => args.flatMap collectTermVars
  | .case s arms => collectTermVars s ++ arms.flatMap fun (_, _, b) => collectTermVars b
  | .record fields => fields.flatMap fun (_, t) => collectTermVars t
  | .fieldAccess e _ => collectTermVars e
  | .pi _ _ _ d c => collectTermVars d ++ collectTermVars c
  | .sigma _ _ f s => collectTermVars f ++ collectTermVars s
  | .eq _ ty l r => collectTermVars ty ++ collectTermVars l ++ collectTermVars r
  | .refl ty x => collectTermVars ty ++ collectTermVars x
  | .transport _ ty m l r eq b =>
      collectTermVars ty ++ collectTermVars m ++ collectTermVars l ++
      collectTermVars r ++ collectTermVars eq ++ collectTermVars b
  | .rowExtend l t tail => collectTermVars l ++ collectTermVars t ++ collectTermVars tail
  | .recordTy r => collectTermVars r
  | .variantTy r => collectTermVars r
  | _ => []

/-- Convert a Term to its structural shape for analysis -/
partial def analyzeTermShape : Term → TermShape
  | .var _ name => .var name
  | .lit l => .lit l
  | .construct name _ args =>
    .ctor name.display (args.map analyzeTermShape |>.toArray)
  | .pair fst snd => .pair (analyzeTermShape fst) (analyzeTermShape snd)
  | .fst e => .fstProj (analyzeTermShape e)
  | .snd e => .sndProj (analyzeTermShape e)
  | .fieldAccess e field => .fieldProj (analyzeTermShape e) field
  | .app fn args =>
    .app (analyzeTermShape fn) (args.map analyzeTermShape |>.toArray)
  | .global name => .var name.display  -- Treat globals as variables for shape analysis
  | _ => .unknown

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

/-- Extract a Pattern from a Term (when the Term represents a pattern) -/
partial def termToPattern : Term → Pattern
  | .var _ name => .var name
  | .lit l => .lit l
  | .construct name _ args =>
    .ctor name.display (args.toArray.map termToPattern)
  | .pair a b => .pair (termToPattern a) (termToPattern b)
  | .record fields =>
    .record (fields.toArray.map fun (n, t) => (n, termToPattern t))
  | _ => .wildcard

/-- Analyze a Term that represents a pattern and extract bindings.
    This is used when we have patterns represented as Terms (from case arms). -/
partial def extractPatternBindings (t : Term) (paramIdx : Nat) (paramName : String)
    (path : StructurePath := .root) : Array BindingInfo :=
  match t with
  | .var _ name =>
    -- A variable in a pattern = a binding
    #[{
      name := name
      paramIdx := paramIdx
      paramName := paramName
      path := path
      depth := path.depth
    }]

  | .construct ctorName _ args =>
    -- Constructor pattern: each argument is deeper
    args.toArray.foldl (init := (#[], 0)) (fun (acc, idx) arg =>
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
    (armBody : Term) (existingParams : Array String) : Array BindingInfo :=
  match scrutineeParam with
  | none => #[]  -- Scrutinee isn't a parameter, can't track size
  | some (paramIdx, paramName) =>
    -- Collect variables used in the arm body that aren't existing parameters
    let usedVars := collectTermVars armBody
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

/-- Analyze a case arm pattern (as a Term) and extract bindings with accurate depths -/
def analyzePatternFromArmAccurate (patternTerm : Term) (scrutineeParam : Option (Nat × String))
    : Array BindingInfo :=
  match scrutineeParam with
  | none => #[]
  | some (paramIdx, paramName) =>
    let pattern := termToPattern patternTerm
    extractPatternBindingsAccurate pattern paramIdx paramName

/-- Enhanced pattern analysis that handles nested constructors properly. -/
def analyzeNestedPattern (scrutinee : Term) (patternCtor : String)
    (patternArgs : List Term) (params : Array String) : Array BindingInfo :=
  match scrutinee with
  | .var _ name =>
    match params.findIdx? (· == name) with
    | some paramIdx =>
      let (bindings, _) := patternArgs.foldl (init := (#[], 0)) fun (acc, idx) arg =>
        let argPath := StructurePath.ctorArg .root patternCtor idx
        let pat := termToPattern arg
        let argBindings := extractPatternBindingsAccurate pat paramIdx name argPath
        (acc ++ argBindings, idx + 1)
      bindings
    | none => #[]
  | _ => #[]

end Soma.Dependent.Totality
