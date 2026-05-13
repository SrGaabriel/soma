import Psychopomp
import Psychopomp.Source.Adapter
import Psychopomp.Driver.Flush
import Psychopomp.Driver.Json
import Psychopomp.Render.Diff
import Psychopomp.Render.Color
import Soma.Syntax.Source
import Soma.Diagnostic.Attach
import Soma.Diagnostic.Cascade

namespace Soma

export Psychopomp (
  Diagnostic Label LabelStyle UnderlinePattern ColorRole
  Severity SeverityLevel Certainty
  SubstrateRef SubstrateView SubstrateKind
  Attachment Edit QuickFix
  Source SourceContext
  SubstrateRepository
  LineIndex
)

abbrev Diagnostics := Array Psychopomp.Diagnostic

namespace Diagnostics

def hasErrors (ds : Diagnostics) : Bool :=
  ds.any fun d => d.severity.level == .error

def errors (ds : Diagnostics) : Diagnostics :=
  ds.filter fun d => d.severity.level == .error

def errorCount (ds : Diagnostics) : Nat :=
  (errors ds).size

end Diagnostics

inductive Phase where
  | parse
  | lower
  | elaborate
  | codegen
  | link
  deriving Repr, BEq, Hashable, Inhabited

namespace Phase

def toString : Phase → String
  | .parse     => "parse"
  | .lower     => "lower"
  | .elaborate => "elaborate"
  | .codegen   => "codegen"
  | .link      => "link"

end Phase

instance : ToString Phase := ⟨Phase.toString⟩

def severity (phase : Phase) (level : Psychopomp.SeverityLevel := .error)
    : Psychopomp.Severity :=
  { level, phase := some phase.toString, certainty := .certain, audiences := [] }

namespace Bridge

/-- Convert a Soma `SourceFile` to a Psychopomp `SourceContext` -/
def sourceContextOf (sf : Soma.Syntax.SourceFile) (tabWidth : Nat := 4)
    : Psychopomp.SourceContext :=
  Psychopomp.SourceContext.of
    { name := sf.path, contents := sf.content } tabWidth

/-- Convert a Soma byte-offset span to a Psychopomp row/col span -/
def psyOfSpan (ctx : Psychopomp.SourceContext) (s : Soma.Syntax.Span)
    : Psychopomp.Span :=
  ctx.spanOfBytes s.start.byteOffset s.stop.byteOffset

/-- Whether the span represents a real source location (todo: fix) -/
def hasRealLocation (s : Soma.Syntax.Span) : Bool :=
  s.start.line > 0 || s.stop.line > 0

end Bridge

structure SubstrateRepo where
  views : Array Psychopomp.SubstrateView := #[]
  byFile : Std.HashMap Soma.Syntax.FileId Psychopomp.SubstrateRef := ∅
  deriving Inhabited

namespace SubstrateRepo

/-- An empty project repository -/
def empty : SubstrateRepo := {}

/-- Look up a `FileId`'s substrate ref, if registered -/
def find? (r : SubstrateRepo) (fid : Soma.Syntax.FileId) : Option Psychopomp.SubstrateRef :=
  r.byFile[fid]?

/-- Register a `SourceFile` and return the new repository plus the allocated ref -/
def putFile (r : SubstrateRepo) (sf : Soma.Syntax.SourceFile)
    : SubstrateRepo × Psychopomp.SubstrateRef :=
  match r.byFile[sf.id]? with
  | some ref => (r, ref)
  | none =>
    let ref := r.views.size
    let view := (Bridge.sourceContextOf sf).toSubstrateView
    ({ views := r.views.push view
       byFile := r.byFile.insert sf.id ref }, ref)

end SubstrateRepo

/-- The `Psychopomp.SubstrateRepository` instance used by the flush/JSON drivers -/
instance : Psychopomp.SubstrateRepository SubstrateRepo where
  get r ref :=
    if h : ref < r.views.size then
      .ok r.views[ref]
    else
      .error s!"SubstrateRepo.get: invalid ref {ref} (repository holds {r.views.size} views)"
  put r view :=
    let ref := r.views.size
    ({ r with views := r.views.push view }, ref)

structure DiagBuilder where
  srcCtx : Psychopomp.SourceContext
  subRef : Psychopomp.SubstrateRef
  deriving Inhabited

namespace DiagBuilder

/-- Build a `DiagBuilder` against an existing project repo -/
def ofSourceFile (repo : SubstrateRepo) (sf : Soma.Syntax.SourceFile)
    : SubstrateRepo × DiagBuilder :=
  let (repo', ref) := repo.putFile sf
  (repo', { srcCtx := Bridge.sourceContextOf sf, subRef := ref })

/-- Build a `DiagBuilder` for a single isolated source file -/
def standalone (sf : Soma.Syntax.SourceFile) : DiagBuilder × SubstrateRepo :=
  let (repo, b) := DiagBuilder.ofSourceFile SubstrateRepo.empty sf
  (b, repo)

def psy (b : DiagBuilder) (s : Soma.Syntax.Span) : Psychopomp.Span :=
  Bridge.psyOfSpan b.srcCtx s

def label (b : DiagBuilder) (span : Soma.Syntax.Span) (msg : String)
    (style : Psychopomp.LabelStyle := .error) : Psychopomp.Label :=
  { substrate := b.subRef, range := b.psy span, message := some msg, style }

def primary (b : DiagBuilder) (span : Soma.Syntax.Span) (msg : String) : Psychopomp.Label :=
  b.label span msg .error

def support (b : DiagBuilder) (span : Soma.Syntax.Span) (msg : String) : Psychopomp.Label :=
  b.label span msg .support

end DiagBuilder

structure DiagContext where
  repo  : SubstrateRepo
  files : Std.HashMap Soma.Syntax.FileId DiagBuilder
  deriving Inhabited

namespace DiagContext

/-- An empty context -/
def empty : DiagContext :=
  { repo := SubstrateRepo.empty, files := ∅ }

/-- Register a single source file in the context -/
def insert (ctx : DiagContext) (sf : Soma.Syntax.SourceFile)
    : DiagContext × DiagBuilder :=
  match ctx.files[sf.id]? with
  | some b => (ctx, b)
  | none =>
    let (repo', b) := DiagBuilder.ofSourceFile ctx.repo sf
    ({ repo := repo', files := ctx.files.insert sf.id b }, b)

/-- Build a context covering every file in a `SourceFileMap` -/
def build (sm : Soma.Syntax.SourceFileMap) : DiagContext := Id.run do
  let mut ctx : DiagContext := DiagContext.empty
  for (_, sf) in sm.files do
    ctx := (ctx.insert sf).1
  return ctx

/-- A context for a single isolated source file -/
def ofSourceFile (sf : Soma.Syntax.SourceFile) : DiagContext :=
  (DiagContext.empty.insert sf).1

/-- Look up a span's `DiagBuilder` by its `FileId` -/
def builderFor? (ctx : DiagContext) (span : Soma.Syntax.Span) : Option DiagBuilder :=
  ctx.files[span.start.file]?

/-- Build a label for a Soma span -/
def label (ctx : DiagContext) (span : Soma.Syntax.Span) (msg : String)
    (style : Psychopomp.LabelStyle := .error) : Psychopomp.Label :=
  match ctx.builderFor? span with
  | some b => b.label span msg style
  | none =>
    { substrate := 0
      range := { startLine := 0, startCol := 0, endLine := 0, endCol := 0 }
      message := some msg
      style }

def primary (ctx : DiagContext) (span : Soma.Syntax.Span) (msg : String)
    : Psychopomp.Label :=
  ctx.label span msg .error

def support (ctx : DiagContext) (span : Soma.Syntax.Span) (msg : String)
    : Psychopomp.Label :=
  ctx.label span msg .support

end DiagContext

namespace Fix

/-- Build a list of `QuickFix.replace` operations from typo-correction suggestions -/
def renameSuggestions (ctx : DiagContext) (span : Soma.Syntax.Span)
    (suggestions : Array String) : List Psychopomp.QuickFix :=
  match ctx.builderFor? span with
  | none => []
  | some b =>
    let psy := b.psy span
    suggestions.toList.map fun candidate =>
      { description := s!"rename to `{candidate}`"
        edits := [.replace b.subRef psy candidate] }

/-- Build a `QuickFix.delete` for an attribute span -/
def deleteSpan (ctx : DiagContext) (span : Soma.Syntax.Span)
    (description : String) : List Psychopomp.QuickFix :=
  match ctx.builderFor? span with
  | none => []
  | some b =>
    [{ description, edits := [.delete b.subRef (b.psy span)] }]

/-- Build a `QuickFix.replace` for a single span -/
def replaceSpan (ctx : DiagContext) (span : Soma.Syntax.Span)
    (newText : String) (description : String) : List Psychopomp.QuickFix :=
  match ctx.builderFor? span with
  | none => []
  | some b =>
    [{ description, edits := [.replace b.subRef (b.psy span) newText] }]

end Fix

namespace Render

def debugMode : IO Bool := do
  match ← IO.getEnv "SOMA_DEBUG" with
  | none => return false
  | some s =>
    let t := s.trimAscii
    return !(t.isEmpty || t == "0" || t == "false")

/-- Audience filter -/
def isUserVisible (d : Psychopomp.Diagnostic) : Bool :=
  match d.severity.audiences with
  | [] => true
  | aud =>
    let onlyCompilerDev :=
      aud.all (· == "compilerDev") && aud.contains "compilerDev"
    !onlyCompilerDev

/-- Filter diagnostics for the current audience -/
def filterAudience (debug : Bool) (ds : Array Psychopomp.Diagnostic)
    : Array Psychopomp.Diagnostic :=
  if debug then ds else ds.filter isUserVisible

/-- Auto-assign a stable `id` if the diagnostic doesn't have one -/
def assignId (d : Psychopomp.Diagnostic) : Psychopomp.Diagnostic :=
  match d.id with
  | some _ => d
  | none =>
    let code := d.code.getD "E0"
    let key := s!"{code}@{d.primary.substrate}:{d.primary.range.startLine}:{d.primary.range.startCol}"
    { d with id := some key }

/-- Apply id assignment recursively -/
partial def assignIdRec (d : Psychopomp.Diagnostic) : Psychopomp.Diagnostic :=
  let d' := assignId d
  { d' with causedBy := d'.causedBy.map assignIdRec }

/-- Normalise an array -/
def normalise (debug : Bool) (ds : Array Psychopomp.Diagnostic)
    : Array Psychopomp.Diagnostic :=
  (filterAudience debug ds).map assignIdRec

/-- Print a single diagnostic to stderr against the supplied repo -/
def eprintDiag (repo : SubstrateRepo) (d : Psychopomp.Diagnostic) : IO Unit := do
  Psychopomp.Driver.Flush.eprint (assignIdRec d) {} repo

/-- Print every diagnostic, one per stanza -/
def eprintAll (repo : SubstrateRepo) (ds : Array Psychopomp.Diagnostic) : IO Unit := do
  let collapsed ← Soma.Diagnostic.Cascade.maybeCollapse ds
  let debug ← debugMode
  for d in normalise debug collapsed do
    Psychopomp.Driver.Flush.eprint d {} repo
    IO.eprintln ""

/-- Print a single diagnostic using the supplied context's repo -/
def eprintDiagCtx (ctx : DiagContext) (d : Psychopomp.Diagnostic) : IO Unit :=
  eprintDiag ctx.repo d

/-- Print every diagnostic against a `DiagContext` -/
def eprintAllCtx (ctx : DiagContext) (ds : Array Psychopomp.Diagnostic) : IO Unit :=
  eprintAll ctx.repo ds

/-- Render a one-line summary `N errors, M warnings emitted` -/
def summary (ds : Array Psychopomp.Diagnostic) : String := Id.run do
  let visible := ds.filter isUserVisible
  let errors := (visible.filter fun d => d.severity.level == .error).size
  let warnings := (visible.filter fun d => d.severity.level == .warning).size
  let mut parts : Array String := #[]
  if errors > 0 then
    let s := if errors == 1 then "error" else "errors"
    parts := parts.push s!"{errors} {s}"
  if warnings > 0 then
    let s := if warnings == 1 then "warning" else "warnings"
    parts := parts.push s!"{warnings} {s}"
  if parts.isEmpty then return "no errors"
  return String.intercalate ", " parts.toList ++ " emitted"

/-- Encode an array of diagnostics as a JSON array string -/
def encodeJson (repo : SubstrateRepo) (ds : Array Psychopomp.Diagnostic) : String :=
  let entries := (ds.map assignIdRec).toList.filterMap fun d =>
    match Psychopomp.Driver.Json.encode d repo with
    | .ok s => some s
    | .error _ => none
  "[" ++ String.intercalate "," entries ++ "]"

/-- Encode using a `DiagContext`'s repo -/
def encodeJsonCtx (ctx : DiagContext) (ds : Array Psychopomp.Diagnostic) : String :=
  encodeJson ctx.repo ds

-- todo: do this properly
def encodeCheckOutput (repo : SubstrateRepo) (ds : Array Psychopomp.Diagnostic)
    (moduleName? : Option String := none) : String :=
  let success := !Diagnostics.hasErrors ds
  let diagsJson := encodeJson repo ds
  let successField := s!"\"success\":{if success then "true" else "false"}"
  let diagsField := s!"\"diagnostics\":{diagsJson}"
  let moduleField? := moduleName?.map fun n =>
    s!"\"module\":\"{n}\""
  let fields := match moduleField? with
    | some m => [successField, diagsField, m]
    | none => [successField, diagsField]
  "{" ++ String.intercalate "," fields ++ "}"

end Render

end Soma
