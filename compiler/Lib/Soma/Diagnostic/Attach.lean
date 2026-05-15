import Psychopomp
import Psychopomp.Render.Diff
import Psychopomp.Render.Color
import Kenosis

open Kenosis.Json (JsonValue)

namespace Soma.Attach

private def jstr (s : String) : JsonValue := .str s

private def jobj (fields : List (String × JsonValue)) : JsonValue := .obj fields

private def jarr (xs : List JsonValue) : JsonValue := .arr xs

private def jbool (b : Bool) : JsonValue := .bool b

/-- Title with optional bold styling -/
private def styledTitle (title : String) (cfg : Psychopomp.RenderConfig) : String :=
  if cfg.colorsEnabled then
    Psychopomp.Render.Ansi.bold ++ title ++ Psychopomp.Render.Ansi.reset
  else title

def typeMismatch (expected actual : String) : Psychopomp.Attachment :=
  { tag := "type-mismatch"
    render := fun sev _ cfg =>
      let (eOut, aOut) := Psychopomp.Render.wordDiff expected actual sev cfg
      { title := styledTitle "type mismatch:" cfg
        body := [s!"  expected: {eOut}", s!"    actual: {aOut}"] }
    payload := some (jobj [
      ("expected", jstr expected),
      ("actual",   jstr actual)
    ]) }

structure UnifyStep where
  origin : String
  description : String

def unifyTrace (steps : List UnifyStep) : Psychopomp.Attachment :=
  { tag := "unify-trace"
    render := fun _ _ cfg =>
      if steps.isEmpty then
        { title := styledTitle "unify trace:" cfg, body := ["  (no steps recorded)"] }
      else
        let bodyLines := steps.map fun step =>
          if step.description.isEmpty then s!"  • {step.origin}"
          else s!"  • {step.origin}: {step.description}"
        { title := styledTitle "unify trace:" cfg, body := bodyLines }
    payload := some (jarr (steps.map fun s =>
      jobj [("origin", jstr s.origin), ("description", jstr s.description)])) }

structure MetaConstraint where
  description : String
  origin : String
  blocked : Bool

def metavarOrigins (constraints : List MetaConstraint) : Psychopomp.Attachment :=
  { tag := "metavar-origins"
    render := fun _ _ cfg =>
      if constraints.isEmpty then
        { title := styledTitle "metavar origins:" cfg
          body := ["  (no related constraints)"] }
      else
        let bodyLines := constraints.map fun c =>
          let suffix := if c.blocked then " (blocked)" else ""
          s!"  • {c.description}{suffix} from {c.origin}"
        { title := styledTitle "metavar origins:" cfg, body := bodyLines }
    payload := some (jarr (constraints.map fun c =>
      jobj [
        ("description", jstr c.description),
        ("origin",      jstr c.origin),
        ("blocked",     jbool c.blocked)
      ])) }

structure InstanceAttempt where
  name : String
  matched : Bool
  reason : Option String

def instanceSearch (className : String) (attempts : List InstanceAttempt)
    : Psychopomp.Attachment :=
  { tag := "instance-search"
    render := fun _ _ cfg =>
      if attempts.isEmpty then
        { title := styledTitle s!"instance search for `{className}`:" cfg
          body := [s!"  no candidates were tried"] }
      else
        let bodyLines := attempts.map fun a =>
          if a.matched then s!"  ✓ {a.name}"
          else match a.reason with
            | some r => s!"  ✗ {a.name}: {r}"
            | none => s!"  ✗ {a.name}"
        { title := styledTitle s!"instance search for `{className}`:" cfg
          body := bodyLines }
    payload :=
      let attemptsJson := attempts.map fun a =>
        let base := [("name", jstr a.name), ("matched", jbool a.matched)]
        let fields := match a.reason with
          | some r => base ++ [("reason", jstr r)]
          | none   => base
        jobj fields
      some (jobj [("class", jstr className), ("attempts", jarr attemptsJson)]) }

def coverage (scrutinee : String) (missing : List String) : Psychopomp.Attachment :=
  { tag := "coverage"
    render := fun _ _ cfg =>
      if missing.isEmpty then
        { title := styledTitle "coverage:" cfg
          body := [s!"  scrutinee: {scrutinee}", "  (no missing cases recorded)"] }
      else
        let bullet := missing.map (s!"  • {·}")
        { title := styledTitle "coverage:" cfg
          body := s!"  scrutinee: {scrutinee}" :: "  missing:" :: bullet }
    payload := some (jobj [
      ("scrutinee", jstr scrutinee),
      ("missing", jarr (missing.map jstr))
    ]) }

structure ProvenanceStep where
  label : String
  origin : String

def universeMismatch (lhs rhs : String) : Psychopomp.Attachment :=
  { tag := "universe-mismatch"
    render := fun _ _ cfg =>
      { title := styledTitle "universe mismatch:" cfg
        body := [s!"  left:  {lhs}", s!"  right: {rhs}"] }
    payload := some (jobj [
      ("lhs", jstr lhs),
      ("rhs", jstr rhs)
    ]) }

structure UnfoldStep where
  term : String
  rule : Option String := none
  stuck : Bool := false
  deriving Inhabited

def unfoldTrace (steps : List UnfoldStep) : Psychopomp.Attachment :=
  { tag := "unfold-trace"
    render := fun _ _ cfg =>
      if steps.isEmpty then
        { title := styledTitle "unfold trace:" cfg
          body := ["  (no reductions tried)"] }
      else
        let bodyLines := steps.map fun s =>
          let arrow := if s.stuck then "  ⊘" else "  ≡"
          let suffix := match s.rule with
            | some r => s!"   -- {r}"
            | none => ""
          s!"{arrow} {s.term}{suffix}"
        { title := styledTitle "unfold trace:" cfg, body := bodyLines }
    payload := some (jarr (steps.map fun s =>
      let base : List (String × JsonValue) :=
        [("term", jstr s.term), ("stuck", jbool s.stuck)]
      let fields := match s.rule with
        | some r => base ++ [("rule", jstr r)]
        | none => base
      jobj fields)) }

def defEqHint (expectedReduced actualReduced : String)
    (suggestion : Option String := none) : Psychopomp.Attachment :=
  { tag := "def-eq-hint"
    render := fun _ _ cfg =>
      let body :=
        [ s!"  expected reduces to: {expectedReduced}"
        , s!"  actual reduces to:   {actualReduced}" ] ++
        (match suggestion with
          | some s => [s!"  suggestion: {s}"]
          | none => [])
      { title := styledTitle "defeq hint:" cfg, body }
    payload :=
      let base : List (String × JsonValue) :=
        [ ("expectedReduced", jstr expectedReduced)
        , ("actualReduced", jstr actualReduced) ]
      let fields := match suggestion with
        | some s => base ++ [("suggestion", jstr s)]
        | none => base
      some (jobj fields) }

structure InsertedImplicit where
  name : String
  value : String

def implicits (surfaceForm : String) (resolved : List InsertedImplicit)
    : Psychopomp.Attachment :=
  { tag := "implicits"
    render := fun _ _ cfg =>
      if resolved.isEmpty then
        { title := styledTitle "implicits:" cfg
          body := [s!"  surface: {surfaceForm}", "  (no implicits inserted)"] }
      else
        let resolvedLines := resolved.map fun r =>
          s!"    {r.name} := {r.value}"
        let body := s!"  surface: {surfaceForm}" :: "  resolved:" :: resolvedLines
        { title := styledTitle "implicits:" cfg, body }
    payload := some (jobj [
      ("surfaceForm", jstr surfaceForm),
      ("resolved", jarr (resolved.map fun r =>
        jobj [("name", jstr r.name), ("value", jstr r.value)]))
    ]) }

structure RefineCandidate where
  name : String
  type : String

end Soma.Attach
