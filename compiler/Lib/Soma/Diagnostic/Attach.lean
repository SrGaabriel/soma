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

def goal (hypotheses : List (String × String)) (target : String)
    (tag : Option String := none) : Psychopomp.Attachment :=
  { tag := "goal"
    render := fun sev _ cfg =>
      let titleSuffix := match tag with
        | some t => s!" ({t})"
        | none => ""
      let title := styledTitle s!"goal{titleSuffix}:" cfg
      let hyps := hypotheses.map fun (n, t) =>
        if cfg.colorsEnabled then
          s!"  {Psychopomp.Render.Ansi.bold}{n}{Psychopomp.Render.Ansi.reset} : {t}"
        else s!"  {n} : {t}"
      let turnstile :=
        if cfg.colorsEnabled then
          s!"  {Psychopomp.Render.styleAnsi .severity sev}⊢{Psychopomp.Render.Ansi.reset} {target}"
        else s!"  ⊢ {target}"
      { title, body := hyps ++ [turnstile] }
    payload :=
      let hypsJson := hypotheses.map fun (n, t) =>
        jobj [("name", jstr n), ("type", jstr t)]
      let base := [("hypotheses", jarr hypsJson), ("target", jstr target)]
      let fields := match tag with
        | some t => base ++ [("tag", jstr t)]
        | none   => base
      some (jobj fields) }

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

def expectedBecause (steps : List ProvenanceStep) : Psychopomp.Attachment :=
  { tag := "expected-because"
    render := fun _ _ cfg =>
      if steps.isEmpty then
        { title := styledTitle "expected because:" cfg, body := [] }
      else
        let bodyLines := steps.map fun s =>
          if s.origin.isEmpty then s!"  • {s.label}"
          else s!"  • {s.label} from {s.origin}"
        { title := styledTitle "expected because:" cfg, body := bodyLines }
    payload := some (jarr (steps.map fun s =>
      jobj [("label", jstr s.label), ("origin", jstr s.origin)])) }

def universeMismatch (lhs rhs : String) : Psychopomp.Attachment :=
  { tag := "universe-mismatch"
    render := fun _ _ cfg =>
      { title := styledTitle "universe mismatch:" cfg
        body := [s!"  left:  {lhs}", s!"  right: {rhs}"] }
    payload := some (jobj [
      ("lhs", jstr lhs),
      ("rhs", jstr rhs)
    ]) }

structure RefineCandidate where
  name : String
  type : String

def refineSuggestions (candidates : List RefineCandidate) : Psychopomp.Attachment :=
  { tag := "refine-suggestions"
    render := fun _ _ cfg =>
      if candidates.isEmpty then
        { title := styledTitle "refine suggestions:" cfg, body := [] }
      else
        let bodyLines := candidates.map fun c => s!"  • {c.name} : {c.type}"
        { title := styledTitle "refine suggestions:" cfg, body := bodyLines }
    payload := some (jarr (candidates.map fun c =>
      jobj [("name", jstr c.name), ("type", jstr c.type)])) }

end Soma.Attach
