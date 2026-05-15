import Psychopomp

namespace Soma.LabelStyle

open Psychopomp

/-- A name being introduced -/
def definition : LabelStyle :=
  { pattern := .heavy, weight := 70, color := .accent, tag := "definition" }

/-- A use of a previously-defined name -/
def reference : LabelStyle :=
  { pattern := .dotted, weight := 60, color := .accent, tag := "reference" }

/-- A coercion / conversion stitched in by the elaborator -/
def inserted : LabelStyle :=
  { pattern := .wavy, weight := 60, color := .severity, tag := "inserted" }

/-- A shadowed binding that's superseded by an inner one -/
def overridden : LabelStyle :=
  { pattern := .strikethrough, weight := 60, color := .severity, tag := "overridden" }

/-- Code inside a binder's scope -/
def enclosed : LabelStyle :=
  { pattern := .dashed, weight := 30, color := .none, tag := "enclosed" }

/-- A proposed change -/
def suggestion : LabelStyle :=
  { pattern := .solid, weight := 50, color := .accent, tag := "suggestion" }

end Soma.LabelStyle
