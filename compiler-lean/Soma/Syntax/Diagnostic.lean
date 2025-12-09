import Soma.Syntax.Source

namespace Soma.Syntax

/-- Severity levels for diagnostics -/
inductive Severity where
  | error
  | warning
  | info
  | hint
  deriving Repr, BEq, Inhabited

instance : ToString Severity where
  toString
    | .error => "error"
    | .warning => "warning"
    | .info => "info"
    | .hint => "hint"

/-- Style for diagnostic labels -/
inductive LabelStyle where
  | primary    -- The main cause (typically red underline)
  | secondary  -- Related context (typically blue underline)
  deriving Repr, BEq, Inhabited

/-- A label pointing to source code with a message -/
structure Label where
  span : Span
  message : String
  style : LabelStyle
  deriving Repr, Inhabited

/-- Create a primary label -/
def Label.primary (span : Span) (message : String) : Label :=
  { span, message, style := .primary }

/-- Create a secondary label -/
def Label.secondary (span : Span) (message : String) : Label :=
  { span, message, style := .secondary }

/-- A complete diagnostic message -/
structure Diagnostic where
  severity : Severity
  code : Option String        -- e.g., "E0308" for documentation lookup
  message : String            -- Main error message
  labels : Array Label        -- Multiple labeled spans
  notes : Array String        -- Additional context
  help : Option String        -- Suggested fix
  deriving Repr, Inhabited

/-- Create a simple error diagnostic with a single primary label -/
def Diagnostic.error (message : String) (span : Span) (label : String := "") : Diagnostic :=
  { severity := .error
  , code := none
  , message
  , labels := #[Label.primary span (if label.isEmpty then message else label)]
  , notes := #[]
  , help := none
  }

/-- Create a simple warning diagnostic -/
def Diagnostic.warning (message : String) (span : Span) (label : String := "") : Diagnostic :=
  { severity := .warning
  , code := none
  , message
  , labels := #[Label.primary span (if label.isEmpty then message else label)]
  , notes := #[]
  , help := none
  }

/-- Add a secondary label to a diagnostic -/
def Diagnostic.withSecondary (d : Diagnostic) (span : Span) (message : String) : Diagnostic :=
  { d with labels := d.labels.push (Label.secondary span message) }

/-- Add a note to a diagnostic -/
def Diagnostic.withNote (d : Diagnostic) (note : String) : Diagnostic :=
  { d with notes := d.notes.push note }

/-- Add help text to a diagnostic -/
def Diagnostic.withHelp (d : Diagnostic) (help : String) : Diagnostic :=
  { d with help := some help }

/-- Add an error code to a diagnostic -/
def Diagnostic.withCode (d : Diagnostic) (code : String) : Diagnostic :=
  { d with code := some code }

/-- Check if a diagnostic is an error -/
def Diagnostic.isError (d : Diagnostic) : Bool :=
  d.severity == .error

/-- All compiler phases produce the same Diagnostic type -/
abbrev Diagnostics := Array Diagnostic

/-- Check if any diagnostics are errors -/
def Diagnostics.hasErrors (ds : Diagnostics) : Bool :=
  ds.any Diagnostic.isError

/-- Get only error diagnostics -/
def Diagnostics.errors (ds : Diagnostics) : Diagnostics :=
  ds.filter Diagnostic.isError

/-- Get error count -/
def Diagnostics.errorCount (ds : Diagnostics) : Nat :=
  ds.filter Diagnostic.isError |>.size

end Soma.Syntax
