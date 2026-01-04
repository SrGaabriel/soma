namespace Soma.Driver

/-- File extension for Soma source files -/
def fileExt : String := ".soma"

/-- Output format for diagnostic messages -/
inductive OutputFormat where
  | human : OutputFormat
  | json : OutputFormat
  deriving Repr, BEq

/-- Compilation mode for the backend -/
inductive CompilationMode where
  | standard : CompilationMode
  | graph : CompilationMode
  | hybrid : CompilationMode
  deriving Repr, BEq

/-- Options for the `check` command -/
structure CheckOptions where
  input : String
  name : Option String := none
  deps : Array (String × String) := #[]
  format : OutputFormat := .json
  deriving Repr

/-- Options for the `metadata` command -/
structure MetadataOptions where
  input : String
  name : Option String := none
  deps : Array (String × String) := #[]
  deriving Repr

/-- Options for the `lower` command (Metal HIR lowering) -/
structure LowerOptions where
  input : String
  showUntyped : Bool := false  -- Show untyped Metal IR
  deriving Repr

/-- Options for the `circuit` command -/
structure CircuitOptions where
  input : String
  linearize : Bool := false
  graphFormat : Bool := false
  eval : Bool := false
  toAlloy : Bool := false
  toLlvm : Bool := false
  deriving Repr

/-- Options for the `build` command -/
structure BuildOptions where
  input : String
  output : Option String := none
  name : Option String := none
  lib : Bool := false
  deps : Array (String × String) := #[]
  skipCircuit : Bool := false
  mode : CompilationMode := .standard
  optimizationLevel : Option Nat := none
  validate : Bool := false
  deriving Repr

/-- All commands supported by the compiler -/
inductive Command where
  | build : BuildOptions → Command
  | check : CheckOptions → Command
  | metadata : MetadataOptions → Command
  | lex : String → Command
  | parse : String → Command
  | lower : LowerOptions → Command
  | circuit : CircuitOptions → Command
  deriving Repr

/-- Get the input file path from a command -/
def Command.inputFile : Command → String
  | .build opts => opts.input
  | .check opts => opts.input
  | .metadata opts => opts.input
  | .lex path => path
  | .parse path => path
  | .lower opts => opts.input
  | .circuit opts => opts.input

end Soma.Driver
