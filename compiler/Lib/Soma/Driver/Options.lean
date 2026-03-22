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

/-- Optimization profile -/
inductive OptProfile where
  | debug   : OptProfile  -- No Soma passes, -O0, Cranelift backend (futurely)
  | dev     : OptProfile  -- All Soma passes, -O1
  | release : OptProfile  -- All Soma passes, -O2 -flto
  deriving Repr, BEq

namespace OptProfile

/-- Default LLVM optimization level for a profile -/
def defaultOptLevel : OptProfile → Nat
  | .debug   => 0
  | .dev     => 1
  | .release => 2

/-- Whether to run Soma-level optimization passes -/
def runSomaPasses : OptProfile → Bool
  | .debug   => false
  | .dev     => true
  | .release => true

/-- Whether to enable LTO at link time -/
def lto : OptProfile → Bool
  | .release => !System.Platform.isWindows
  | _ => false

/-- Parse a profile name string -/
def parse? : String → Option OptProfile
  | "debug"   => some .debug
  | "dev"     => some .dev
  | "release" => some .release
  | _ => none

instance : ToString OptProfile where
  toString
    | .debug => "debug"
    | .dev => "dev"
    | .release => "release"

end OptProfile

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

/-- Options for the `lower` command (declaration lowering) -/
structure LowerOptions where
  input : String
  showUntyped : Bool := false  -- Show untyped Core module
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
  profile : OptProfile := .dev
  optimizationLevel : Option Nat := none
  validate : Bool := false
  sysroot : Option String := none
  emitLlvm : Bool := false
  target : Option String := none
  deriving Repr

namespace BuildOptions

/-- Resolved LLVM optimization level: explicit flag overrides profile default -/
def resolvedOptLevel (opts : BuildOptions) : Nat :=
  opts.optimizationLevel.getD opts.profile.defaultOptLevel

/-- Whether to run Soma-level optimization passes -/
def runSomaPasses (opts : BuildOptions) : Bool :=
  opts.profile.runSomaPasses

/-- Whether to enable LTO -/
def lto (opts : BuildOptions) : Bool :=
  opts.profile.lto

end BuildOptions

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
