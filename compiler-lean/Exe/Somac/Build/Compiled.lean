import Soma.Project
import Soma.Metal
import Soma.Typing

namespace Somac.Build

open Soma
open Soma.Project
open Soma.Metal
open Soma.Typing

/-- Result of checking/compiling a single module -/
structure CheckedModule where
  name : String
  resolvedAst : Syntax.Module
  metalModule : Metal.Module
  publicSymbols : SymbolEnv
  instances : InstanceEnv
  uniqueCounter : Nat

/-- A fully compiled module ready for linking -/
structure CompiledModule where
  name : String
  metalNormalized : Metal.Module
  -- alloyExpanded : Alloy.Module
  publicSymbols : SymbolEnv
  publicInstances : InstanceEnv
  resolvedAst : Syntax.Module

namespace CompiledModule

/-- Extract constructor metadata from this module.
    TODO: Implement when Metal lowering produces type definitions
-/
def constructorMetadata (_m : CompiledModule) : Std.HashMap Metal.Name Nat :=
  {}  -- TODO: Extract from metalNormalized.types

end CompiledModule

/-- External dependency loaded from a tarball/package -/
structure ExternalDependency where
  name : String
  version : Option String := none
  symbols : Std.HashMap String SymbolEnv
  instances : Std.HashMap String InstanceEnv
  constructors : Std.HashMap String Nat -- constructor name -> tag
  -- alloyModules : Array Alloy.Module

/-- Errors that can occur during module compilation -/
inductive CompileError where
  | parseError (module : String) (message : String)
  | typeError (module : String) (errors : Array String)
  | cyclicDependency (modules : Array String)
  | dependencyNotFound (name : String) (path : String)
  | dependencyLoadError (name : String) (message : String)
  deriving Repr

instance : ToString CompileError where
  toString
    | .parseError m msg => s!"Parse error in {m}: {msg}"
    | .typeError m errs => s!"Type errors in {m}:\n" ++ String.intercalate "\n" errs.toList
    | .cyclicDependency mods => s!"Cyclic dependency: {mods.toList}"
    | .dependencyNotFound name path => s!"Dependency '{name}' not found at {path}"
    | .dependencyLoadError name msg => s!"Failed to load dependency '{name}': {msg}"

end Somac.Build
