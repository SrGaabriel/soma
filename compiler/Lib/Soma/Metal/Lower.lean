
import Soma.Metal.Lower.Env
import Soma.Metal.Lower.Monad
import Soma.Metal.Lower.Expr
import Soma.Metal.Lower.Decl

namespace Soma.Metal.Lower

open Soma.Syntax (Module)
open Soma.Metal (UntypedModule)

/-- Result of lowering a module -/
structure LowerResult where
  module : UntypedModule
  errors : Array LowerError
  warnings : Array LowerWarning
  globalEnv : GlobalEnv

/-- Lower a Syntax module to an UntypedModule.

    It does:
    1. Collection of global definitions (types, functions, constructors)
    2. Resolution of all name references
    3. Conversion of Syntax.Expr to Metal.Expr
-/
def lower (syntaxModule : Syntax.Module) : LowerResult :=
  let (metalModule, finalState) := LowerM.run (lowerModule syntaxModule.name syntaxModule.decls) syntaxModule.name
  { module := metalModule
  , errors := finalState.errors
  , warnings := finalState.warnings
  , globalEnv := finalState.globalEnv
  }

/-- Lower with an initial environment (for multi-module compilation) -/
def lowerWithEnv (syntaxModule : Syntax.Module) (initialEnv : GlobalEnv) : LowerResult :=
  let initialState : LowerState := {
    nextBindingId := 0
    nextUniqueId := 0
    moduleName := syntaxModule.name
    errors := #[]
    warnings := #[]
    globalEnv := initialEnv
  }
  let (metalModule, finalState) := StateT.run (lowerModule syntaxModule.name syntaxModule.decls) initialState
  { module := metalModule
  , errors := finalState.errors
  , warnings := finalState.warnings
  , globalEnv := finalState.globalEnv
  }

/-- Check if lowering succeeded without errors -/
def LowerResult.success (r : LowerResult) : Bool := r.errors.isEmpty

/-- Get error messages -/
def LowerResult.errorMessages (r : LowerResult) : Array String :=
  r.errors.map LowerError.message

/-- Get warning messages -/
def LowerResult.warningMessages (r : LowerResult) : Array String :=
  r.warnings.map LowerWarning.message

end Soma.Metal.Lower
