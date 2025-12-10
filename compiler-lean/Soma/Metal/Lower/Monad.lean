import Soma.Metal.Lower.Error
import Soma.Metal.Lower.Env
import Soma.Metal.Name

namespace Soma.Metal.Lower

open Soma.Metal
open Soma.Syntax (Span)

/-- Mutable state during lowering -/
structure LowerState where
  nextBindingId : Nat
  nextUniqueId : Nat
  errors : Array LowerError
  globalEnv : GlobalEnv

namespace LowerState

def empty (moduleName : String) : LowerState :=
  { nextBindingId := 0
  , nextUniqueId := 0
  , errors := #[]
  , globalEnv := GlobalEnv.empty moduleName
  }

end LowerState

/-- The lowering monad -/
abbrev LowerM := StateM LowerState

namespace LowerM

/-- Generate a fresh binding ID -/
def freshBindingId : LowerM BindingId := do
  let st ← get
  let id := st.nextBindingId
  set { st with nextBindingId := id + 1 }
  pure ⟨id⟩

/-- Generate a fresh unique ID -/
def freshUniqueId : LowerM Nat := do
  let st ← get
  let id := st.nextUniqueId
  set { st with nextUniqueId := id + 1 }
  pure id

/-- Get the module name -/
def getModuleName : LowerM String := do
  let st ← get
  pure st.globalEnv.moduleName

/-- Report an error -/
def reportError (err : LowerError) : LowerM Unit := do
  let st ← get
  set { st with errors := st.errors.push err }

/-- Get the global environment -/
def getGlobalEnv : LowerM GlobalEnv := do
  let st ← get
  pure st.globalEnv

/-- Modify the global environment -/
def modifyGlobalEnv (f : GlobalEnv → GlobalEnv) : LowerM Unit := do
  let st ← get
  set { st with globalEnv := f st.globalEnv }

/-- Create a global name -/
def mkGlobalName (name : String) : LowerM Name := do
  let modName ← getModuleName
  let unique ← freshUniqueId
  pure $ .global modName name unique

/-- Create a constructor name -/
def mkCtorName (typeName : String) (ctorName : String) (tag : Nat) : LowerM Name := do
  pure $ .ctor typeName ctorName tag

/-- Create a synthetic name -/
def mkSyntheticName (kind : SyntheticKind) : LowerM Name := do
  let id ← freshUniqueId
  pure $ .synthetic kind id

/-- Look up a variable - first in local scope, then in globals -/
def lookupVar (localEnv : LocalEnv scope) (name : String)
    : LowerM (Option (Sum (ScopedVar scope) GlobalInfo)) := do
  -- First check local scope
  match localEnv.lookup name with
  | some v => pure (some (.inl v))
  | none =>
    -- Then check globals
    let genv ← getGlobalEnv
    match genv.lookupGlobal name with
    | some info => pure (some (.inr info))
    | none =>
      -- Finally check constructors (they're also valid as expressions)
      match genv.lookupConstructor name with
      | some ctorInfo =>
        -- Use uninhabited span for synthetic GlobalInfo from constructor lookup
        let globalInfo : GlobalInfo := { name := ctorInfo.name, typeSyntax := none, definedAt := Span.uninhabited }
        pure (some (.inr globalInfo))
      | none => pure none

/-- Look up a type by name -/
def lookupType (name : String) : LowerM (Option TypeInfo) := do
  let genv ← getGlobalEnv
  pure (genv.lookupType name)

/-- Look up a constructor by name -/
def lookupConstructor (name : String) : LowerM (Option ConstructorInfo) := do
  let genv ← getGlobalEnv
  pure (genv.lookupConstructor name)

/-- Look up a type class by name -/
def lookupTypeClass (name : String) : LowerM (Option TypeClassInfo) := do
  let genv ← getGlobalEnv
  pure (genv.lookupTypeClass name)

/-- Register a global binding -/
def registerGlobal (name : String) (info : GlobalInfo) : LowerM Unit := do
  modifyGlobalEnv (·.addGlobal name info)

/-- Register a type -/
def registerType (name : String) (info : TypeInfo) : LowerM Unit := do
  modifyGlobalEnv (·.addType name info)

/-- Register a constructor -/
def registerConstructor (name : String) (info : ConstructorInfo) : LowerM Unit := do
  modifyGlobalEnv (·.addConstructor name info)

/-- Register a type class -/
def registerTypeClass (name : String) (info : TypeClassInfo) : LowerM Unit := do
  modifyGlobalEnv (·.addTypeClass name info)

/-- Run the lowering monad -/
def run (m : LowerM α) (moduleName : String) : α × LowerState :=
  StateT.run m (LowerState.empty moduleName)

end LowerM

end Soma.Metal.Lower
