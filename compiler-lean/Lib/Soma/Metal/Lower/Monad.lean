import Soma.Metal.Lower.Error
import Soma.Metal.Lower.Env
import Soma.Metal.Name
import Soma.Unique

namespace Soma.Metal.Lower

open Soma
open Soma.Metal
open Soma.Syntax (Span)

/-- Mutable state during lowering -/
structure LowerState where
  nextBindingId : Nat
  nextUniqueId : Nat
  moduleName : String
  errors : Array LowerError
  globalEnv : GlobalEnv

namespace LowerState

def empty (moduleName : String) : LowerState :=
  { nextBindingId := 0
  , nextUniqueId := 0
  , moduleName
  , errors := #[]
  , globalEnv := GlobalEnv.empty moduleName
  }

/-- Create a LowerState with a pre-populated GlobalEnv for external symbols -/
def withExternalSymbols (moduleName : String) (initialEnv : GlobalEnv) : LowerState :=
  { nextBindingId := 0
  , nextUniqueId := 0
  , moduleName
  , errors := #[]
  , globalEnv := initialEnv
  }

end LowerState

/-- The lowering monad -/
abbrev LowerM := StateM LowerState

namespace LowerM

/-- Get the module name -/
def getModuleName : LowerM String := do
  let st ← get
  pure st.moduleName

/-- Generate a fresh binding ID with full context -/
def freshBindingId (original : String) (bindingKind : LocalPrefix := .patternVar) : LowerM BindingId := do
  let st ← get
  let id := st.nextBindingId
  let modName := st.moduleName
  set { st with nextBindingId := id + 1 }
  pure { id, module := modName, original, kind := bindingKind }

/-- Generate a fresh binding ID for a parameter -/
def freshParamId (name : String) : LowerM BindingId :=
  freshBindingId name .param

/-- Generate a fresh binding ID for a pattern variable -/
def freshPatternVarId (name : String) : LowerM BindingId :=
  freshBindingId name .patternVar

/-- Generate a fresh binding ID for a temporary -/
def freshTempId (name : String := "_tmp") : LowerM BindingId :=
  freshBindingId name .temp

/-- Generate a fresh unique ID -/
def freshUniqueId : LowerM Nat := do
  let st ← get
  let id := st.nextUniqueId
  set { st with nextUniqueId := id + 1 }
  pure id

/-- Generate a fresh Unique -/
def freshUnique (original : String) : LowerM Unique := do
  let modName ← getModuleName
  let id ← freshUniqueId
  pure { id, module := modName, original }

/-- Report an error -/
def reportError (err : LowerError) : LowerM Unit := do
  let st ← get
  set { st with errors := st.errors.push err }

/-- Get all errors -/
def getErrors : LowerM (Array LowerError) := do
  let st ← get
  pure st.errors

/-- Check if there are any errors -/
def hasErrors : LowerM Bool := do
  let errs ← getErrors
  pure !errs.isEmpty

/-- Get the global environment -/
def getGlobalEnv : LowerM GlobalEnv := do
  let st ← get
  pure st.globalEnv

/-- Modify the global environment -/
def modifyGlobalEnv (f : GlobalEnv → GlobalEnv) : LowerM Unit := do
  let st ← get
  set { st with globalEnv := f st.globalEnv }

/-- Create a user name from a Unique -/
def mkUserName (unique : Unique) : Name :=
  .user unique

/-- Create a fresh user name -/
def freshUserName (original : String) : LowerM Name := do
  let unique ← freshUnique original
  pure (mkUserName unique)

/-- Create a constructor name -/
def mkCtorName (typeUnique : Unique) (ctorName : String) (tag : Nat) : Name :=
  .ctor typeUnique ctorName tag

/-- Create a fresh constructor name -/
def freshCtorName (typeName : String) (ctorName : String) (tag : Nat) : LowerM Name := do
  let typeUnique ← freshUnique typeName
  pure (mkCtorName typeUnique ctorName tag)

/-- Create a synthetic name from a base unique -/
def mkSyntheticName (base : Unique) (kind : SyntheticKind) : Name :=
  .synthetic base kind 0

/-- Create a fresh synthetic name -/
def freshSyntheticName (baseName : String) (kind : SyntheticKind) : LowerM Name := do
  let base ← freshUnique baseName
  pure (mkSyntheticName base kind)

/-- Create an intrinsic name -/
def mkIntrinsicName (i : Intrinsic) : Name := .intrinsic i

/-- Create a runtime function name -/
def mkRuntimeName (fn : RuntimeFn) : Name := .intrinsic (.runtime fn)

/-- Create a primitive op name -/
def mkPrimOpName (op : PrimOp) : Name := .intrinsic (.primOp op)

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
        let globalInfo : GlobalInfo := { name := ctorInfo.name, typeSyntax := none, definedAt := ctorInfo.span }
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

/-- Run the lowering monad with an initial GlobalEnv for external symbols -/
def runWithEnv (m : LowerM α) (moduleName : String) (initialEnv : GlobalEnv) : α × LowerState :=
  StateT.run m (LowerState.withExternalSymbols moduleName initialEnv)

/-- Run and extract just the result -/
def run' (m : LowerM α) (moduleName : String) : α :=
  (run m moduleName).1

/-- Run and extract just the errors -/
def runErrors (m : LowerM α) (moduleName : String) : Array LowerError :=
  (run m moduleName).2.errors

end LowerM

end Soma.Metal.Lower
