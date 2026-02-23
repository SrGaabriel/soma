import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Core.TypeId
import Soma.Dependent.Monad
import Soma.Dependent.Error
import Soma.Dependent.Prelude
import Soma.Unique

namespace Soma.Dependent.Totality

open Soma.Core
open Soma.Syntax (Span)
open Soma (Unique)

/-- A placeholder QualifiedName for use in Inhabited instances -/
def dummyName : QualifiedName := ⟨{ id := 0, module := "$totality", original := "$dummy" }⟩

/-- The totality status of a definition -/
inductive TotalityStatus where
  | isPartial -- Function is partial (default)
  | isTotal -- Function is total (verified to terminate)
  | isUnknown -- Function totality is unknown (needs checking)
  deriving Repr, BEq, Inhabited

/-- Information about a function for totality checking -/
structure FunctionInfo where
  name : QualifiedName
  markedTotal : Bool
  status : TotalityStatus
  params : Array String
  fnType : Value
  span : Span

instance : Inhabited FunctionInfo where
  default := {
    name := dummyName
    markedTotal := false
    status := .isPartial
    params := #[]
    fnType := Value.vType .zero
    span := Span.uninhabited
  }

/-- A path through a pattern structure -/
inductive StructurePath where
  | root -- The scrutinee itself
  | fst (parent : StructurePath) -- First of pair/tuple
  | snd (parent : StructurePath) -- Second of pair/tuple
  | field (parent : StructurePath) (name : String) -- Record field
  | ctorArg (parent : StructurePath) (ctor : String) (idx : Nat) -- Constructor argument
  deriving Repr, BEq, Inhabited

namespace StructurePath

/-- Compute the depth of a path (number of constructor unwrappings) -/
def depth : StructurePath → Nat
  | .root => 0
  | .fst p => p.depth -- Projection: same depth
  | .snd p => p.depth -- Projection: same depth
  | .field p _ => p.depth -- Projection: same depth
  | .ctorArg p _ _ => p.depth + 1 -- Constructor unwrap: +1 depth

/-- Pretty print a path for debugging -/
def toString : StructurePath → String
  | .root => "root"
  | .fst p => s!"{p.toString}.fst"
  | .snd p => s!"{p.toString}.snd"
  | .field p n => s!"{p.toString}.{n}"
  | .ctorArg p c i => s!"{p.toString}.{c}[{i}]"

instance : ToString StructurePath := ⟨toString⟩

end StructurePath

/-- Complete information about a pattern-bound variable -/
structure BindingInfo where
  name : String -- The variable name
  paramIdx : Nat -- Which function parameter this came from
  paramName : String -- Name of that parameter
  path : StructurePath -- Path through the pattern to this binding
  depth : Nat -- Precomputed depth for efficiency
  deriving Repr, Inhabited

namespace BindingInfo

/-- Is this binding strictly smaller than its source parameter? -/
def isSmaller (b : BindingInfo) : Bool := b.depth > 0

/-- Is this binding at the same level as its source parameter? -/
def isSameLevel (b : BindingInfo) : Bool := b.depth == 0

end BindingInfo

/-- Result of comparing a recursive call argument to the original pattern -/
inductive StructuralCmp where
  | smaller (reason : String)   -- Strictly smaller (terminates!)
  | equal                       -- Same size (continue lexicographic check)
  | larger                      -- Larger (fails unless earlier arg was smaller)
  | unknown                     -- Can't determine
  deriving Repr, BEq, Inhabited

namespace StructuralCmp

def isSmaller : StructuralCmp → Bool
  | .smaller _ => true
  | _ => false

def isEqual : StructuralCmp → Bool
  | .equal => true
  | _ => false

end StructuralCmp

/-- A decrease witness for termination checking -/
inductive DecreaseWitness where
  | arg (paramIdx : Nat) (reason : String) -- Decrease on a specific argument
  | lex (witnesses : Array DecreaseWitness) -- Lexicographic decrease
  | notFound (reason : String) -- No decrease found
  deriving Repr, Inhabited

/-- The termination checking context -/
structure TerminationContext where
  /-- Function parameters -/
  params : Array String
  /-- Map from variable name to binding info -/
  bindings : Std.HashMap String BindingInfo := {}
  /-- The current function being checked -/
  currentFn : Option FunctionInfo := none
  deriving Inhabited

namespace TerminationContext

def empty : TerminationContext := { params := #[] }

/-- Create a context from function parameters -/
def fromParams (params : Array String) : TerminationContext :=
  let bindings := params.foldl (init := ({}, 0)) fun (acc, idx) name =>
    let info : BindingInfo := {
      name := name
      paramIdx := idx
      paramName := name
      path := .root
      depth := 0
    }
    (acc.insert name info, idx + 1)
  { params := params, bindings := bindings.1 }

/-- Look up binding info for a variable -/
def lookup (ctx : TerminationContext) (name : String) : Option BindingInfo :=
  ctx.bindings.get? name

/-- Add a new binding (from pattern matching) -/
def addBinding (ctx : TerminationContext) (info : BindingInfo) : TerminationContext :=
  { ctx with bindings := ctx.bindings.insert info.name info }

/-- Add multiple bindings -/
def addBindings (ctx : TerminationContext) (infos : Array BindingInfo) : TerminationContext :=
  infos.foldl (fun c i => c.addBinding i) ctx

/-- Check if a variable is known to be smaller than some parameter -/
def isSmaller (ctx : TerminationContext) (name : String) : Bool :=
  match ctx.lookup name with
  | some info => info.isSmaller
  | none => false

end TerminationContext

/-- Information about a recursive call -/
structure RecursiveCallInfo where
  callSpan : Span
  callee : QualifiedName
  argNames : Array String
  decrease : DecreaseWitness

instance : Inhabited RecursiveCallInfo where
  default := {
    callSpan := Span.uninhabited
    callee := dummyName
    argNames := #[]
    decrease := .notFound ""
  }

/-- State for termination checking -/
structure TermState where
  currentFn : Option FunctionInfo := none
  ctx : TerminationContext := TerminationContext.empty
  recursiveCalls : Array RecursiveCallInfo := #[]
  errors : Array TCError := #[]
  deriving Inhabited

/-- Termination checking monad -/
abbrev TermM := StateT TermState (Except TCError)

namespace TermM

def run (m : TermM α) (state : TermState := {}) : Except TCError (α × TermState) :=
  m state

def run' (m : TermM α) (state : TermState := {}) : Except TCError α :=
  (m.run state).map (·.1)

def getState : TermM TermState := get
def modifyState (f : TermState → TermState) : TermM Unit := modify f
def throw (e : TCError) : TermM α := Except.error e

def addError (e : TCError) : TermM Unit :=
  modifyState fun s => { s with errors := s.errors.push e }

def getCurrentFn : TermM (Option FunctionInfo) := do
  return (← getState).currentFn

def setCurrentFn (fn : FunctionInfo) : TermM Unit :=
  modifyState fun s => { s with
    currentFn := some fn
    ctx := TerminationContext.fromParams fn.params
  }

def getContext : TermM TerminationContext := do
  return (← getState).ctx

def modifyContext (f : TerminationContext → TerminationContext) : TermM Unit :=
  modifyState fun s => { s with ctx := f s.ctx }

def addBinding (info : BindingInfo) : TermM Unit :=
  modifyContext (·.addBinding info)

def addBindings (infos : Array BindingInfo) : TermM Unit :=
  modifyContext (·.addBindings infos)

def recordRecursiveCall (info : RecursiveCallInfo) : TermM Unit :=
  modifyState fun s => { s with recursiveCalls := s.recursiveCalls.push info }

/-- Run an action with additional bindings, then restore the context -/
def withBindings (bindings : Array BindingInfo) (action : TermM α) : TermM α := do
  let saved := (← getState).ctx
  addBindings bindings
  let result ← action
  modifyState fun s => { s with ctx := saved }
  return result

-- Legacy compatibility
def markSmallerThan (varName : String) (paramIdx : Nat) (paramName : String) : TermM Unit := do
  addBinding {
    name := varName
    paramIdx := paramIdx
    paramName := paramName
    path := .ctorArg .root "pattern" 0
    depth := 1
  }

def markAllSmallerThan (varNames : List String) (paramIdx : Nat) (paramName : String) : TermM Unit := do
  for name in varNames do
    markSmallerThan name paramIdx paramName

def isSmallerThan (varName : String) : TermM (Option (Nat × String)) := do
  let ctx ← getContext
  match ctx.lookup varName with
  | some info => if info.isSmaller then return some (info.paramIdx, info.paramName) else return none
  | none => return none

def withSmallerBindings (bindings : List (String × Nat × String)) (action : TermM α) : TermM α := do
  let infos := bindings.map fun (name, paramIdx, paramName) => {
    name := name
    paramIdx := paramIdx
    paramName := paramName
    path := .ctorArg .root "pattern" 0
    depth := 1
  }
  withBindings infos.toArray action

def getSizeContext : TermM TerminationContext := getContext

end TermM

/-- Registry of function totality status -/
structure TotalityRegistry where
  functions : Std.HashMap String TotalityStatus := {}
  deriving Inhabited

namespace TotalityRegistry

def empty : TotalityRegistry := {}

def register (reg : TotalityRegistry) (name : String) (status : TotalityStatus) : TotalityRegistry :=
  { reg with functions := reg.functions.insert name status }

def lookup (reg : TotalityRegistry) (name : String) : Option TotalityStatus :=
  reg.functions.get? name

def isTotal (reg : TotalityRegistry) (name : String) : Bool :=
  match reg.lookup name with
  | some .isTotal => true
  | _ => false

end TotalityRegistry

/-- Result of totality checking -/
structure TotalityCheckResult where
  status : TotalityStatus
  errors : Array TCError
  recursiveCalls : Array RecursiveCallInfo
  deriving Inhabited

end Soma.Dependent.Totality
