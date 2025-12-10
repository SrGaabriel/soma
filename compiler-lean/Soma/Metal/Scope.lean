import Soma.Metal.Name

namespace Soma.Metal

/-- A scope is a list of binding IDs (newest bindings first) -/
abbrev Scope := List BindingId

/-- Evidence that a binding is in scope -/
abbrev InScope (b : BindingId) (s : Scope) := b ∈ s

/-- A scoped variable - a binding with proof it's in scope -/
structure ScopedVar (scope : Scope) where
  binding : BindingId
  original : String
  proof : InScope binding scope

namespace ScopedVar

instance : ToString (ScopedVar s) := ⟨fun v => v.original⟩

/-- Weaken a scoped variable to a larger scope -/
def weaken {s : Scope} (v : ScopedVar s) (b : BindingId) : ScopedVar (b :: s) :=
  { binding := v.binding
  , original := v.original
  , proof := List.Mem.tail b v.proof
  }

/-- Weaken by prepending multiple bindings -/
def weakenMany {s : Scope} (v : ScopedVar s) (bs : List BindingId) : ScopedVar (bs ++ s) :=
  match bs with
  | [] => v
  | b :: rest =>
    -- v : ScopedVar s
    -- Need: ScopedVar ((b :: rest) ++ s) = ScopedVar (b :: (rest ++ s))
    let v' : ScopedVar (rest ++ s) := v.weakenMany rest
    v'.weaken b

/-- Create a variable for the most recently bound ID -/
def here (b : BindingId) (orig : String) (s : Scope) : ScopedVar (b :: s) :=
  { binding := b
  , original := orig
  , proof := List.Mem.head _
  }

end ScopedVar

/-- Environment mapping source names to scoped variables -/
structure ScopeEnv (scope : Scope) where
  bindings : List (String × ScopedVar scope)

namespace ScopeEnv

/-- Empty scope environment -/
def empty : ScopeEnv [] := ⟨[]⟩

/-- Look up a name in the scope environment -/
def lookup (env : ScopeEnv scope) (name : String) : Option (ScopedVar scope) :=
  env.bindings.find? (fun (n, _) => n == name) |>.map Prod.snd

/-- Extend the environment with a new binding -/
def extend (env : ScopeEnv scope) (b : BindingId) (name : String) : ScopeEnv (b :: scope) :=
  let weakened := env.bindings.map fun (n, v) => (n, v.weaken b)
  let newVar := ScopedVar.here b name scope
  ⟨(name, newVar) :: weakened⟩

/-- Extend with multiple bindings at once.
    The first binding in the list becomes the innermost (most recently bound).
    Result scope is `bindings.map Prod.fst ++ scope`. -/
def extendMany (env : ScopeEnv scope) (bindings : List (BindingId × String))
    : ScopeEnv (bindings.map Prod.fst ++ scope) :=
  match bindings with
  | [] => env
  | (b, name) :: rest =>
    -- First extend with the rest (recursively)
    let env' : ScopeEnv (rest.map Prod.fst ++ scope) := extendMany env rest
    -- Then extend with b at the front
    let env'' : ScopeEnv (b :: (rest.map Prod.fst ++ scope)) := env'.extend b name
    -- The result type is ((b, name) :: rest).map Prod.fst ++ scope
    --                  = (b :: rest.map Prod.fst) ++ scope
    --                  = b :: (rest.map Prod.fst ++ scope)  -- by List.cons_append
    -- So env'' has exactly the right type
    env''

end ScopeEnv

end Soma.Metal
