import Soma.Typing

namespace Soma.Metal

open Soma.Typing

/-- Unique identifier for a local binding site -/
structure BindingId where
  id : Nat
  deriving Repr, BEq, Hashable, Ord, DecidableEq, Inhabited

namespace BindingId

instance : ToString BindingId := ⟨fun b => s!"#{b.id}"⟩

def next (b : BindingId) : BindingId := ⟨b.id + 1⟩

end BindingId

/-- Kinds of synthetic (compiler-generated) names -/
inductive SyntheticKind where
  | closure
  | instanceMethod (forType : MonoTy)
  | erasure
  | temp
  deriving BEq

namespace SyntheticKind

def toString : SyntheticKind → String
  | .closure => "closure"
  | .instanceMethod ty => s!"instance_{ty}"
  | .erasure => "era"
  | .temp => "tmp"

instance : ToString SyntheticKind := ⟨SyntheticKind.toString⟩

end SyntheticKind

/-- A fully resolved name in Metal IR -/
inductive Name where
  | local (binding : BindingId) (original : String)
  | global (module : String) (name : String) (unique : Nat)
  | ctor (typeName : String) (ctorName : String) (tag : Nat)
  | synthetic (kind : SyntheticKind) (id : Nat)
  deriving BEq

namespace Name

/-- Get a display name for error messages and debugging -/
def display : Name → String
  | .local _ orig => orig
  | .global mod n _ => if mod.isEmpty then n else s!"{mod}.{n}"
  | .ctor ty c _ => s!"{ty}.{c}"
  | .synthetic k id => s!"${k}_{id}"

instance : ToString Name := ⟨Name.display⟩

/-- Check if this is a local binding -/
def isLocal : Name → Bool
  | .local _ _ => true
  | _ => false

/-- Check if this is a global name -/
def isGlobal : Name → Bool
  | .global _ _ _ => true
  | _ => false

/-- Check if this is a constructor -/
def isCtor : Name → Bool
  | .ctor _ _ _ => true
  | _ => false

/-- Check if this is synthetic -/
def isSynthetic : Name → Bool
  | .synthetic _ _ => true
  | _ => false

/-- Get the binding ID if this is a local name -/
def bindingId? : Name → Option BindingId
  | .local b _ => some b
  | _ => none

/-- Get the constructor tag if this is a constructor -/
def ctorTag? : Name → Option Nat
  | .ctor _ _ tag => some tag
  | _ => none

end Name

end Soma.Metal
