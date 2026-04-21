-- import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Primitive
import Soma.Core.Quote
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Error
import Soma.Dependent.Infer
import Soma.Syntax.Ast

namespace Soma.Dependent.Elaborate

open Soma.Core
open Soma.Syntax (Span)

/-- Environment for tracking type variables during elaboration -/
structure ElabEnv where
  /-- Type variables in scope: name -> (level, kind) -/
  tyVars : List (String × DeBruijnLvl × Value)
  /-- Current De Bruijn level -/
  level : Nat := 0
  /-- Value overrides: type variable name -> pre-allocated Value -/
  overrides : List (String × Value) := []
  deriving Inhabited

namespace ElabEnv

def empty : ElabEnv := { tyVars := [], level := 0, overrides := [] }

/-- Extend the environment with a new type variable -/
def extend (env : ElabEnv) (name : String) (kind : Value) : ElabEnv :=
  { env with
    tyVars := (name, ⟨env.level⟩, kind) :: env.tyVars
  , level := env.level + 1
  }

/-- Add a value override for a type variable name -/
def addOverride (env : ElabEnv) (name : String) (val : Value) : ElabEnv :=
  { env with overrides := (name, val) :: env.overrides }

end ElabEnv

/-- Elaborate a type expression to a Value through the unified `inferTypeExpr` path -/
partial def elaborateType (env : ElabEnv) (ty : Soma.Syntax.Expr) : TCM Value := do
  let tyTy : Value := Value.vType Level.zero
  let go : TCM Value := do
    let expr ← Soma.Dependent.inferTypeExpr ty
    TCM.evalExpr expr
  -- Sort `tyVars` by level ascending so we push bindings outermost-first
  let sortedTyVars : List (String × DeBruijnLvl × Value) :=
    env.tyVars.toArray.qsort (fun a b => a.2.1.lvl < b.2.1.lvl) |>.toList
  let withTyVars : TCM Value :=
    sortedTyVars.foldr (init := go)
      (fun (name, _lvl, kind) acc => do
        let uid ← TCM.freshLocalId name
        TCM.withBinding name uid kind .omega .implicit Span.uninhabited acc)
  env.overrides.foldr (init := withTyVars)
    (fun (name, val) acc => do
      let uid ← TCM.freshLocalId name
      TCM.withBindingValue name uid tyTy .omega .implicit Span.uninhabited val acc)

end Soma.Dependent.Elaborate
