import Soma.Dependent.Totality.Core
import Soma.Dependent.Totality.TermShape
import Soma.Dependent.Totality.CallMatrix
import Soma.Core.Expr

namespace Soma.Dependent.Totality

open Soma.Core

/-- Ordering result for LPO comparison -/
inductive LPOResult where
  | less        -- Strictly less
  | equal       -- Equal
  | greater     -- Strictly greater
  | incomparable -- Cannot compare
  deriving Repr, BEq, Inhabited

namespace LPOResult

end LPOResult

/-- Compare two term shapes using LPO.
    Key insight: a term is less if it's a proper subterm, or if it's
    a constructor application where the arguments are lexicographically less. -/
partial def compareLPO (t1 t2 : TermShape) (ctx : TerminationContext) : LPOResult :=
  match t1, t2 with
  -- Variables: compare by their structural depth
  | .var n1, .var n2 =>
    if n1 == n2 then .equal
    else
      match ctx.lookup n1, ctx.lookup n2 with
      | some i1, some i2 =>
        if i1.depth > i2.depth then .less      -- Deeper = came from more unwrapping = smaller
        else if i1.depth < i2.depth then .greater
        else if i1.paramIdx == i2.paramIdx then .equal
        else .incomparable
      | _, _ => .incomparable

  -- Constructor vs constructor
  | .ctor n1 args1, .ctor n2 args2 =>
    if n1 == n2 && args1.size == args2.size then
      compareLPOArgs args1.toList args2.toList ctx
    else
      if args2.any (fun a => compareLPO t1 a ctx == .equal) then .less
      else if args2.any (fun a => compareLPO t1 a ctx == .less) then .less
      else .incomparable

  -- Variable is subterm of constructor => less
  | .var _, .ctor _ args2 =>
    if args2.any (fun a => compareLPO t1 a ctx == .equal) then .less
    else if args2.any (fun a => compareLPO t1 a ctx == .less) then .less
    else .incomparable

  | _, _ => .incomparable
where
  compareLPOArgs (args1 args2 : List TermShape) (ctx : TerminationContext) : LPOResult :=
    match args1, args2 with
    | [], [] => .equal
    | a1 :: rest1, a2 :: rest2 =>
      match compareLPO a1 a2 ctx with
      | .less => .less
      | .equal => compareLPOArgs rest1 rest2 ctx
      | .greater => .greater
      | .incomparable => .incomparable
    | _, _ => .incomparable

/-- Whether a type is inductive or coinductive -/
inductive Inductivity where
  | inductive_    -- Regular inductive type (must terminate)
  | coinductive   -- Coinductive type (must be productive)
  deriving Repr, BEq, Inhabited

/-- Guardedness status for productivity checking -/
inductive Guardedness where
  | guarded (depth : Nat)     -- Under `depth` constructors
  | unguarded                 -- Not under any constructor
  | mixed                     -- Some paths guarded, some not
  deriving Repr, BEq, Inhabited

/-- Information about a coinductive type -/
structure CodataInfo where
  unique : Unique
  name : String
  constructors : Array String
  deriving Repr, Inhabited

/-- Registry for coinductive types -/
structure CodataRegistry where
  types : Std.HashMap String CodataInfo
  deriving Inhabited

namespace CodataRegistry


end CodataRegistry

/-- Collect the head and spine of nested applications -/
private partial def collectAppSpine (e : Soma.Core.Expr) : Soma.Core.Expr × List Soma.Core.Expr :=
  match e with
  | .app fn arg =>
    let (head, args) := collectAppSpine fn
    (head, args ++ [arg])
  | _ => (e, [])

end Soma.Dependent.Totality
