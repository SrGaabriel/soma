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

def isLess : LPOResult → Bool
  | .less => true
  | _ => false

def combine (r1 r2 : LPOResult) : LPOResult :=
  match r1, r2 with
  | .less, .less => .less
  | .less, .equal => .less
  | .equal, .less => .less
  | .equal, .equal => .equal
  | .greater, _ => .greater
  | _, .greater => .greater
  | _, _ => .incomparable

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

  | .pair f1 s1, .pair f2 s2 =>
    compareLPOArgs [f1, s1] [f2, s2] ctx

  -- Projections: compare inner terms
  | .fstProj i1, .fstProj i2 => compareLPO i1 i2 ctx
  | .sndProj i1, .sndProj i2 => compareLPO i1 i2 ctx

  -- Projection is less than the whole
  | .fstProj i1, t2 =>
    if compareLPO i1 t2 ctx == .equal then .less
    else .incomparable
  | .sndProj i1, t2 =>
    if compareLPO i1 t2 ctx == .equal then .less
    else .incomparable

  -- Variable is subterm of constructor => less
  | .var _, .ctor _ args2 =>
    if args2.any (fun a => compareLPO t1 a ctx == .equal) then .less
    else if args2.any (fun a => compareLPO t1 a ctx == .less) then .less
    else .incomparable

  | .var _, .pair fst2 snd2 =>
    if compareLPO t1 fst2 ctx == .equal || compareLPO t1 fst2 ctx == .less then .less
    else if compareLPO t1 snd2 ctx == .equal || compareLPO t1 snd2 ctx == .less then .less
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

/-- Check termination using LPO for a recursive call -/
def checkLPOTermination (args : List Soma.Core.Expr) (ctx : TerminationContext) : Option String :=
  let argShapes := args.map analyzeExprShape
  let paramShapes := ctx.params.toList.map fun p => TermShape.var p

  let results := argShapes.zip paramShapes |>.map fun (arg, param) =>
    compareLPO arg param ctx

  let rec check (rs : List LPOResult) (idx : Nat) : Option String :=
    match rs with
    | [] => none
    | .less :: _ => some s!"LPO decrease on argument {idx}"
    | .equal :: rest => check rest (idx + 1)
    | _ => none
  check results 0

/-! ## Coinductive Types and Productivity Checking -/

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

def empty : CodataRegistry := { types := {} }

def register (r : CodataRegistry) (info : CodataInfo) : CodataRegistry :=
  { r with types := r.types.insert info.name info }

def lookup (r : CodataRegistry) (name : String) : Option CodataInfo :=
  r.types.get? name

def isCodata (r : CodataRegistry) (name : String) : Bool :=
  r.types.contains name

def isConstructor (r : CodataRegistry) (ctorName : String) : Bool :=
  r.types.toList.any fun (_, info) => info.constructors.contains ctorName

end CodataRegistry

/-- Collect the head and spine of nested applications -/
private partial def collectAppSpine (e : Soma.Core.Expr) : Soma.Core.Expr × List Soma.Core.Expr :=
  match e with
  | .app fn arg =>
    let (head, args) := collectAppSpine fn
    (head, args ++ [arg])
  | _ => (e, [])

/-- Check if a term is productive (all corecursive calls are guarded) -/
partial def checkProductivity (fnName : String) (body : Soma.Core.Expr) (codata : CodataRegistry)
    : Guardedness :=
  go body .unguarded
where
  go (t : Soma.Core.Expr) (guard : Guardedness) : Guardedness :=
    match t with
    | .construct name _ args _ =>
      if codata.isConstructor name.display then
        let newGuard := match guard with
          | .guarded d => .guarded (d + 1)
          | .unguarded => .guarded 1
          | .mixed => .mixed
        args.foldl (fun g arg => combineGuardedness g (go arg newGuard)) newGuard
      else
        args.foldl (fun g arg => combineGuardedness g (go arg guard)) guard

    | .app _ _ =>
      let (head, args) := collectAppSpine t
      match head with
      | .const name _ =>
        if name.display == fnName then
          match guard with
          | .guarded _ => args.foldl (fun g arg => combineGuardedness g (go arg guard)) guard
          | .unguarded => .unguarded
          | .mixed => .mixed
        else
          let g := go head guard
          args.foldl (fun g' arg => combineGuardedness g' (go arg guard)) g
      | _ =>
        let g := go head guard
        args.foldl (fun g' arg => combineGuardedness g' (go arg guard)) g

    | .lam _ _ _ body => go body guard

    | .«case» scruts arms _ =>
      let g := scruts.foldl (fun g' s => combineGuardedness g' (go s guard)) guard
      arms.toList.foldl (fun g' arm => combineGuardedness g' (go arm.body guard)) g

    | .if_ c th el =>
      let g1 := go c guard
      let g2 := go th guard
      let g3 := go el guard
      combineGuardedness g1 (combineGuardedness g2 g3)

    | .pair a b => combineGuardedness (go a guard) (go b guard)

    | .projFst e => go e guard
    | .projSnd e => go e guard

    | .record fields =>
      fields.foldl (fun g (_, v) => combineGuardedness g (go v guard)) guard

    | _ => guard

  combineGuardedness (g1 g2 : Guardedness) : Guardedness :=
    match g1, g2 with
    | .guarded d1, .guarded d2 => .guarded (min d1 d2)
    | .guarded _, .unguarded => .mixed
    | .unguarded, .guarded _ => .mixed
    | .unguarded, .unguarded => .unguarded
    | .mixed, _ => .mixed
    | _, .mixed => .mixed

/-- Check productivity for a function -/
def checkCodataProductivity (fnName : String) (body : Soma.Core.Expr) (codata : CodataRegistry)
    : Bool × String :=
  match checkProductivity fnName body codata with
  | .guarded depth => (true, s!"productive: guarded at depth {depth}")
  | .unguarded => (false, "unproductive: unguarded corecursive call")
  | .mixed => (false, "unproductive: some corecursive calls are unguarded")

end Soma.Dependent.Totality
