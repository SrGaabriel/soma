import Soma.Infer.Error
import Soma.Infer.Substitution

namespace Soma.Infer

open Soma.Typing
open Soma.Syntax

/-- State for unification: substitution and fresh counter -/
structure UnifyState where
  subst : Subst
  freshCounter : Nat
  deriving Inhabited

/-- Result of unification -/
abbrev UnifyResult := Except InferError UnifyState

/-- Information about a nominal type's row structure for unification -/
structure NominalTypeRow where
  /-- The row type representing the struct's fields -/
  row : RowTy

instance : Inhabited NominalTypeRow where
  default := { row := .rowEmpty }

/-- Function type to look up a nominal type's row structure by TypeId -/
abbrev TypeRowLookup := TypeId → Option NominalTypeRow

/-- Context for unification operations -/
structure UnifyContext where
  /-- The purpose of this unification (for error messages) -/
  purpose : UnifyPurpose
  /-- Span of the "expected" type -/
  expectedSpan : Span
  /-- Span of the "actual" type -/
  actualSpan : Span
  /-- Optional lookup for nominal type row structures -/
  lookupTypeRow : TypeRowLookup := fun _ => none

namespace Unify

/-- Create initial unify state with a given fresh counter -/
def initState (freshCounter : Nat := 0) : UnifyState :=
  { subst := Subst.empty, freshCounter }

/-- Create a state with just a substitution -/
def stateFromSubst (σ : Subst) (counter : Nat) : UnifyState :=
  { subst := σ, freshCounter := counter }

/-- Compose two unify states -/
def composeState (s1 s2 : UnifyState) : UnifyState :=
  { subst := s2.subst.compose s1.subst, freshCounter := s2.freshCounter }

/-- Generate a fresh row variable -/
def freshRowVar (name : String) (counter : Nat) : (RowTy × Nat) :=
  let v : TyVarId := { name := name, id := counter, kind := .row }
  (.var v, counter + 1)

mutual
/-- Check if a type variable occurs in a list of types -/
def occursInList (varId : Nat) : List MonoTy → Bool
  | [] => false
  | t :: rest => occursK varId t || occursInList varId rest

/-- Check if a type variable occurs in a type (kind-polymorphic occurs check) -/
def occursK (varId : Nat) : {k : Kind} → Ty k → Bool
  | _, .var v => v.id == varId
  | _, .starPrim _ => false
  | _, .higherPrim _ => false
  | _, .userCon _ _ => false
  | _, .app f a => occursK varId f || occursK varId a
  | _, .arrow from_ to => occursK varId from_ || occursK varId to
  | _, .tuple fst snd rest =>
    occursK varId fst || occursK varId snd || occursInList varId rest
  | _, .labelLit _ => false
  | _, .rowEmpty => false
  | _, .rowExtend label ty tail =>
    occursK varId label || occursK varId ty || occursK varId tail
  | _, .record row => occursK varId row
  | _, .variant row => occursK varId row
end

/-- Check if a type variable occurs in a label type -/
def occursInLabel (varId : Nat) (label : LabelTy) : Bool :=
  occursK varId label

/-- Check if a type variable occurs in a row type -/
def occursInRow (varId : Nat) (row : RowTy) : Bool :=
  occursK varId row

/-- Monomorphic occurs check (for backwards compatibility) -/
def occurs (varId : Nat) (ty : MonoTy) : Bool := occursK varId ty

/-- Bind a type variable to a type of the same kind, with occurs check -/
def bindVarK {k : Kind} (v : TyVarId) (ty : Ty k) (ctx : UnifyContext) (counter : Nat) : UnifyResult :=
  -- If binding to itself, return empty substitution
  match ty with
  | .var v' =>
    if v.id == v'.id then
      .ok { subst := Subst.empty, freshCounter := counter }
    else if occursK v.id ty then
      -- For error message, we need a MonoTy - use a placeholder
      .error (.occursCheck v (.var ⟨s!"<kind {k}>", 0, .star⟩) ctx.actualSpan)
    else
      .ok { subst := Subst.singletonAny v.id ⟨k, ty⟩, freshCounter := counter }
  | _ =>
    if occursK v.id ty then
      .error (.occursCheck v (.var ⟨s!"<kind {k}>", 0, .star⟩) ctx.actualSpan)
    else
      .ok { subst := Subst.singletonAny v.id ⟨k, ty⟩, freshCounter := counter }

/-- Bind a monomorphic type variable -/
def bindVar (v : TyVarId) (ty : MonoTy) (ctx : UnifyContext) (counter : Nat) : UnifyResult :=
  bindVarK v ty ctx counter

/-- Bind a label variable -/
def bindLabelVar (v : TyVarId) (label : LabelTy) (ctx : UnifyContext) (counter : Nat) : UnifyResult :=
  if occursInLabel v.id label then
    .error (.occursCheck v (.var ⟨"<label>", 0, .star⟩) ctx.actualSpan)
  else
    .ok { subst := Subst.singletonAny v.id ⟨.label, label⟩, freshCounter := counter }

/-- Bind a row variable -/
def bindRowVar (v : TyVarId) (row : RowTy) (ctx : UnifyContext) (counter : Nat) : UnifyResult :=
  if occursInRow v.id row then
    .error (.occursCheck v (.var ⟨"<row>", 0, .star⟩) ctx.actualSpan)
  else
    .ok { subst := Subst.singletonAny v.id ⟨.row, row⟩, freshCounter := counter }

/-- Unify two label types -/
def unifyLabel (l1 l2 : LabelTy) (ctx : UnifyContext) (counter : Nat) : UnifyResult :=
  match l1, l2 with
  -- Two literal labels: must be equal
  | .labelLit n1, .labelLit n2 =>
    if n1 == n2 then .ok (initState counter)
    else .error (.labelMismatch n1 n2 ctx.actualSpan)
  -- Variable on left: bind
  | .var v, label => bindLabelVar v label ctx counter
  -- Variable on right: symmetric
  | label, .var v => bindLabelVar v label ctx counter
  -- Catch-all for impossible cases
  | _, _ => .ok (initState counter)

/-- Find the row variable at the tail of a row, along with the prefix fields.
    Returns (variable, list of (label, type) pairs from head to variable) -/
def findRowTailVar (row : RowTy) : Option (TyVarId × List (LabelTy × MonoTy)) :=
  match row with
  | .rowEmpty => none
  | .var v => some (v, [])
  | .rowExtend label ty tail => do
    let (v, prefix_) ← findRowTailVar tail
    some (v, (label, ty) :: prefix_)
  | _ => none

/-- Rebuild a row from a prefix list and a new tail -/
def rebuildRowWithTail (prefix_ : List (LabelTy × MonoTy)) (tail : RowTy) : RowTy :=
  prefix_.foldr (init := tail) fun (label, ty) acc => .rowExtend label ty acc

/-- Collect all concrete (literal) labels from a row type -/
def collectConcreteLabels (row : RowTy) : Array String :=
  match row with
  | .rowEmpty => #[]
  | .var _ => #[]
  | .rowExtend label _ tail =>
    match label with
    | .labelLit name => #[name] ++ collectConcreteLabels tail
    | .var _ => collectConcreteLabels tail -- Skip label variables
    | _ => collectConcreteLabels tail -- Impossible cases
  | _ => #[] -- Impossible cases

/-- Rewrite a row to bring a specific concrete label to the front.
    Returns (fieldType, rowWithoutLabel) if label is found.
    Only works for concrete labels—label variables are not searched. -/
def rowRewrite (name : String) (row : RowTy) : Option (MonoTy × RowTy) :=
  match row with
  | .rowEmpty => none
  | .rowExtend label ty tail =>
    match label with
    | .labelLit n =>
      if n == name then some (ty, tail)
      else do
        let (fieldTy, rest) ← rowRewrite name tail
        some (fieldTy, .rowExtend label ty rest)
    | _ => none  -- Cannot rewrite through label variable or impossible cases
  | _ => none  -- Cannot rewrite through row variable or impossible cases

mutual
  /-- Unify two row types with row rewriting -/
  partial def unifyRow (r1 r2 : RowTy) (ctx : UnifyContext) (counter : Nat) : UnifyResult := do
    -- Quick equality check
    if Ty.heq r1 r2 then return initState counter
    -- Match on the structure
    match r1, r2 with
    | .rowEmpty, .rowEmpty => .ok (initState counter)
    | .var v, row => bindRowVar v row ctx counter
    | row, .var v => bindRowVar v row ctx counter
    | .rowExtend l1 t1 tail1, .rowExtend l2 t2 tail2 =>
      match l1, l2 with
      | .labelLit n1, .labelLit n2 =>
        if n1 == n2 then
          -- Same label: unify types and tails
          let s1 ← unifyMono t1 t2 ctx counter
          let s2 ← unifyRow (s1.subst.applyRow tail1) (s1.subst.applyRow tail2) ctx s1.freshCounter
          .ok (composeState s1 s2)
        else
          -- Different labels: try row rewriting on both sides
          match rowRewrite n1 r2 with
          | some (t1', tail2') =>
            let s1 ← unifyMono t1 t1' ctx counter
            let s2 ← unifyRow (s1.subst.applyRow tail1) (s1.subst.applyRow tail2') ctx s1.freshCounter
            .ok (composeState s1 s2)
          | none =>
            -- n1 not in r2, try to find n2 in r1
            match rowRewrite n2 r1 with
            | some (t2', tail1') =>
              let s1 ← unifyMono t2' t2 ctx counter
              let s2 ← unifyRow (s1.subst.applyRow tail1') (s1.subst.applyRow tail2) ctx s1.freshCounter
              .ok (composeState s1 s2)
            | none =>
              -- Neither label found in the other via rewriting
              -- For these rows to unify, both must end up containing both labels
              let (freshTail, counter') := freshRowVar "r" counter
              let row1Extended := Ty.rowExtend l2 t2 freshTail
              let row2Extended := Ty.rowExtend l1 t1 freshTail
              let s1 ← unifyRow tail1 row1Extended ctx counter'
              let s2 ← unifyRow (s1.subst.applyRow tail2) (s1.subst.applyRow row2Extended) ctx s1.freshCounter
              .ok (composeState s1 s2)
      | _, _ =>
        match l1, l2 with
        | .var _, .labelLit name2 =>
          -- l1 is a variable, l2 is concrete. Check if r2 has multiple concrete labels...
          let allLabels := #[name2] ++ collectConcreteLabels tail2
          if allLabels.size > 1 then
            .error (.ambiguousLabel allLabels ctx.actualSpan)
          else
            -- Only one field, proceed with unification
            let s1 ← unifyLabel l1 l2 ctx counter
            let s2 ← unifyMono (s1.subst.apply t1) (s1.subst.apply t2) ctx s1.freshCounter
            let s12 := composeState s1 s2
            let s3 ← unifyRow (s12.subst.applyRow tail1) (s12.subst.applyRow tail2) ctx s12.freshCounter
            .ok (composeState s12 s3)
        | .labelLit name1, .var _ =>
          -- l1 is concrete, l2 is a variable. Check if r1 has multiple concrete labels.
          let allLabels := #[name1] ++ collectConcreteLabels tail1
          if allLabels.size > 1 then
            .error (.ambiguousLabel allLabels ctx.actualSpan)
          else
            -- Only one field, proceed with unification
            let s1 ← unifyLabel l1 l2 ctx counter
            let s2 ← unifyMono (s1.subst.apply t1) (s1.subst.apply t2) ctx s1.freshCounter
            let s12 := composeState s1 s2
            let s3 ← unifyRow (s12.subst.applyRow tail1) (s12.subst.applyRow tail2) ctx s12.freshCounter
            .ok (composeState s12 s3)
        | _, _ =>
          -- Both are variables or other cases: unify labels directly
          let s1 ← unifyLabel l1 l2 ctx counter
          let s2 ← unifyMono (s1.subst.apply t1) (s1.subst.apply t2) ctx s1.freshCounter
          let s12 := composeState s1 s2
          let s3 ← unifyRow (s12.subst.applyRow tail1) (s12.subst.applyRow tail2) ctx s12.freshCounter
          .ok (composeState s12 s3)
    | .rowEmpty, .rowExtend l _ _ =>
      match l with
      | .labelLit name => .error (.extraRowField name ctx.actualSpan)
      | _ => .error (.rowMismatch r1 r2 ctx.actualSpan)
    | .rowExtend l _ _, .rowEmpty =>
      match l with
      | .labelLit name => .error (.missingRowField name ctx.actualSpan)
      | _ => .error (.rowMismatch r1 r2 ctx.actualSpan)
    | _, _ => .ok (initState counter)  -- Catch-all for impossible cases

  /-- Unify two monomorphic types (kind *) -/
  partial def unifyMono (t1 t2 : MonoTy) (ctx : UnifyContext) (counter : Nat) : UnifyResult := do
    -- Quick equality check
    if t1 == t2 then
      return initState counter

    match t1, t2 with
    | .var v1, .var v2 =>
      if v1.id == v2.id then
        return initState counter
      else
        -- Prefer binding the one with higher ID
        if v1.id > v2.id then
          bindVar v1 t2 ctx counter
        else
          bindVar v2 t1 ctx counter

    | .var v, t =>
      bindVar v t ctx counter

    | t, .var v =>
      bindVar v t ctx counter

    -- Primitive types
    | .starPrim p1, .starPrim p2 =>
      if p1 == p2 then
        return initState counter
      else
        .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)

    -- Type constructors
    | .userCon _ id1, .userCon _ id2 =>
      if id1 == id2 then
        return initState counter
      else
        .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)

    -- Function types
    | .arrow from1 to1, .arrow from2 to2 => do
      let s1 ← unifyMono from1 from2 ctx counter
      let s2 ← unifyMono (s1.subst.apply to1) (s1.subst.apply to2) ctx s1.freshCounter
      return composeState s1 s2

    -- Type application
    | .app f1 a1, .app f2 a2 =>
      unifyAppSome ⟨_, f1⟩ ⟨_, a1⟩ ⟨_, f2⟩ ⟨_, a2⟩ ctx counter

    -- Tuple types
    | .tuple fst1 snd1 rest1, .tuple fst2 snd2 rest2 =>
      if rest1.length != rest2.length then
        .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)
      else do
        let s1 ← unifyMono fst1 fst2 ctx counter
        let s2 ← unifyMono (s1.subst.apply snd1) (s1.subst.apply snd2) ctx s1.freshCounter
        let s12 := composeState s1 s2
        unifyLists (rest1.map s12.subst.apply) (rest2.map s12.subst.apply) s12 ctx

    -- Record types (structural)
    | .record r1, .record r2 =>
      unifyRow r1 r2 ctx counter

    -- Variant types (structural) uses same row unification
    | .variant r1, .variant r2 =>
      unifyRow r1 r2 ctx counter

    -- Nominal type vs structural record: expose nominal's row structure
    | .userCon _ id, .record row =>
      match ctx.lookupTypeRow id with
      | some nominalRow =>
        -- Unify the nominal type's row with the structural row
        unifyRow nominalRow.row row ctx counter
      | none =>
        -- No row info available, fall back to type mismatch
        .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)

    | .record row, .userCon _ id =>
      match ctx.lookupTypeRow id with
      | some nominalRow =>
        -- Unify the structural row with the nominal type's row
        unifyRow row nominalRow.row ctx counter
      | none =>
        -- No row info available, fall back to type mismatch
        .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)

    -- Mismatch cases
    | _, _ =>
      .error (.typeMismatch t1 t2 ctx.purpose ctx.expectedSpan ctx.actualSpan)

  /-- Unify two SomeTy values (heterogeneous unification) -/
  partial def unifySome (s1 s2 : SomeTy) (ctx : UnifyContext) (counter : Nat) : UnifyResult := do
    -- First check if kinds match
    if h : s1.kind = s2.kind then
      -- Kinds match - use homogeneous unification
      let t2' : Ty s1.kind := h ▸ s2.ty
      unifyAtKind s1.kind s1.ty t2' ctx counter
    else
      -- Kind mismatch - use the dedicated error variant
      .error (.kindMismatch s1.kind s2.kind ctx.actualSpan)

  /-- Unify two types at a given kind -/
  partial def unifyAtKind (k : Kind) (t1 t2 : Ty k) (ctx : UnifyContext) (counter : Nat) : UnifyResult :=
    match k, t1, t2 with
    -- Star kind: use monomorphic unification
    | .star, t1, t2 => unifyMono t1 t2 ctx counter
    -- Label kind
    | .label, t1, t2 => unifyLabel t1 t2 ctx counter
    -- Row kind
    | .row, t1, t2 => unifyRow t1 t2 ctx counter
    -- Arrow kinds: handle type constructor unification inline
    | .arrow _ _, .var v1, .var v2 =>
      if v1.id == v2.id then .ok (initState counter)
      else if v1.id > v2.id then bindVarK v1 t2 ctx counter
      else bindVarK v2 t1 ctx counter
    | .arrow _ _, .var v, t => bindVarK v t ctx counter
    | .arrow _ _, t, .var v => bindVarK v t ctx counter
    | .arrow _ _, .higherPrim p1, .higherPrim p2 =>
      if p1 == p2 then .ok (initState counter)
      else .error (.typeMismatch (.var ⟨s!"{p1}", 0, .star⟩) (.var ⟨s!"{p2}", 0, .star⟩) ctx.purpose ctx.expectedSpan ctx.actualSpan)
    | .arrow _ _, .userCon _ id1, .userCon _ id2 =>
      if id1 == id2 then .ok (initState counter)
      else .error (.typeMismatch (.var ⟨id1.name, 0, .star⟩) (.var ⟨id2.name, 0, .star⟩) ctx.purpose ctx.expectedSpan ctx.actualSpan)
    | .arrow _ _, .app f1 a1, .app f2 a2 =>
      unifyAppSome ⟨_, f1⟩ ⟨_, a1⟩ ⟨_, f2⟩ ⟨_, a2⟩ ctx counter
    | .arrow _ _, _, _ =>
      .error (.typeMismatch (.var ⟨"_", 0, .star⟩) (.var ⟨"_", 0, .star⟩) ctx.purpose ctx.expectedSpan ctx.actualSpan)

  /-- Unify two arrow-kinded types -/
  partial def unifyArrowK (k1 k2 : Kind) (t1 t2 : Ty (.arrow k1 k2)) (ctx : UnifyContext) (counter : Nat) : UnifyResult := do
    match t1, t2 with
    -- Both are type variables - bind one to the other
    | .var v1, .var v2 =>
      if v1.id == v2.id then
        return initState counter
      else if v1.id > v2.id then
        bindVarK v1 t2 ctx counter
      else
        bindVarK v2 t1 ctx counter

    -- One is a variable, bind it
    | .var v, t => bindVarK v t ctx counter
    | t, .var v => bindVarK v t ctx counter

    -- Both are higher primitives
    | .higherPrim p1, .higherPrim p2 =>
      if p1 == p2 then return initState counter
      else .error (.typeMismatch (.var ⟨s!"{p1}", 0, .star⟩) (.var ⟨s!"{p2}", 0, .star⟩) ctx.purpose ctx.expectedSpan ctx.actualSpan)

    -- Both are user-defined type constructors
    | .userCon _ id1, .userCon _ id2 =>
      if id1 == id2 then return initState counter
      else .error (.typeMismatch (.var ⟨id1.name, 0, .star⟩) (.var ⟨id2.name, 0, .star⟩) ctx.purpose ctx.expectedSpan ctx.actualSpan)

    -- Type application at arrow kind
    | .app f1 a1, .app f2 a2 =>
      unifyAppSome ⟨_, f1⟩ ⟨_, a1⟩ ⟨_, f2⟩ ⟨_, a2⟩ ctx counter

    -- Mismatch
    | _, _ =>
      .error (.typeMismatch (.var ⟨"_", 0, .star⟩) (.var ⟨"_", 0, .star⟩) ctx.purpose ctx.expectedSpan ctx.actualSpan)

  /-- Unify type applications using SomeTy to handle heterogeneous existential kinds -/
  partial def unifyAppSome (f1 a1 f2 a2 : SomeTy) (ctx : UnifyContext) (counter : Nat) : UnifyResult := do
    -- Unify the type constructors
    let s1 ← unifySome f1 f2 ctx counter
    -- Apply substitution and unify arguments
    let a1' := s1.subst.applySome a1
    let a2' := s1.subst.applySome a2
    let s2 ← unifySome a1' a2' ctx s1.freshCounter
    return composeState s1 s2

  /-- Unify two arrays of monomorphic types element-wise -/
  partial def unifyArrays (arr1 arr2 : Array MonoTy) (ctx : UnifyContext) (counter : Nat) : UnifyResult := do
    let mut state := initState counter
    for i in [:arr1.size] do
      if h : i < arr1.size ∧ i < arr2.size then
        let t1 := state.subst.apply arr1[i]
        let t2 := state.subst.apply arr2[i]
        let s ← unifyMono t1 t2 ctx state.freshCounter
        state := composeState state s
    return state

  /-- Unify two lists of monomorphic types element-wise, accumulating state -/
  partial def unifyLists (ts1 ts2 : List MonoTy) (acc : UnifyState) (ctx : UnifyContext) : UnifyResult := do
    match ts1, ts2 with
    | [], [] => return acc
    | t1 :: rest1, t2 :: rest2 =>
      let s ← unifyMono t1 t2 ctx acc.freshCounter
      let acc' := composeState acc s
      unifyLists (rest1.map acc'.subst.apply) (rest2.map acc'.subst.apply) acc' ctx
    | _, _ => return acc  -- Shouldn't happen if lengths match
end

/-- Simple unification with minimal context (for internal use) -/
def unify (t1 t2 : MonoTy) (span : Span) (counter : Nat := 0) : UnifyResult :=
  unifyMono t1 t2 { purpose := .general, expectedSpan := span, actualSpan := span } counter

/-- Unify with purpose context -/
def unifyWith (expected actual : MonoTy) (purpose : UnifyPurpose)
    (expectedSpan actualSpan : Span) (counter : Nat := 0) : UnifyResult :=
  unifyMono expected actual { purpose, expectedSpan, actualSpan } counter

/-- Unify a list of types to a single type -/
def unifyAll (types : Array MonoTy) (spans : Array Span) (purpose : UnifyPurpose) (counter : Nat := 0)
    : Except InferError (MonoTy × UnifyState) := do
  -- Assert that spans and types arrays have the same length
  if types.size != spans.size then
    panic! s!"unifyAll: types.size ({types.size}) != spans.size ({spans.size})"

  match types[0]? with
  | none => return (.starPrim .unit, initState counter)
  | some first =>
    let firstSpan := spans[0]!
    let mut result := first
    let mut state := initState counter
    for i in [1:types.size] do
      match types[i]? with
      | none => pure ()
      | some ty =>
        let tySpan := spans[i]!
        let ctx : UnifyContext := {
          purpose := purpose
          expectedSpan := firstSpan
          actualSpan := tySpan
        }
        let s ← unifyMono (state.subst.apply result) (state.subst.apply ty) ctx state.freshCounter
        state := composeState state s
        result := state.subst.apply result
    return (result, state)

end Unify

end Soma.Infer
