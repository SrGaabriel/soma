import Soma.Dependent.Totality.Core
import Soma.Core.Expr

namespace Soma.Dependent.Totality

open Soma.Core

/-- A linear form `c + Σᵢ kᵢ·pᵢ` over function parameters -/
structure LinForm where
  const : Int := 0
  coeffs : Array Int := #[]
  deriving Repr, BEq, Inhabited

namespace LinForm

def ofConst (c : Int) : LinForm := { const := c, coeffs := #[] }

def ofParam (idx : Nat) : LinForm :=
  let coeffs := (List.replicate (idx + 1) (0 : Int)).toArray.set! idx 1
  { const := 0, coeffs := coeffs }

def coeff (f : LinForm) (i : Nat) : Int := f.coeffs[i]?.getD 0

def isNonNegConst (f : LinForm) : Bool :=
  f.const ≥ 0 && f.coeffs.all (· == 0)

private def widerSize (a b : LinForm) : Nat := max a.coeffs.size b.coeffs.size

/-- Component-wise sum -/
def add (a b : LinForm) : LinForm :=
  let n := widerSize a b
  let coeffs := (List.range n).toArray.map fun i => a.coeff i + b.coeff i
  { const := a.const + b.const, coeffs := coeffs }

/-- Component-wise negation -/
def neg (a : LinForm) : LinForm :=
  { const := -a.const, coeffs := a.coeffs.map (-·) }

/-- Component-wise difference -/
def sub (a b : LinForm) : LinForm := a.add b.neg

/-- Scale by a non-negative integer -/
def scale (f : LinForm) (k : Nat) : LinForm :=
  let kI : Int := Int.ofNat k
  { const := f.const * kI, coeffs := f.coeffs.map (· * kI) }

/-- Render for diagnostics -/
def toDisplay (f : LinForm) : String := Id.run do
  let mut parts : Array String := #[]
  let mut i := 0
  for c in f.coeffs do
    if c != 0 then
      let mag := if c < 0 then -c else c
      let coefStr := if mag == 1 then s!"p{i}" else s!"{mag}·p{i}"
      let sign := if c < 0 then "-" else if parts.isEmpty then "" else "+"
      parts := parts.push (sign ++ coefStr)
    i := i + 1
  if f.const != 0 then
    let sign := if f.const < 0 then "-" else if parts.isEmpty then "" else "+"
    let mag := if f.const < 0 then -f.const else f.const
    parts := parts.push (sign ++ toString mag)
  if parts.isEmpty then "0" else String.intercalate " " parts.toList

end LinForm

/-- A linear-arithmetic fact `f ≥ 0` -/
inductive LinAtom where
  | nonneg (f : LinForm)
  deriving Repr, Inhabited

namespace LinAtom

def fromLe (lhs rhs : LinForm) : LinAtom := .nonneg (rhs.sub lhs)
def fromLt (lhs rhs : LinForm) : LinAtom := .nonneg ((rhs.sub lhs).sub (LinForm.ofConst 1))
def fromGe (lhs rhs : LinForm) : LinAtom := fromLe rhs lhs
def fromGt (lhs rhs : LinForm) : LinAtom := fromLt rhs lhs

def negate : LinAtom → LinAtom
  | .nonneg f => .nonneg (f.neg.sub (LinForm.ofConst 1))

end LinAtom

/-- A conjunction of linear-arithmetic facts in normal form -/
structure LinCtx where
  facts : Array LinForm := #[]
  deriving Repr, Inhabited

namespace LinCtx

def empty : LinCtx := {}

def addAtom (ctx : LinCtx) : LinAtom → LinCtx
  | .nonneg f => { ctx with facts := ctx.facts.push f }

end LinCtx

/-- Collect an application spine `(f a b c)` into `(f, [a, b, c])` -/
private partial def appSpine (e : Expr) : Expr × List Expr :=
  match e with
  | .app fn arg =>
    let (head, args) := appSpine fn
    (head, args ++ [arg])
  | _ => (e, [])

/-- Extract a parameter-resolvable name from an expression -/
private def nameOf : Expr → Option String
  | .fvar id _ => some id.original
  | .const n _ => some n.display
  | _ => none

/-- Try to interpret `e` as a linear form over the function parameters -/
partial def analyzeLinForm (e : Expr) (params : Array String) : Option LinForm :=
  match e with
  | .lit (.int v) => some (LinForm.ofConst v)
  | .ann inner _ => analyzeLinForm inner params
  | _ =>
    match nameOf e with
    | some name => (params.findIdx? (· == name)).map LinForm.ofParam
    | none =>
      let (head, args) := appSpine e
      match head, args with
      | .const op _, [a, b] =>
        match analyzeLinForm a params, analyzeLinForm b params with
        | some aF, some bF =>
          match op.display with
          | "+" => some (aF.add bF)
          | "-" => some (aF.sub bF)
          | _ => none
        | _, _ => none
      | _, _ => none

/-- Recognise a boolean condition as a single linear-arithmetic atom -/
def analyzeCondAtom (cond : Expr) (params : Array String) : Option LinAtom :=
  let (head, args) := appSpine cond
  match head, args with
  | .const op _, [a, b] =>
    match analyzeLinForm a params, analyzeLinForm b params with
    | some aF, some bF =>
      match op.display with
      | "<=" => some (LinAtom.fromLe aF bF)
      | "<"  => some (LinAtom.fromLt aF bF)
      | ">=" => some (LinAtom.fromGe aF bF)
      | ">"  => some (LinAtom.fromGt aF bF)
      | _ => none
    | _, _ => none
  | _, _ => none

/-- Try to prove `query ≥ 0` -/
partial def entailsNonneg (ctx : LinCtx) (query : LinForm) : Bool :=
  go ctx.facts.toList query
where
  maxK : Nat := 2
  go (facts : List LinForm) (q : LinForm) : Bool :=
    match facts with
    | [] => q.isNonNegConst
    | f :: rest =>
      (List.range (maxK + 1)).any fun k => go rest (q.sub (f.scale k))

/-- A linear decrease witness -/
structure LinearWitness where
  measure : LinForm
  description : String
  deriving Repr, Inhabited

/-- Try to prove that a recursive call `f(arg₀, …)` decreases a linear measure `pⱼ − pᵢ` that the guard context keeps non-negative -/
def findLinearDecrease (params : Array String) (args : List Expr) (ctx : LinCtx)
    : Option LinearWitness :=
  let arity := params.size
  let argArr := args.toArray
  if argArr.size < arity then none
  else
    let argForms : Array (Option LinForm) := argArr.map (analyzeLinForm · params)
    let pairs : List (Nat × Nat) :=
      (List.range arity).flatMap fun i =>
        (List.range arity).filterMap fun j => if i == j then none else some (i, j)
    pairs.findSome? fun (i, j) =>
      match argForms[i]?, argForms[j]? with
      | some (some argI), some (some argJ) =>
        let measure := (LinForm.ofParam j).sub (LinForm.ofParam i)
        let afterCall := argJ.sub argI
        let strictMinusOne := (measure.sub afterCall).sub (LinForm.ofConst 1)
        if entailsNonneg ctx measure && entailsNonneg ctx strictMinusOne then
          let desc := s!"linear measure {measure.toDisplay} (≥ 0 by guard, ↓ {(measure.sub afterCall).toDisplay} per call)"
          some { measure, description := desc }
        else none
      | _, _ => none

end Soma.Dependent.Totality
