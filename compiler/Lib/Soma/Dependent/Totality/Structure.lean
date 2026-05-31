import Soma.Dependent.Totality.Core
import Soma.Core.Expr

namespace Soma.Dependent.Totality

open Soma.Core
open Soma (Unique)

/-- A recursive (or mutual) call discovered in a body -/
structure RawCall where
  callee : String
  args : Array Expr
  env : List (Option Prov)
  deriving Inhabited

/-- Accumulated results of analyzing one function body -/
structure FnAnalysis where
  /-- All structural positions tracked for this function -/
  dims : Array Prov
  /-- Every recursive/mutual call in the body -/
  calls : Array RawCall
  deriving Inhabited

/-- Resolve the structural position denoted by an expression -/
partial def provOf (paramIdx : Std.HashMap Unique Nat) (env : List (Option Prov))
    : Expr → Option Prov
  | .fvar u _ => (paramIdx.get? u).map (fun i => { root := i, path := [] })
  | .bvar i => env[i]?.bind id
  | .fieldAccess e f _ => (provOf paramIdx env e).map (·.extend (.field f))
  | .ann e _ => provOf paramIdx env e
  | _ => none

/-- Resolve the structural position of `e` navigated along `path` -/
partial def resolvePos (paramIdx : Std.HashMap Unique Nat) (env : List (Option Prov))
    (e : Expr) (path : AccessPath) : Option Prov :=
  match path with
  | [] => provOf paramIdx env e
  | proj :: rest =>
    match e, proj with
    | .construct name _ args _, .con c j =>
      if name.display == c then
        match args[j]? with
        | some a => resolvePos paramIdx env a rest
        | none => none
      else none
    | .inject label args _, .variant l j =>
      if label == l then
        match args[j]? with
        | some a => resolvePos paramIdx env a rest
        | none => none
      else none
    | .tuple es, .tuple j =>
      match es[j]? with
      | some a => resolvePos paramIdx env a rest
      | none => none
    | .record fields, .field nm =>
      match fields.find? (·.1 == nm) with
      | some (_, v) => resolvePos paramIdx env v rest
      | none => none
    | .ann e' _, _ => resolvePos paramIdx env e' path
    | _, _ =>
      (provOf paramIdx env e).map (·.extendAll path)

/-- Mutable accumulator for the body walk -/
private structure WalkState where
  dims : Std.HashSet Prov := {}
  calls : Array RawCall := #[]

private def WalkState.addDim (s : WalkState) : Option Prov → WalkState
  | some p => { s with dims := s.dims.insert p }
  | none => s

/-- Collect the application spine `(f a b c)` into `(f, [a, b, c])` -/
private partial def appSpine (e : Expr) : Expr × Array Expr :=
  let rec go (e : Expr) (acc : Array Expr) : Expr × Array Expr :=
    match e with
    | .app fn arg => go fn (acc.push arg)
    | _ => (e, acc)
  let (head, revArgs) := go e #[]
  (head, revArgs.reverse)

/-- Walk a pattern -/
private partial def collectPattern (pat : Pattern) (pos : Option Prov)
    : StateM WalkState (Array (Option Prov)) := do
  match pat with
  | .var (some _) =>
    modify (·.addDim pos)
    return #[pos]
  | .var none => return #[]
  | .wildcard => return #[]
  | .lit _ => return #[]
  | .ctor name _ fields => do
    modify (·.addDim pos)
    let mut acc : Array (Option Prov) := #[]
    for j in [:fields.size] do
      let fieldPos := pos.map (·.extend (.con name.display j))
      acc := acc ++ (← collectPattern fields[j]! fieldPos)
    return acc
  | .inject label arg => do
    modify (·.addDim pos)
    match arg with
    | some p => collectPattern p (pos.map (·.extend (.variant label 0)))
    | none => return #[]

/-- Walk a function body -/
private partial def walk (paramIdx : Std.HashMap Unique Nat) (targets : Std.HashSet String)
    (env : List (Option Prov)) (e : Expr) : StateM WalkState Unit := do
  let recordIfTarget (name : QualifiedName) (args : Array Expr) : StateM WalkState Unit := do
    if targets.contains name.display then
      modify fun s => { s with calls := s.calls.push { callee := name.display, args, env } }
  match e with
  | .bvar _ | .fvar _ _ | .mvar _ | .tyvar _ _ | .lit _ | .sort _
  | .rowSort | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ => pure ()
  | .const name _ => recordIfTarget name #[]
  | .app _ _ =>
    let (head, args) := appSpine e
    match head with
    | .const name _ => recordIfTarget name args
    | _ => walk paramIdx targets env head
    for a in args do walk paramIdx targets env a
  | .lam _ _ d b =>
    walk paramIdx targets env d
    walk paramIdx targets (none :: env) b
  | .let_ _ t v b =>
    walk paramIdx targets env t
    walk paramIdx targets env v
    walk paramIdx targets (provOf paramIdx env v :: env) b
  | .pi _ _ _ d c =>
    walk paramIdx targets env d
    walk paramIdx targets (none :: env) c
  | .construct _ _ args _ => for a in args do walk paramIdx targets env a
  | .«case» scruts motive arms =>
    for s in scruts do walk paramIdx targets env s
    walk paramIdx targets env motive
    let scrutProvs := scruts.map (provOf paramIdx env ·)
    for arm in arms do
      let pats := arm.patterns
      let mut binderProvs : Array (Option Prov) := #[]
      for i in [:pats.size] do
        let pos := scrutProvs[i]?.bind id
        binderProvs := binderProvs ++ (← collectPattern pats[i]! pos)
      -- Body bound variable `bvar j` is the `(k-1-j)`-th binding, so the innermost de-Bruijn slot holds the last binding
      let env' := binderProvs.reverse.toList ++ env
      walk paramIdx targets env' arm.body
  | .record fields => for (_, v) in fields do walk paramIdx targets env v
  | .recordUpdate base updates =>
    walk paramIdx targets env base
    for (_, v) in updates do walk paramIdx targets env v
  | .fieldAccess e _ _ => walk paramIdx targets env e
  | .inject _ args _ => for a in args do walk paramIdx targets env a
  | .if_ c t el =>
    walk paramIdx targets env c
    walk paramIdx targets env t
    walk paramIdx targets env el
  | .closure _ caps _ => for c in caps do walk paramIdx targets env c
  | .array es _ => for a in es do walk paramIdx targets env a
  | .tuple es => for a in es do walk paramIdx targets env a
  | .rowExtend l f t =>
    walk paramIdx targets env l
    walk paramIdx targets env f
    walk paramIdx targets env t
  | .recordTy r => walk paramIdx targets env r
  | .variantTy r => walk paramIdx targets env r
  | .dataTy _ ps => for p in ps do walk paramIdx targets env p
  | .ann ex t =>
    walk paramIdx targets env ex
    walk paramIdx targets env t

/-- Analyze a function body -/
def analyzeFunction (params : Array Unique) (targets : Std.HashSet String) (body : Expr)
    : FnAnalysis :=
  let paramIdx : Std.HashMap Unique Nat :=
    params.foldl (init := ({}, 0)) (fun (m, i) u => (m.insert u i, i + 1)) |>.1
  let seedDims : Std.HashSet Prov :=
    (Array.range params.size).foldl (init := {}) fun s i => s.insert { root := i, path := [] }
  let init : WalkState := { dims := seedDims, calls := #[] }
  let (_, st) := (walk paramIdx targets [] body).run init
  { dims := st.dims.toArray, calls := st.calls }

/-- Build a size-change matrix entry set for one call -/
def callRelations (paramIdx : Std.HashMap Unique Nat) (callerDims : Array Prov)
    (calleeDims : Array Prov) (call : RawCall) : Array (Prov × Prov × SizeRel) := Id.run do
  let mut out : Array (Prov × Prov × SizeRel) := #[]
  for cDim in calleeDims do
    let resolved? : Option Prov :=
      match call.args[cDim.root]? with
      | some a => resolvePos paramIdx call.env a cDim.path
      | none => none
    match resolved? with
    | none => pure ()
    | some r =>
      for dDim in callerDims do
        if dDim.root == r.root then
          if dDim.path == r.path then
            out := out.push (dDim, cDim, .le)
          else if AccessPath.isPrefixOf dDim.path r.path then
            out := out.push (dDim, cDim, .lt)
  return out

end Soma.Dependent.Totality
