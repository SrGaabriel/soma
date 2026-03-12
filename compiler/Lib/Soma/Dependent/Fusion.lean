import Soma.Core.Expr
import Soma.Core.Function
import Soma.Dependent.Monad

namespace Soma.Dependent.Fusion

open Soma.Core (Expr QualifiedName Arm Pattern BinderInfo Literal TypedFunction PrimType)
open Soma (Unique)
open Soma.Dependent (Globals WiredIn WiredRole)

/-- Semantic roles for fusion-eligible list operations -/
inductive FusionRole where
  | map | filter | foldl | foldr
  | sum | product | length | any | all
  deriving BEq, Hashable, Repr

/-- Dummy type for synthetic lambda domains -/
private def dummyTy : Expr := .sort .zero

/-- Split args into leading type-level args and trailing value-level args -/
private def splitTypeValueArgs (args : Array Expr) : Array Expr × Array Expr := Id.run do
  let mut i := 0
  for arg in args do
    if arg.isTypeLevelExpr then i := i + 1
    else break
  (args.extract 0 i, args.extract i args.size)

/-- Fusion context -/
structure FusionCtx where
  /-- Map from wired-in Unique → FusionRole -/
  roles : Std.HashMap Unique FusionRole := {}
  /-- Post-specialization bodies of named consumer functions (sum, product) -/
  consumerBodies : Std.HashMap FusionRole Expr := {}

/-- Resolve the fusion role of a `.const` expression via wired-in Uniques -/
private def constFusionRole (ctx : FusionCtx) : Expr → Option FusionRole
  | .const qn _ => ctx.roles.get? qn.id
  | _ => none

/-- Build a fusion context from the wired-in registry and typed function map -/
def buildFusionCtx
    (fns : Std.HashMap String TypedFunction)
    (globals : Globals) : FusionCtx := Id.run do
  let mut roles : Std.HashMap Unique FusionRole := {}
  let wiredRolePairs : Array (WiredRole × FusionRole) := #[
    (.listMap,     .map),     (.listFilter,  .filter),
    (.listFoldl,   .foldl),   (.listFoldr,   .foldr),
    (.listSum,     .sum),     (.listProduct, .product),
    (.listLength,  .length),  (.listAny,     .any),
    (.listAll,     .all)
  ]
  for (wr, fr) in wiredRolePairs do
    match globals.wiredIn.getUnique? wr with
    | some info => roles := roles.insert info.name.id fr
    | none => pure ()
  let mut bodies : Std.HashMap FusionRole Expr := {}
  for (consumerName, role) in #[("sum", FusionRole.sum), ("product", FusionRole.product)] do
    match fns.get? consumerName with
    | some fn =>
      if roles.get? fn.name.id == some role then
        bodies := bodies.insert role fn.body
    | none => pure ()
  return { roles, consumerBodies := bodies }

/-- Check if an expression is a known list producer call (map, filter) -/
private def isProducerCall (ctx : FusionCtx) (e : Expr) : Bool :=
  let (head, args) := e.collectAppSpine
  let (_, valArgs) := splitTypeValueArgs args
  match constFusionRole ctx head with
  | some .map    => valArgs.size == 2
  | some .filter => valArgs.size == 2
  | _ => false

/-- Inline single-use let bindings where the value is a producer call and the
    body contains a consumer applied to that binding -/
private partial def inlineProducerLets (ctx : FusionCtx) (e : Expr) : Expr :=
  match e with
  | .let_ name ty val body =>
    let val' := inlineProducerLets ctx val
    let body' := inlineProducerLets ctx body
    if isProducerCall ctx val' then
      let uses := body'.countBVar
      if uses == 1 then
        body'.instantiate val'
      else
        .let_ name ty val' body'
    else
      .let_ name ty val' body'
  | .lam info n d b => .lam info n d (inlineProducerLets ctx b)
  | .app f a => .app (inlineProducerLets ctx f) (inlineProducerLets ctx a)
  | .«case» scruts arms resultTy =>
    .«case» (scruts.map (inlineProducerLets ctx))
      (arms.map fun arm => Arm.mk arm.patterns (inlineProducerLets ctx arm.body))
      resultTy
  | .if_ c t el => .if_ (inlineProducerLets ctx c) (inlineProducerLets ctx t) (inlineProducerLets ctx el)
  | .construct n tag args rty => .construct n tag (args.map (inlineProducerLets ctx)) rty
  | .pair f s => .pair (inlineProducerLets ctx f) (inlineProducerLets ctx s)
  | .record _ => e
  | _ => e

/-- When fusing `foldl {A} {B} g z (map {C} {A} f xs)`, the element type
    changes from A (map output) to C (map input) -/
private def adjustFoldTypeArgsForMap (foldTyArgs mapTyArgs : Array Expr) : Array Expr :=
  if foldTyArgs.size >= 2 && mapTyArgs.size >= 1 then
    #[mapTyArgs[0]!, foldTyArgs[1]!]
  else
    foldTyArgs

/-- When fusing `map {A} {C} f (map {D} {A} g xs)`, the input type becomes D
    and the output type stays C -/
private def adjustMapTypeArgs (outerTyArgs innerTyArgs : Array Expr) : Array Expr :=
  if outerTyArgs.size >= 2 && innerTyArgs.size >= 1 then
    #[innerTyArgs[0]!, outerTyArgs[1]!]
  else
    outerTyArgs

mutual

/-- The main recursive fusion driver -/
private partial def fuseExpr (ctx : FusionCtx) (e : Expr) : Expr :=
  let e := fuseChildren ctx e
  fuseFixpoint ctx e

/-- Apply fusion rules repeatedly until fixpoint -/
private partial def fuseFixpoint (ctx : FusionCtx) (e : Expr) : Expr :=
  let (head, args) := e.collectAppSpine
  match head with
  | .const _ _ =>
    match tryFuse ctx head args with
    | some fused => fuseFixpoint ctx fused
    | none => e
  | _ => e

/-- Recursively fuse children of a non-application expression -/
private partial def fuseChildren (ctx : FusionCtx) (e : Expr) : Expr :=
  match e with
  | .app f a => .app (fuseExpr ctx f) (fuseExpr ctx a)
  | .lam info name domain body =>
    .lam info name domain (fuseExpr ctx body)
  | .let_ name ty val body =>
    .let_ name ty (fuseExpr ctx val) (fuseExpr ctx body)
  | .«case» scruts arms resultTy =>
    .«case» (scruts.map (fuseExpr ctx))
      (arms.map fun arm => Arm.mk arm.patterns (fuseExpr ctx arm.body))
      (fuseExpr ctx resultTy)
  | .if_ c t el => .if_ (fuseExpr ctx c) (fuseExpr ctx t) (fuseExpr ctx el)
  | .construct name tag args resultTy =>
    .construct name tag (args.map (fuseExpr ctx)) (fuseExpr ctx resultTy)
  | .pair f s => .pair (fuseExpr ctx f) (fuseExpr ctx s)
  | .projFst x => .projFst (fuseExpr ctx x)
  | .projSnd x => .projSnd (fuseExpr ctx x)
  | .fieldAccess x f i => .fieldAccess (fuseExpr ctx x) f i
  | .inject l args rty => .inject l (args.map (fuseExpr ctx)) (fuseExpr ctx rty)
  | .closure name caps => .closure name (caps.map (fuseExpr ctx))
  | .array es ety => .array (es.map (fuseExpr ctx)) (fuseExpr ctx ety)
  | .tuple es => .tuple (es.map (fuseExpr ctx))
  | .ann x t => .ann (fuseExpr ctx x) (fuseExpr ctx t)
  | .record _ => e
  | _ => e

/-- Try to fuse a top-level application spine -/
private partial def tryFuse (ctx : FusionCtx) (head : Expr) (args : Array Expr) : Option Expr :=
  let role := constFusionRole ctx head
  let (tyArgs, valArgs) := splitTypeValueArgs args
  match role with
  | some .foldl =>
    if valArgs.size == 3 then
      fuseFoldWithProducer ctx head tyArgs valArgs[0]! valArgs[1]! valArgs[2]! false
    else none
  | some .foldr =>
    if valArgs.size == 3 then
      fuseFoldWithProducer ctx head tyArgs valArgs[0]! valArgs[1]! valArgs[2]! true
    else none
  | some .sum =>
    if valArgs.size == 1 then fuseNamedConsumer ctx .sum valArgs[0]!
    else none
  | some .product =>
    if valArgs.size == 1 then fuseNamedConsumer ctx .product valArgs[0]!
    else none
  | some .length =>
    if valArgs.size == 1 then fuseLengthWithProducer ctx head tyArgs valArgs[0]!
    else none
  | some .map =>
    if valArgs.size == 2 then fuseMapWithProducer ctx head tyArgs valArgs[0]! valArgs[1]!
    else none
  | some .filter =>
    if valArgs.size == 2 then fuseFilterWithProducer ctx head tyArgs valArgs[0]! valArgs[1]!
    else none
  | some .any | some .all =>
    if valArgs.size == 2 then
      fusePredicateWithProducer ctx head tyArgs valArgs[0]! valArgs[1]!
    else none
  | _ => none

/-- Fuse `foldl/foldr g z (map f xs)` or `foldl/foldr g z (filter p xs)` -/
private partial def fuseFoldWithProducer
    (ctx : FusionCtx) (outerHead : Expr) (outerTyArgs : Array Expr)
    (g z listArg : Expr) (isRight : Bool) : Option Expr :=
  let (innerHead, innerArgs) := listArg.collectAppSpine
  let (innerTyArgs, innerValArgs) := splitTypeValueArgs innerArgs
  match constFusionRole ctx innerHead with
  | some .map =>
    if innerValArgs.size != 2 then none
    else
      let f := innerValArgs[0]!
      let xs := innerValArgs[1]!
      let newG :=
        if isRight then
          -- foldr: g : a → b → b, so fused = λ x acc → g (f x) acc
          let g' := g.shiftUp 2
          let f' := f.shiftUp 2
          Expr.lam .explicit "x" dummyTy
            (.lam .explicit "acc" dummyTy
              (.app (.app g' (.app f' (.bvar 1))) (.bvar 0)))
        else
          -- foldl: g : b → a → b, so fused = λ acc x → g acc (f x)
          let g' := g.shiftUp 2
          let f' := f.shiftUp 2
          Expr.lam .explicit "acc" dummyTy
            (.lam .explicit "x" dummyTy
              (.app (.app g' (.bvar 1)) (.app f' (.bvar 0))))
      let newTyArgs := adjustFoldTypeArgsForMap outerTyArgs innerTyArgs
      some (Expr.rebuildAppSpine outerHead (newTyArgs ++ #[newG, z, xs]))
  -- foldl/r g z (filter p xs)
  | some .filter =>
    if innerValArgs.size != 2 then none
    else
      let p := innerValArgs[0]!
      let xs := innerValArgs[1]!
      let newG :=
        if isRight then
          -- foldr: λ x acc → if p x then g x acc else acc
          let g' := g.shiftUp 2
          let p' := p.shiftUp 2
          Expr.lam .explicit "x" dummyTy
            (.lam .explicit "acc" dummyTy
              (.if_ (.app p' (.bvar 1))
                    (.app (.app g' (.bvar 1)) (.bvar 0))
                    (.bvar 0)))
        else
          -- foldl: λ acc x → if p x then g acc x else acc
          let g' := g.shiftUp 2
          let p' := p.shiftUp 2
          Expr.lam .explicit "acc" dummyTy
            (.lam .explicit "x" dummyTy
              (.if_ (.app p' (.bvar 0))
                    (.app (.app g' (.bvar 1)) (.bvar 0))
                    (.bvar 1)))
      -- filter preserves element type, so type args unchanged
      some (Expr.rebuildAppSpine outerHead (outerTyArgs ++ #[newG, z, xs]))
  | _ => none

/-- Fuse `sum/product (map f xs)` or `sum/product (filter p xs)` -/
private partial def fuseNamedConsumer
    (ctx : FusionCtx) (role : FusionRole)
    (listArg : Expr) : Option Expr :=
  -- Only inline if the argument is a producer (otherwise no fusion opportunity)
  let (innerHead, _) := listArg.collectAppSpine
  match constFusionRole ctx innerHead with
  | some .map | some .filter =>
    match ctx.consumerBodies.get? role with
    | some consumerBody =>
      -- consumerBody has bvar(0) for its list argument
      -- Instantiate to get: foldl (λ acc x → specialized_op acc x) identity listArg
      some (consumerBody.instantiate listArg)
    | none => none
  | _ => none

/-- Fuse `length (map _ xs)` → `length xs` -/
private partial def fuseLengthWithProducer
    (ctx : FusionCtx) (outerHead : Expr) (outerTyArgs : Array Expr)
    (listArg : Expr) : Option Expr :=
  let (innerHead, innerArgs) := listArg.collectAppSpine
  let (innerTyArgs, innerValArgs) := splitTypeValueArgs innerArgs
  match constFusionRole ctx innerHead with
  | some .map =>
    if innerValArgs.size != 2 then none
    else
      let xs := innerValArgs[1]!
      let newTyArgs := if innerTyArgs.size >= 1 then #[innerTyArgs[0]!] else outerTyArgs
      some (Expr.rebuildAppSpine outerHead (newTyArgs ++ #[xs]))
  | _ => none

/-- Fuse `map f (map g xs)` → `map (λ x → f (g x)) xs` -/
private partial def fuseMapWithProducer
    (ctx : FusionCtx) (outerHead : Expr) (outerTyArgs : Array Expr)
    (f listArg : Expr) : Option Expr :=
  let (innerHead, innerArgs) := listArg.collectAppSpine
  let (innerTyArgs, innerValArgs) := splitTypeValueArgs innerArgs
  match constFusionRole ctx innerHead with
  | some .map =>
    if innerValArgs.size != 2 then none
    else
      let g := innerValArgs[0]!
      let xs := innerValArgs[1]!
      let f' := f.shiftUp 1
      let g' := g.shiftUp 1
      let newF := Expr.lam .explicit "x" dummyTy
        (.app f' (.app g' (.bvar 0)))
      let newTyArgs := adjustMapTypeArgs outerTyArgs innerTyArgs
      some (Expr.rebuildAppSpine outerHead (newTyArgs ++ #[newF, xs]))
  | _ => none

/-- Fuse `filter p (filter q xs)` → `filter (λ x → if q x then p x else false) xs` -/
private partial def fuseFilterWithProducer
    (ctx : FusionCtx) (outerHead : Expr) (outerTyArgs : Array Expr)
    (p listArg : Expr) : Option Expr :=
  let (innerHead, innerArgs) := listArg.collectAppSpine
  let (_, innerValArgs) := splitTypeValueArgs innerArgs
  match constFusionRole ctx innerHead with
  | some .filter =>
    if innerValArgs.size != 2 then none
    else
      let q := innerValArgs[0]!
      let xs := innerValArgs[1]!
      let p' := p.shiftUp 1
      let q' := q.shiftUp 1
      let newP := Expr.lam .explicit "x" dummyTy
        (.if_ (.app q' (.bvar 0))
              (.app p' (.bvar 0))
              (.lit (.bool false)))
      some (Expr.rebuildAppSpine outerHead (outerTyArgs ++ #[newP, xs]))
  | _ => none

/-- Fuse `any/all pred (map f xs)` → `any/all (λ x → pred (f x)) xs` -/
private partial def fusePredicateWithProducer
    (ctx : FusionCtx) (outerHead : Expr) (outerTyArgs : Array Expr)
    (pred listArg : Expr) : Option Expr :=
  let (innerHead, innerArgs) := listArg.collectAppSpine
  let (innerTyArgs, innerValArgs) := splitTypeValueArgs innerArgs
  match constFusionRole ctx innerHead with
  | some .map =>
    if innerValArgs.size != 2 then none
    else
      let f := innerValArgs[0]!
      let xs := innerValArgs[1]!
      let pred' := pred.shiftUp 1
      let f' := f.shiftUp 1
      let newPred := Expr.lam .explicit "x" dummyTy
        (.app pred' (.app f' (.bvar 0)))
      let newTyArgs := if innerTyArgs.size >= 1 then #[innerTyArgs[0]!] else outerTyArgs
      some (Expr.rebuildAppSpine outerHead (newTyArgs ++ #[newPred, xs]))
  | _ => none

end

/-- Apply build/fold fusion to a single TypedFunction -/
def fuseFunction (ctx : FusionCtx) (fn : TypedFunction) : TypedFunction :=
  let inlined := inlineProducerLets ctx fn.body
  let fused := fuseExpr ctx inlined
  let reduced := fused.betaReduce
  { fn with body := reduced }

/-- Apply build/fold fusion to all typed functions in a module -/
def fuseAll
    (fns : Std.HashMap String TypedFunction)
    (globals : Globals)
    : Std.HashMap String TypedFunction := Id.run do
  let ctx := buildFusionCtx fns globals
  -- If no fusible functions are wired-in, skip the pass entirely
  if ctx.roles.isEmpty then return fns
  let mut result : Std.HashMap String TypedFunction := {}
  for (name, fn) in fns.toList do
    result := result.insert name (fuseFunction ctx fn)
  result

end Soma.Dependent.Fusion
