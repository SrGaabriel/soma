import Soma.Core.Expr
import Soma.Core.Function
import Soma.Core.Intrinsic
import Soma.Core.Quote
import Soma.Dependent.Monad

namespace Soma.Dependent.Fusion

open Soma.Core (Expr QualifiedName Arm Pattern BinderInfo Literal TypedFunction PrimType
                Intrinsic PrimOp)
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

/-- Resolved list constructor info for synthesizing Cons/Nil in cross-producer fusion -/
structure ListCtorInfo where
  consName : QualifiedName
  consTag  : Nat
  nilName  : QualifiedName
  nilTag   : Nat
  listTyId : Unique

/-- Resolved wired `Bool` constructor info -/
structure BoolCtorInfo where
  trueName  : QualifiedName
  trueTag   : Nat
  falseName : QualifiedName
  falseTag  : Nat
  boolTyId  : Unique

/-- Fusion context -/
structure FusionCtx where
  /-- Map from wired-in Unique → FusionRole -/
  roles : Std.HashMap Unique FusionRole := {}
  /-- Consumer function bodies (sum, product): their Expr bodies with bvar(0) for list param -/
  consumerBodies : Std.HashMap FusionRole Expr := {}
  /-- Fallback: foldl .const expression with correct type (when consumerBodies unavailable) -/
  foldlConst : Option Expr := none
  /-- reverse .const expression with correct type (for cross-producer fusion) -/
  reverseConst : Option Expr := none
  /-- Fallback: Int addition .const expression with correct type (for sum expansion) -/
  addConst : Option Expr := none
  /-- Fallback: Int multiplication .const expression with correct type (for product expansion) -/
  mulConst : Option Expr := none
  /-- List constructor info for cross-producer fusion (Cons, Nil, List type) -/
  listCtors : Option ListCtorInfo := none
  /-- The wired-in `Int` type -/
  intTyExpr : Option Expr := none
  /-- The wired-in `Bool` constructor info -/
  boolCtors : Option BoolCtorInfo := none

/-- Resolve the fusion role of a `.const` expression via wired-in Uniques -/
private def constFusionRole (ctx : FusionCtx) : Expr → Option FusionRole
  | .const qn _ => ctx.roles.get? qn.id
  | _ => none

/-- Build a fusion context from the wired-in registry and globals -/
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
  for (_, fn) in fns.toList do
    match roles.get? fn.name.id with
    | some role =>
      if role == .sum || role == .product then
        bodies := bodies.insert role fn.body
    | none => pure ()
  let mkConst (qn : QualifiedName) : Expr :=
    match globals.defs.get? qn with
    | some info => .const qn (Soma.Core.quoteExpr0 info.type)
    | none => .const qn dummyTy
  let foldlConst := match globals.wiredIn.getUnique? .listFoldl with
    | some info => some (mkConst info.name)
    | none => none
  let reverseConst := match globals.wiredIn.getUnique? .listReverse with
    | some info => some (mkConst info.name)
    | none => none
  -- Build reverse index: Unique → WiredRole (for efficient type→role lookup)
  let uniqueToRole : Std.HashMap Soma.Unique Soma.Dependent.WiredRole :=
    globals.wiredIn.roles.fold (init := {}) fun acc role infos =>
      infos.foldl (fun m info => m.insert info.name.id role) acc
  let isInt32Ty (v : Soma.Core.Value) : Bool :=
    match v with
    | .vDataType uid _ =>
      match uniqueToRole.get? uid with
      | some r => Soma.Dependent.WiredRole.primType? r == some PrimType.int
      | none => false
    | _ => false
  let isInt32Op (qn : QualifiedName) : Bool :=
    match globals.defs.get? qn with
    | some info =>
      match info.type with
      | .vPi _ _ _ dom _ => isInt32Ty dom
      | _ => false
    | none => false
  let mut addConst : Option Expr := none
  let mut mulConst : Option Expr := none
  for (qn, intrinsic) in globals.intrinsics.toList do
    match intrinsic with
    | .primOp .add =>
      if isInt32Op qn then addConst := some (mkConst qn)
    | .primOp .mul =>
      if isInt32Op qn then mulConst := some (mkConst qn)
    | _ => pure ()
  -- Resolve list constructors for cross-producer fusion
  let listCtors := do
    let consInfo ← globals.wiredIn.getUnique? .cons
    let nilInfo  ← globals.wiredIn.getUnique? .nil
    let listInfo ← globals.wiredIn.getUnique? .typeList
    let consDef  ← globals.defs.get? consInfo.name
    let nilDef   ← globals.defs.get? nilInfo.name
    guard consDef.isConstructor
    guard nilDef.isConstructor
    pure { consName := consInfo.name, consTag := consDef.ctorTag,
           nilName := nilInfo.name, nilTag := nilDef.ctorTag,
           listTyId := listInfo.name.id }
  let intTyExpr : Option Expr :=
    globals.wiredIn.getUnique? .typeInt |>.map fun info =>
      Expr.dataTy info.name.id #[]
  let boolCtors : Option BoolCtorInfo := do
    let boolInfo ← globals.wiredIn.getUnique? .typeBool
    let indMeta  ← globals.lookupInductive boolInfo.name
    let trueCtor  ← indMeta.ctors.find? (fun c => c.simpleName == "True")
    let falseCtor ← indMeta.ctors.find? (fun c => c.simpleName == "False")
    pure { trueName := trueCtor.name, trueTag := trueCtor.tag,
           falseName := falseCtor.name, falseTag := falseCtor.tag,
           boolTyId := boolInfo.name.id }
  return { roles, consumerBodies := bodies, foldlConst, reverseConst,
           addConst, mulConst, listCtors, intTyExpr, boolCtors }

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
  | .«case» scruts motive arms =>
    .«case» (scruts.map (inlineProducerLets ctx))
      motive
      (arms.map fun arm => Arm.mk arm.patterns (inlineProducerLets ctx arm.body))
  | .if_ c t el => .if_ (inlineProducerLets ctx c) (inlineProducerLets ctx t) (inlineProducerLets ctx el)
  | .construct n tag args rty => .construct n tag (args.map (inlineProducerLets ctx)) rty
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

/-- Helper: build `Cons x acc` as `construct consName consTag #[x, acc] (dataTy listTyId [elemTy])` -/
private def mkCons (lci : ListCtorInfo) (elemTy x acc : Expr) : Expr :=
  .construct lci.consName lci.consTag #[x, acc] (.dataTy lci.listTyId #[elemTy])

/-- Helper: build `Nil` as `construct nilName nilTag #[] (dataTy listTyId [elemTy])` -/
private def mkNil (lci : ListCtorInfo) (elemTy : Expr) : Expr :=
  .construct lci.nilName lci.nilTag #[] (.dataTy lci.listTyId #[elemTy])

/-- Resolve the wired `Int` type as a Core Expr for accumulator annotations -/
private def fusionIntTyExpr (ctx : FusionCtx) : Expr :=
  match ctx.intTyExpr with
  | some e => e
  | none   => dummyTy

/-- Build the wired `Bool` Core Expr type form -/
private def fusionBoolTyExpr (bci : BoolCtorInfo) : Expr :=
  .dataTy bci.boolTyId #[]

/-- Synthesize a literal Boolean Core term as the wired `Bool` constructor application -/
private def mkBoolLit (bci : BoolCtorInfo) (b : Bool) : Expr :=
  let (name, tag) := if b then (bci.trueName, bci.trueTag)
                          else (bci.falseName, bci.falseTag)
  .construct name tag #[] (fusionBoolTyExpr bci)

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
  | .«case» scruts motive arms =>
    .«case» (scruts.map (fuseExpr ctx))
      (fuseExpr ctx motive)
      (arms.map fun arm => Arm.mk arm.patterns (fuseExpr ctx arm.body))
  | .if_ c t el => .if_ (fuseExpr ctx c) (fuseExpr ctx t) (fuseExpr ctx el)
  | .construct name tag args resultTy =>
    .construct name tag (args.map (fuseExpr ctx)) (fuseExpr ctx resultTy)
  | .fieldAccess x f i => .fieldAccess (fuseExpr ctx x) f i
  | .inject l args rty => .inject l (args.map (fuseExpr ctx)) (fuseExpr ctx rty)
  | .closure name caps ty =>
    .closure name (caps.map (fuseExpr ctx)) (fuseExpr ctx ty)
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

/-- Fuse `foldl/foldr g z (map f xs)` or `foldl/foldr g z (filter p xs)`
    foldr {a} {b} : (a → b → b) → b → [a] → b → outerTyArgs = [a, b]
    foldl {a} {b} : (b → a → b) → b → [a] → b → outerTyArgs = [a, b]
    map {c} {a} f xs → innerTyArgs = [c, a]
    filter {a} p xs → innerTyArgs = [a] -/
private partial def fuseFoldWithProducer
    (ctx : FusionCtx) (outerHead : Expr) (outerTyArgs : Array Expr)
    (g z listArg : Expr) (isRight : Bool) : Option Expr :=
  let (innerHead, innerArgs) := listArg.collectAppSpine
  let (innerTyArgs, innerValArgs) := splitTypeValueArgs innerArgs
  let accTy  := outerTyArgs[1]?.getD dummyTy
  let elemTy := outerTyArgs[0]?.getD dummyTy
  match constFusionRole ctx innerHead with
  | some .map =>
    if innerValArgs.size != 2 then none
    else
      let f := innerValArgs[0]!
      let xs := innerValArgs[1]!
      -- After fusion with map {c} {a}: element type changes from a to c
      let fusedElemTy := innerTyArgs[0]?.getD elemTy
      let newG :=
        if isRight then
          -- foldr: g : a → b → b, so fused = λ x acc → g (f x) acc
          let g' := g.shiftUp 2
          let f' := f.shiftUp 2
          Expr.lam .explicit "x" fusedElemTy
            (.lam .explicit "acc" accTy
              (.app (.app g' (.app f' (.bvar 1))) (.bvar 0)))
        else
          -- foldl: g : b → a → b, so fused = λ acc x → g acc (f x)
          let g' := g.shiftUp 2
          let f' := f.shiftUp 2
          Expr.lam .explicit "acc" accTy
            (.lam .explicit "x" fusedElemTy
              (.app (.app g' (.bvar 1)) (.app f' (.bvar 0))))
      let newTyArgs := adjustFoldTypeArgsForMap outerTyArgs innerTyArgs
      some (Expr.rebuildAppSpine outerHead (newTyArgs ++ #[newG, z, xs]))
  -- foldl/r g z (filter p xs): filter preserves element type
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
          Expr.lam .explicit "x" elemTy
            (.lam .explicit "acc" accTy
              (.if_ (.app p' (.bvar 1))
                    (.app (.app g' (.bvar 1)) (.bvar 0))
                    (.bvar 0)))
        else
          -- foldl: λ acc x → if p x then g acc x else acc
          let g' := g.shiftUp 2
          let p' := p.shiftUp 2
          Expr.lam .explicit "acc" accTy
            (.lam .explicit "x" elemTy
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
  -- Only fuse if the argument is a producer (otherwise no fusion opportunity)
  let (innerHead, _) := listArg.collectAppSpine
  match constFusionRole ctx innerHead with
  | some .map | some .filter =>
    fuseNamedConsumerDirect ctx role listArg
  | _ => none

/-- Fallback direct construction for fuseNamedConsumer when consumer body is unavailable -/
private partial def fuseNamedConsumerDirect
    (ctx : FusionCtx) (role : FusionRole)
    (listArg : Expr) : Option Expr :=
  let (opConst?, identity) := match role with
    | .sum     => (ctx.addConst, Expr.lit (.int 0))
    | .product => (ctx.mulConst, Expr.lit (.int 1))
    | _ => (none, dummyTy)
  match opConst?, ctx.foldlConst with
  | some opConst, some foldlConst =>
    let intTy := fusionIntTyExpr ctx
    let (innerHead, innerArgs) := listArg.collectAppSpine
    let (innerTyArgs, innerValArgs) := splitTypeValueArgs innerArgs
    match constFusionRole ctx innerHead with
    | some .map =>
      if innerValArgs.size != 2 then none
      else
        let f := innerValArgs[0]!
        let xs := innerValArgs[1]!
        let f' := f.shiftUp 2
        -- For sum (map @A @B f xs): acc : B (= Int), x : A (map input type)
        let accTy := intTy
        let elemTy := if innerTyArgs.size >= 1 then innerTyArgs[0]! else intTy
        let fusedG := Expr.lam .explicit "acc" accTy
          (.lam .explicit "x" elemTy
            (.app (.app opConst (.bvar 1)) (.app f' (.bvar 0))))
        let foldlTyArgs := #[elemTy, intTy]
        some (Expr.rebuildAppSpine foldlConst (foldlTyArgs ++ #[fusedG, identity, xs]))
    | some .filter =>
      if innerValArgs.size != 2 then none
      else
        let p := innerValArgs[0]!
        let xs := innerValArgs[1]!
        let p' := p.shiftUp 2
        -- For sum (filter @A p xs): acc : Int, x : A (element type)
        let accTy := intTy
        let elemTy := if innerTyArgs.size >= 1 then innerTyArgs[0]! else intTy
        let fusedG := Expr.lam .explicit "acc" accTy
          (.lam .explicit "x" elemTy
            (.if_ (.app p' (.bvar 0))
              (.app (.app opConst (.bvar 1)) (.bvar 0))
              (.bvar 1)))
        let foldlTyArgs := #[elemTy, intTy]
        some (Expr.rebuildAppSpine foldlConst (foldlTyArgs ++ #[fusedG, identity, xs]))
    | _ => none
  | _, _ => none

/-- Fuse `length {a} (map {c} {a} _ xs)` → `length {c} xs`
    Fuse `length {a} (filter {a} p xs)` → `foldl {a} {Int} (λ acc x → if p x then acc+1 else acc) 0 xs` -/
private partial def fuseLengthWithProducer
    (ctx : FusionCtx) (outerHead : Expr) (outerTyArgs : Array Expr)
    (listArg : Expr) : Option Expr :=
  let (innerHead, innerArgs) := listArg.collectAppSpine
  let (innerTyArgs, innerValArgs) := splitTypeValueArgs innerArgs
  match constFusionRole ctx innerHead with
  | some .map =>
    if innerValArgs.size != 2 then none
    else
      -- length (map _ xs) → length xs: map doesn't change list length
      let xs := innerValArgs[1]!
      let newTyArgs := if innerTyArgs.size >= 1 then #[innerTyArgs[0]!] else outerTyArgs
      some (Expr.rebuildAppSpine outerHead (newTyArgs ++ #[xs]))
  | some .filter =>
    if innerValArgs.size != 2 then none
    else
      -- length (filter p xs) → foldl (λ acc x → if p x then acc+1 else acc) 0 xs
      match ctx.foldlConst, ctx.addConst with
      | some foldlConst, some addConst =>
        let intTy := fusionIntTyExpr ctx
        let p := innerValArgs[0]!
        let xs := innerValArgs[1]!
        let p' := p.shiftUp 2
        let accTy := intTy
        let elemTy := if innerTyArgs.size >= 1 then innerTyArgs[0]! else intTy
        let countG := Expr.lam .explicit "acc" accTy
          (.lam .explicit "x" elemTy
            (.if_ (.app p' (.bvar 0))
              (.app (.app addConst (.bvar 1)) (.lit (.int 1)))
              (.bvar 1)))
        let foldlTyArgs := #[elemTy, intTy]
        some (Expr.rebuildAppSpine foldlConst (foldlTyArgs ++ #[countG, .lit (.int 0), xs]))
      | _, _ => none
  | _ => none

/-- Fuse `map {a} {c} f (map {d} {a} g xs)` → `map {d} {c} (λ x → f (g x)) xs`
    Fuse `map {a} {b} f (filter {a} p xs)` → `foldr {a} {[b]} (λ x acc → if p x then Cons (f x) acc else acc) Nil xs` -/
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
      -- x has inner map's input type d
      let elemTy := innerTyArgs[0]?.getD dummyTy
      let newF := Expr.lam .explicit "x" elemTy
        (.app f' (.app g' (.bvar 0)))
      let newTyArgs := adjustMapTypeArgs outerTyArgs innerTyArgs
      some (Expr.rebuildAppSpine outerHead (newTyArgs ++ #[newF, xs]))
  | some .filter =>
    -- map f (filter p xs): eliminate intermediate filtered list
    -- → reverse (foldl (λ acc x → if p x then Cons (f x) acc else acc) Nil xs)
    -- Uses foldl (tail-recursive) + reverse (tail-recursive) instead of foldr (stack-consuming)
    if innerValArgs.size != 2 then none
    else
      match ctx.foldlConst, ctx.reverseConst, ctx.listCtors with
      | some foldlConst, some reverseConst, some lci =>
        let p := innerValArgs[0]!
        let xs := innerValArgs[1]!
        let inputElemTy := innerTyArgs[0]?.getD dummyTy   -- a
        let outputElemTy := outerTyArgs[1]?.getD dummyTy   -- b
        let resultListTy := Expr.dataTy lci.listTyId #[outputElemTy]  -- [b]
        let f' := f.shiftUp 2
        let p' := p.shiftUp 2
        -- foldl step: λ acc x → if p x then Cons (f x) acc else acc
        let stepFn := Expr.lam .explicit "acc" resultListTy
          (.lam .explicit "x" inputElemTy
            (.if_ (.app p' (.bvar 0))
              (mkCons lci outputElemTy (.app f' (.bvar 0)) (.bvar 1))
              (.bvar 1)))
        let nil := mkNil lci outputElemTy
        -- reverse (foldl {a} {[b]} stepFn Nil xs)
        let foldlCall := Expr.rebuildAppSpine foldlConst (#[inputElemTy, resultListTy, stepFn, nil, xs])
        some (Expr.rebuildAppSpine reverseConst (#[outputElemTy, foldlCall]))
      | _, _, _ => none
  | _ => none

/-- Fuse `filter {a} p (filter {a} q xs)` → `filter {a} (λ x → if q x then p x else false) xs`
    Fuse `filter {a} p (map {c} {a} f xs)` → `foldr {c} {[a]} (λ x acc → if p (f x) then Cons (f x) acc else acc) Nil xs` -/
private partial def fuseFilterWithProducer
    (ctx : FusionCtx) (outerHead : Expr) (outerTyArgs : Array Expr)
    (p listArg : Expr) : Option Expr :=
  let (innerHead, innerArgs) := listArg.collectAppSpine
  let (innerTyArgs, innerValArgs) := splitTypeValueArgs innerArgs
  match constFusionRole ctx innerHead with
  | some .filter =>
    if innerValArgs.size != 2 then none
    else
      match ctx.boolCtors with
      | none => none
      | some bci =>
        let q := innerValArgs[0]!
        let xs := innerValArgs[1]!
        let p' := p.shiftUp 1
        let q' := q.shiftUp 1
        -- x has element type a (same for both filters)
        let elemTy := outerTyArgs[0]?.getD dummyTy
        let newP := Expr.lam .explicit "x" elemTy
          (.if_ (.app q' (.bvar 0))
                (.app p' (.bvar 0))
                (mkBoolLit bci false))
        some (Expr.rebuildAppSpine outerHead (outerTyArgs ++ #[newP, xs]))
  | some .map =>
    -- filter p (map f xs): eliminate intermediate mapped list
    -- → reverse (foldl (λ acc x → let y = f x in if p y then Cons y acc else acc) Nil xs)
    -- Uses foldl (tail-recursive) + reverse (tail-recursive) instead of foldr.
    -- f(x) computed once via let binding to avoid duplicate work.
    if innerValArgs.size != 2 then none
    else
      match ctx.foldlConst, ctx.reverseConst, ctx.listCtors with
      | some foldlConst, some reverseConst, some lci =>
        let f := innerValArgs[0]!
        let xs := innerValArgs[1]!
        let inputElemTy := innerTyArgs[0]?.getD dummyTy   -- c
        let outputElemTy := outerTyArgs[0]?.getD dummyTy   -- a
        let resultListTy := Expr.dataTy lci.listTyId #[outputElemTy]  -- [a]
        let f' := f.shiftUp 2
        let p' := p.shiftUp 2
        -- foldl step: λ acc x → let y = f x in if p y then Cons y acc else acc
        -- Under 2 binders (acc=bvar1, x=bvar0), then let introduces bvar0=y:
        --   y=bvar(0), x=bvar(1), acc=bvar(2)
        let stepFn := Expr.lam .explicit "acc" resultListTy
          (.lam .explicit "x" inputElemTy
            (.let_ "y" outputElemTy (.app f' (.bvar 0))
              (.if_ (.app (p'.shiftUp 1) (.bvar 0))
                (mkCons lci outputElemTy (.bvar 0) (.bvar 2))
                (.bvar 2))))
        let nil := mkNil lci outputElemTy
        -- reverse {a} (foldl {c} {[a]} stepFn Nil xs)
        let foldlCall := Expr.rebuildAppSpine foldlConst (#[inputElemTy, resultListTy, stepFn, nil, xs])
        some (Expr.rebuildAppSpine reverseConst (#[outputElemTy, foldlCall]))
      | _, _, _ => none
  | _ => none

/-- Fuse `any/all {a} pred (map {c} {a} f xs)` → `any/all {c} (λ x → pred (f x)) xs`
    Also fuse `any/all {a} pred (filter {a} p xs)` → `any/all {a} (λ x → p x && pred x) xs`
    (for all: `λ x → ¬(p x) ∨ pred x` i.e. `if p x then pred x else true`) -/
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
      -- x has map's input type c
      let elemTy := innerTyArgs[0]?.getD dummyTy
      let newPred := Expr.lam .explicit "x" elemTy
        (.app pred' (.app f' (.bvar 0)))
      let newTyArgs := if innerTyArgs.size >= 1 then #[innerTyArgs[0]!] else outerTyArgs
      some (Expr.rebuildAppSpine outerHead (newTyArgs ++ #[newPred, xs]))
  | some .filter =>
    if innerValArgs.size != 2 then none
    else
      match ctx.boolCtors with
      | none => none
      | some bci =>
        let p := innerValArgs[0]!
        let xs := innerValArgs[1]!
        let pred' := pred.shiftUp 1
        let p' := p.shiftUp 1
        -- x has element type a (filter preserves it)
        let elemTy := outerTyArgs[0]?.getD dummyTy
        -- Determine the role to pick the right combinator
        let role := constFusionRole ctx outerHead
        let newPred := match role with
          | some .any =>
            -- any pred (filter p xs) → any (λ x → if p x then pred x else false) xs
            Expr.lam .explicit "x" elemTy
              (.if_ (.app p' (.bvar 0))
                    (.app pred' (.bvar 0))
                    (mkBoolLit bci false))
          | _ =>
            -- all pred (filter p xs) → all (λ x → if p x then pred x else true) xs
            Expr.lam .explicit "x" elemTy
              (.if_ (.app p' (.bvar 0))
                    (.app pred' (.bvar 0))
                    (mkBoolLit bci true))
        -- filter preserves element type, so keep outerTyArgs
        some (Expr.rebuildAppSpine outerHead (outerTyArgs ++ #[newPred, xs]))
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
