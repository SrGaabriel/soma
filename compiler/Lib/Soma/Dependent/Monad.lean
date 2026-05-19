import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Core.Expr
import Soma.Core.Intrinsic
import Soma.Dependent.Origin
import Soma.Core.Path
import Soma.Dependent.Error
import Soma.Dependent.Suggest
import Soma.Core.Module
import Soma.Syntax.Source
import Std.Data.HashMap
import Std.Data.HashMap.Raw
import Kenosis

namespace Soma.Dependent

open Soma (Unique)
open Soma.Core
open Soma.Syntax (Span)
open Kenosis

/-- An entry in the typing context -/
structure CtxEntry where
  /-- Variable name -/
  name : String
  /-- Unique local identifier for usage tracking -/
  bindingId : Unique
  /-- Free variable id for Core.Expr output -/
  fvarId : Soma.Unique
  /-- Variable's type (as a Value) -/
  type : Value
  /-- Quantity annotation -/
  qty : Quantity
  /-- De Bruijn level -/
  level : DeBruijnLvl
  /-- How this variable is bound -/
  binder : BinderInfo
  /-- Span where variable was introduced -/
  span : Span
  deriving Inhabited

/-- A work item handled by the unified solver -/
inductive Constraint where
  /-- Unify two values -/
  | unify (v1 v2 : Value) (span : Span)
  /-- Check that v1 is a subtype of v2 -/
  | subtype (v1 v2 : Value) (span : Span)
  /-- Solve a level constraint -/
  | levelEq (l1 l2 : Level)
  /-- Solve a level ordering -/
  | levelLe (l1 l2 : Level)
  | resolveInstance (metaId : MetaId) (classId : Unique) (args : Array Value) (span : Span)
  | deferredInstance (metaId : MetaId) (domTy : Value) (span : Span)
  deriving Inhabited

namespace Constraint

/-- Get the span of a constraint -/
def span : Constraint → Span
  | .unify _ _ s => s
  | .subtype _ _ s => s
  | .levelEq _ _ => Span.uninhabited
  | .levelLe _ _ => Span.uninhabited
  | .resolveInstance _ _ _ s => s
  | .deferredInstance _ _ s => s

/-- Get a human-readable description of the constraint -/
def describe : Constraint → String
  | .unify v1 v2 _ => s!"unify `{v1}` with `{v2}`"
  | .subtype v1 v2 _ => s!"`{v1}` <: `{v2}`"
  | .levelEq l1 l2 => s!"level `{l1}` = `{l2}`"
  | .levelLe l1 l2 => s!"level `{l1}` ≤ `{l2}`"
  | .resolveInstance _ classId _ _ => s!"resolve instance for class `{classId.original}`"
  | .deferredInstance _ domTy _ => s!"deferred instance constraint on `{domTy}`"

/-- Every metavariable whose progress could affect this constraint -/
def referencedMetas : Constraint → Array MetaId
  | .unify v1 v2 _ =>
    (Value.collectMetas v1 ++ Value.collectMetas v2).toList.eraseDups.toArray
  | .subtype v1 v2 _ =>
    (Value.collectMetas v1 ++ Value.collectMetas v2).toList.eraseDups.toArray
  | .levelEq _ _ => #[]
  | .levelLe _ _ => #[]
  | .resolveInstance metaId _ args _ =>
    (#[metaId] ++ args.foldl (fun acc v => acc ++ Value.collectMetas v) #[])
      |>.toList.eraseDups.toArray
  | .deferredInstance metaId domTy _ =>
    (#[metaId] ++ Value.collectMetas domTy).toList.eraseDups.toArray

/-- Every level variable whose progress could affect this constraint. -/
def referencedLevelVars : Constraint → Array LevelVarId
  | .unify _ _ _ => #[]   -- value-level metas, not level vars
  | .subtype _ _ _ => #[]
  | .levelEq l1 l2 => (l1.freeVars ++ l2.freeVars).eraseDups.toArray
  | .levelLe l1 l2 => (l1.freeVars ++ l2.freeVars).eraseDups.toArray
  | .resolveInstance _ _ _ _ => #[]
  | .deferredInstance _ _ _ => #[]

end Constraint

/-- A tracked constraint with its ID, dependencies, and provenance -/
structure TrackedConstraint where
  /-- The underlying constraint -/
  constraint : Constraint
  /-- Constraint ID for dependency tracking -/
  constraintId : ConstraintId
  /-- Metas referenced by this constraint (cached for efficiency) -/
  metas : Array MetaId
  /-- Level variables referenced by this constraint (cached for efficiency) -/
  levelVars : Array LevelVarId := #[]
  /-- Where this constraint originated from -/
  origin : ConstraintOrigin
  /-- Parent constraints that led to this one (for error chain) -/
  parentConstraints : Array ConstraintId
  deriving Inhabited

namespace TrackedConstraint

/-- Convert to ConstraintInfo for error reporting -/
def toInfo (tc : TrackedConstraint) : ConstraintInfo :=
  { origin := tc.origin
  , description := tc.constraint.describe
  , span := tc.constraint.span }

end TrackedConstraint

/-- Origin metadata for global declarations -/
inductive DeclarationOrigin where
  | user
  | function
  | theorem_
  | typeDecl
  | class_
  | constructor
  | projection
  | traitMethod
  | instanceMethod
  | intrinsic
  | extern
  | generated
  deriving Inhabited, BEq, Serialize, Deserialize

/-- Information about a global definition -/
structure GlobalInfo where
  /-- The canonical Name for this definition -/
  name : Soma.Core.QualifiedName
  /-- The type of the definition -/
  type : Value
  /-- The value (for unfolding), if available -/
  value : Option Value := none
  /-- Intrinsic metadata for codegen dispatch (when this global is intrinsic/extern) -/
  intrinsic : Option Soma.Core.Intrinsic := none
  /-- Whether this is a constructor -/
  isConstructor : Bool := false
  /-- Constructor tag (if isConstructor) -/
  ctorTag : Nat := 0
  /-- Declaration classification metadata. -/
  origin : DeclarationOrigin := .user
  deriving Serialize, Deserialize

instance : Inhabited GlobalInfo where
  default := {
    name := ⟨{ id := 0, module := "", original := "" }⟩
    type := .vType .zero
  }

namespace GlobalInfo

end GlobalInfo

/-- Kind of inductive-like type declaration tracked in metadata. -/
inductive InductiveKind where
  | algebraic
  | record
  deriving Inhabited, BEq, Serialize, Deserialize

/-- Metadata for a single constructor belonging to an inductive type -/
structure ConstructorMeta where
  /-- Fully qualified constructor name -/
  name : Soma.Core.QualifiedName
  /-- Unqualified constructor/member name in its parent namespace -/
  simpleName : String
  /-- Constructor tag used by pattern matching/codegen -/
  tag : Nat
  /-- Runtime arity (explicit fields) -/
  arity : Nat
  /-- Elaborated constructor type -/
  type : Value
  deriving Inhabited, Serialize, Deserialize

/-- Metadata for an inductive-like declaration and its constructors. -/
structure InductiveMeta where
  /-- Source declaration kind -/
  kind : InductiveKind
  /-- Declared type parameter names, in order -/
  typeVarNames : Array String := #[]
  /-- Constructor metadata in declaration order -/
  ctors : Array ConstructorMeta := #[]
  /-- Ordered field names for record declarations -/
  fieldNames : Array String := #[]
  /-- QTT quantities of the fields, parallel to `fieldNames` -/
  fieldQuantities : Array Soma.Core.Quantity := #[]
  /-- Universe the declaration head lives in -/
  headSort : Soma.Core.Level := .lit 0
  /-- For `Prop`-kinded inductives only: is this a small proposition? -/
  isSmall : Bool := false
  deriving Inhabited, Serialize, Deserialize

namespace InductiveMeta

/-- Add or replace constructor metadata by simple name, preserving order where possible -/
def upsertCtor (m : InductiveMeta) (ctor : ConstructorMeta) : InductiveMeta :=
  let idx? := m.ctors.findIdx? (fun c => c.simpleName == ctor.simpleName)
  match idx? with
  | some idx => { m with ctors := m.ctors.set! idx ctor }
  | none => { m with ctors := m.ctors.push ctor }

end InductiveMeta

/-- Typed roles for language-level wired declarations -/
inductive WiredRole where
  | pair
  | typePair
  | sigma
  | typeSigma
  | cons
  | nil
  | typeInt
  | typeBool
  | typeString
  | typeFloat
  | typeDouble
  | typeUnit
  | typeInt8
  | typeInt16
  | typeInt64
  | typeWord
  | typeWord8
  | typeWord16
  | typeWord64
  | typeNat
  | typeList
  | typeArray
  | typeRef
  | typeWorld
  | typePtr
  | pureIO
  | bindIO
  | sortType
  | sortType0
  | sortType1
  | sortRow
  | sortLabel
  | listMap
  | listFilter
  | listFoldl
  | listFoldr
  | listSum
  | listProduct
  | listLength
  | listAny
  | listAll
  | listReverse
  | typeEq
  | refl
  deriving Inhabited, BEq, DecidableEq, Hashable, Repr, Serialize, Deserialize

namespace WiredRole

def canonical : WiredRole → String
  | .pair => "pair"
  | .typePair => "type.pair"
  | .sigma => "sigma"
  | .typeSigma => "type.sigma"
  | .cons => "cons"
  | .nil => "nil"
  | .typeInt => "type.int"
  | .typeBool => "type.bool"
  | .typeString => "type.string"
  | .typeFloat => "type.float"
  | .typeDouble => "type.double"
  | .typeUnit => "type.unit"
  | .typeInt8 => "type.int8"
  | .typeInt16 => "type.int16"
  | .typeInt64 => "type.int64"
  | .typeWord => "type.word"
  | .typeWord8 => "type.word8"
  | .typeWord16 => "type.word16"
  | .typeWord64 => "type.word64"
  | .typeNat => "type.nat"
  | .typeList => "type.list"
  | .typeArray => "type.array"
  | .typeRef => "type.ref"
  | .typeWorld => "type.world"
  | .typePtr => "type.ptr"
  | .pureIO => "io.pure"
  | .bindIO => "io.bind"
  | .sortType => "sort.type"
  | .sortType0 => "sort.type0"
  | .sortType1 => "sort.type1"
  | .sortRow => "sort.row"
  | .sortLabel => "sort.label"
  | .listMap => "list.map"
  | .listFilter => "list.filter"
  | .listFoldl => "list.foldl"
  | .listFoldr => "list.foldr"
  | .listSum => "list.sum"
  | .listProduct => "list.product"
  | .listLength => "list.length"
  | .listAny => "list.any"
  | .listAll => "list.all"
  | .listReverse => "list.reverse"
  | .typeEq => "type.eq"
  | .refl => "refl"

instance : ToString WiredRole := ⟨canonical⟩

def fromString? : String → Option WiredRole
  | "pair" => some .pair
  | "type.pair" => some .typePair
  | "sigma" => some .sigma
  | "type.sigma" => some .typeSigma
  | "cons" => some .cons
  | "nil" => some .nil
  | "type.int" | "int" => some .typeInt
  | "type.int8" | "int8" => some .typeInt8
  | "type.int16" | "int16" => some .typeInt16
  | "type.int64" | "int64" => some .typeInt64
  | "type.bool" | "bool" => some .typeBool
  | "type.string" | "string" => some .typeString
  | "type.float" | "float" => some .typeFloat
  | "type.double" | "double" => some .typeDouble
  | "type.unit" | "unit" => some .typeUnit
  | "type.word" | "word" => some .typeWord
  | "type.word8" | "word8" => some .typeWord8
  | "type.word16" | "word16" => some .typeWord16
  | "type.word64" | "word64" => some .typeWord64
  | "type.nat" | "nat" => some .typeNat
  | "type.list" | "list" => some .typeList
  | "type.array" | "array" => some .typeArray
  | "type.ref" | "ref" => some .typeRef
  | "type.world" | "world" => some .typeWorld
  | "type.ptr" | "ptr" => some .typePtr
  | "io.pure" => some .pureIO
  | "io.bind" => some .bindIO
  | "sort.type" | "type" => some .sortType
  | "sort.type0" | "type0" => some .sortType0
  | "sort.type1" | "type1" => some .sortType1
  | "sort.row" | "row" => some .sortRow
  | "sort.label" | "label" => some .sortLabel
  | "list.map" => some .listMap
  | "list.filter" => some .listFilter
  | "list.foldl" => some .listFoldl
  | "list.foldr" => some .listFoldr
  | "list.sum" => some .listSum
  | "list.product" => some .listProduct
  | "list.length" => some .listLength
  | "list.any" => some .listAny
  | "list.all" => some .listAll
  | "list.reverse" => some .listReverse
  | "type.eq" => some .typeEq
  | "refl" => some .refl
  | _ => none

/-- Map wired type roles to canonical primitive representations when applicable -/
def primType? : WiredRole → Option Soma.Core.PrimType
  | .typeInt => some .int
  | .typeBool => some .bool
  | .typeFloat => some .float
  | .typeDouble => some .double
  | .typeUnit => some .unit
  | .typeInt8 => some .int8
  | .typeInt16 => some .int16
  | .typeInt64 => some .int64
  | .typeWord => some .word
  | .typeWord8 => some .word8
  | .typeWord16 => some .word16
  | .typeWord64 => some .word64
  | .typeWorld => some .world
  | .typeArray => some .array
  | .typeList => some .list
  | .typeRef => some .ref
  | .typePtr => some .ptr
  | _ => none

/-- Roles whose declaration's inductive uid backs an alternate `vPrimTy` representation is not normalized (TODO: remove) -/
def primTyAlias? : WiredRole → Option Soma.Core.PrimType
  | .typeString => some .string
  | _ => none

/-- The full `vPrimTy ↔ wired role` correspondence -/
def primTyOfRole? (r : WiredRole) : Option Soma.Core.PrimType :=
  match primType? r with
  | some p => some p
  | none => primTyAlias? r

/-- Every `WiredRole` value, in declaration order -/
def all : Array WiredRole := #[
  .pair, .typePair, .sigma, .typeSigma, .cons, .nil,
  .typeInt, .typeBool, .typeString, .typeFloat, .typeDouble,
  .typeUnit, .typeInt8, .typeInt16, .typeInt64,
  .typeWord, .typeWord8, .typeWord16, .typeWord64, .typeNat,
  .typeList, .typeArray, .typeRef, .typeWorld, .typePtr,
  .pureIO, .bindIO,
  .sortType, .sortType0, .sortType1, .sortRow, .sortLabel,
  .listMap, .listFilter, .listFoldl, .listFoldr,
  .listSum, .listProduct, .listLength, .listAny, .listAll, .listReverse,
  .typeEq, .refl
]

end WiredRole

/-- Well-known language entities resolved via @[wired_in "role"] attributes -/
structure WiredIn where
  /-- Role → all declarations bound to this role -/
  roles : Std.HashMap WiredRole (Array GlobalInfo) := {}
  deriving Inhabited

namespace WiredIn

/-- Look up all declarations registered to a role -/
def getAll (w : WiredIn) (role : WiredRole) : Array GlobalInfo :=
  w.roles.getD role #[]

/-- Look up a role only when it has exactly one declaration -/
def getUnique? (w : WiredIn) (role : WiredRole) : Option GlobalInfo :=
  match w.getAll role with
  | #[info] => some info
  | _ => none

/-- Register a constructor under a role -/
def register (w : WiredIn) (role : WiredRole) (info : GlobalInfo) : WiredIn :=
  let existing := w.roles.getD role #[]
  if existing.any (fun e => e.name == info.name) then
    w
  else
    { w with roles := w.roles.insert role (existing.push info) }

end WiredIn

/-- Recursive namespace tree for name resolution -/
structure Namespace where
  /-- Declarations directly in this namespace: name → identity -/
  decls : Std.HashMap.Raw String Soma.Core.QualifiedName := {}
  /-- Child namespaces -/
  children : Std.HashMap.Raw String Namespace := {}

instance : Inhabited Namespace where
  default := {}

namespace Namespace

def empty : Namespace := {}

/-- Resolve a name to its QualifiedName -/
def getDecl? (ns : Namespace) (name : String) : Option Soma.Core.QualifiedName :=
  ns.decls.get? name

/-- Look up a child namespace -/
def getChild? (ns : Namespace) (name : String) : Option Namespace :=
  ns.children.get? name

/-- Register a name → identity mapping -/
def insertDecl (ns : Namespace) (name : String) (qn : Soma.Core.QualifiedName) : Namespace :=
  { ns with decls := ns.decls.insert name qn }

/-- Resolve a qualified path to its QualifiedName -/
partial def resolve (ns : Namespace) (parts : List String) : Option Soma.Core.QualifiedName :=
  match parts with
  | [] => none
  | [name] => ns.getDecl? name
  | seg :: rest =>
    match ns.getChild? seg with
    | some child => child.resolve rest
    | none => none

/-- Insert a name → identity mapping at a qualified path, creating intermediate namespaces -/
partial def insertAt (ns : Namespace) (parts : List String) (qn : Soma.Core.QualifiedName) : Namespace :=
  match parts with
  | [] => ns
  | [name] => ns.insertDecl name qn
  | seg :: rest =>
    let child := (ns.children.get? seg).getD .empty
    let child' := child.insertAt rest qn
    { ns with children := ns.children.insert seg child' }

/-- Walk a path and return the namespace node at that location -/
partial def getAt? (ns : Namespace) (parts : List String) : Option Namespace :=
  match parts with
  | [] => some ns
  | seg :: rest =>
    match ns.getChild? seg with
    | some child => child.getAt? rest
    | none => none

/-- Recursively merge another namespace into this one -/
partial def merge (ns1 ns2 : Namespace) : Namespace :=
  let mergedDecls := Std.HashMap.Raw.fold (fun acc name qn =>
    acc.insert name qn) ns1.decls ns2.decls
  let mergedChildren := Std.HashMap.Raw.fold (fun acc childName child2 =>
    match acc.get? childName with
    | some child1 => acc.insert childName (Namespace.merge child1 child2)
    | none => acc.insert childName child2) ns1.children ns2.children
  { decls := mergedDecls, children := mergedChildren }

/-- Merge a child namespace at a given path, creating intermediates as needed -/
partial def mergeAt (ns : Namespace) (parts : List String) (other : Namespace) : Namespace :=
  match parts with
  | [] => Namespace.merge ns other
  | seg :: rest =>
    let child := (ns.children.get? seg).getD .empty
    let child' := child.mergeAt rest other
    { ns with children := ns.children.insert seg child' }

/-- Collect all declarations with their namespace paths -/
partial def collectPaths (ns : Namespace) (_prefix : Array String)
    : Array (Array String × String × Soma.Core.QualifiedName) :=
  let fromDecls := ns.decls.fold (init := #[]) fun acc name qn =>
    acc.push (_prefix, name, qn)
  ns.children.fold (init := fromDecls) fun acc childName child =>
    acc ++ child.collectPaths (_prefix.push childName)

end Namespace

structure Globals where
  /-- Hierarchical namespace tree for resolution (name → identity) -/
  root : Namespace := .empty
  /-- Flat declaration map (identity → data) -/
  defs : Std.HashMap Soma.Core.QualifiedName GlobalInfo := {}
  /-- Explicit imports: unqualified name → (tree path, identity) -/
  imports : Std.HashMap.Raw String (List String × Soma.Core.QualifiedName) := {}
  /-- Intrinsic dispatch table keyed by qualified global name -/
  intrinsics : Std.HashMap Soma.Core.QualifiedName Soma.Core.Intrinsic := {}
  /-- Ordered field names for record types -/
  recordFields : Std.HashMap Soma.Core.QualifiedName (Array String) := {}
  /-- First-class inductive metadata keyed by type QualifiedName -/
  inductives : Std.HashMap Soma.Core.QualifiedName InductiveMeta := {}
  /-- Reverse index: constructor qualified name -> inductive QualifiedName -/
  ctorToInductive : Std.HashMap Soma.Core.QualifiedName Soma.Core.QualifiedName := {}
  /-- Well-known constructors for pattern desugaring -/
  wiredIn : WiredIn := {}
  deriving Inhabited

namespace Globals

def empty : Globals := {}

/-- Register a declaration at a namespace path -/
def register (g : Globals) (ns : Array String) (displayName : String) (info : GlobalInfo) : Globals :=
  let g' := { g with
    root := g.root.insertAt (ns.toList ++ [displayName]) info.name
    defs := g.defs.insert info.name info }
  match info.intrinsic with
  | some i =>
    { g' with intrinsics := g'.intrinsics.insert info.name i }
  | none => g'

/-- Register a declaration by QualifiedName only without inserting it into the namespace tree -/
def registerAnonymous (g : Globals) (info : GlobalInfo) : Globals :=
  let g' := { g with defs := g.defs.insert info.name info }
  match info.intrinsic with
  | some i => { g' with intrinsics := g'.intrinsics.insert info.name i }
  | none => g'

/-- Look up a declaration by its QualifiedName -/
def getDef (g : Globals) (qn : Soma.Core.QualifiedName) : Option GlobalInfo :=
  g.defs.get? qn

/-- Register an explicit import: makes `name` resolvable unqualified to `qn` -/
def registerImport (g : Globals) (name : String) (treePath : List String) (qn : Soma.Core.QualifiedName) : Globals :=
  { g with imports := g.imports.insert name (treePath, qn) }

/-- Inject prelude symbols into the imports map. Each symbol name is resolved
    through the namespace tree under the prelude module path. Symbols that
    don't resolve (e.g., prelude not loaded) are silently skipped. -/
def injectPrelude (g : Globals) (preludePath : List String) (symbols : Array String) : Globals :=
  symbols.foldl (init := g) fun g' name =>
    if g'.imports.contains name then g'
    else
      match g'.root.resolve (preludePath ++ [name]) with
      | some qn => g'.registerImport name preludePath qn
      | none => g'

/-- Register or refresh top-level inductive metadata for a type name -/
def registerInductive (g : Globals) (qn : Soma.Core.QualifiedName)
    (kind : InductiveKind) (typeVarNames : Array String := #[])
    (fieldNames : Array String := #[])
    (fieldQuantities : Array Soma.Core.Quantity := #[])
    (headSort : Soma.Core.Level := .lit 0) : Globals :=
  let metaInfo : InductiveMeta := match g.inductives.get? qn with
    | some existing =>
      { existing with
        kind := kind
        typeVarNames := typeVarNames
        fieldNames := fieldNames
        fieldQuantities := fieldQuantities
        headSort := headSort }
    | none =>
      { kind := kind
        typeVarNames := typeVarNames
        fieldNames := fieldNames
        fieldQuantities := fieldQuantities
        headSort := headSort }
  { g with
    recordFields := if fieldNames.isEmpty then g.recordFields else g.recordFields.insert qn fieldNames
    inductives := g.inductives.insert qn metaInfo }

/-- Register constructor metadata under an inductive type -/
def registerConstructorMeta (g : Globals) (typeQN : Soma.Core.QualifiedName) (ctor : ConstructorMeta) : Globals :=
  let g := match g.inductives.get? typeQN with
    | some metaInfo =>
      let updated := metaInfo.upsertCtor ctor
      { g with inductives := g.inductives.insert typeQN updated }
    | none => g
  { g with ctorToInductive := g.ctorToInductive.insert ctor.name typeQN }

/-- Look up inductive metadata by QualifiedName -/
def lookupInductive (g : Globals) (qn : Soma.Core.QualifiedName) : Option InductiveMeta :=
  g.inductives.get? qn

/-- Look up inductive metadata owning a constructor -/
def lookupInductiveByCtor (g : Globals) (ctorName : Soma.Core.QualifiedName)
    : Option InductiveMeta :=
  match g.ctorToInductive.get? ctorName with
  | some typeQN => g.inductives.get? typeQN
  | none => none

/-- Resolve a name through the namespace tree, returning its QualifiedName -/
def resolve (g : Globals) (currentNs : Array String) (path : Array String) (name : String) : Option Soma.Core.QualifiedName :=
  let suffix := path.toList ++ [name]
  match g.root.resolve (currentNs.toList ++ suffix) with
  | some qn => some qn
  | none =>
    if path.isEmpty then
      match g.imports.get? name with
      | some (_, qn) => some qn
      | none => none
    else
      match g.root.resolve suffix with
      | some qn => some qn
      | none =>
        match path.toList with
        | head :: rest =>
          match g.imports.get? head with
          | some (treePath, _) =>
            g.root.resolve (treePath ++ [head] ++ rest ++ [name])
          | none => none
        | [] => none

/-- Find a constructor by simple name within an inductive type -/
def lookupCtor (g : Globals) (typeQN : Soma.Core.QualifiedName) (ctorSimpleName : String) : Option ConstructorMeta :=
  match g.lookupInductive typeQN with
  | some indInfo => indInfo.ctors.find? (·.simpleName == ctorSimpleName)
  | none => none

/-- Look up a record field's positional index -/
def lookupFieldIndex (g : Globals) (typeQN : Soma.Core.QualifiedName) (fieldName : String) : Option Nat :=
  match g.lookupInductive typeQN with
  | some indInfo =>
    match indInfo.fieldNames.toList.findIdx? (· == fieldName) with
    | some idx => some idx
    | none =>
      match g.recordFields.get? typeQN with
      | some fields => fields.toList.findIdx? (· == fieldName)
      | none => none
  | none =>
    match g.recordFields.get? typeQN with
    | some fields => fields.toList.findIdx? (· == fieldName)
    | none => none

/-- Collect all declarations -/
def allDecls (g : Globals) : List (Soma.Core.QualifiedName × GlobalInfo) :=
  g.defs.fold (fun acc qn info => (qn, info) :: acc) []

/-- Convert Globals to GlobalEnv (for evaluation context) -/
def toGlobalEnv (g : Globals) : GlobalEnv :=
  let withDefs : GlobalEnv := g.defs.fold (init := GlobalEnv.empty) fun acc qn info =>
    match info.value with
    | some v => acc.insert qn v
    | none => acc
  let withRecords := g.inductives.fold (init := withDefs) fun acc typeQN indMeta =>
    if indMeta.fieldNames.isEmpty then acc
    else
      match indMeta.ctors[0]? with
      | some ctor => acc.insertRecordCtorInfo typeQN.id ctor.type indMeta.fieldNames
      | none => acc
  let withPrims := WiredRole.all.foldl (init := withRecords) fun acc role =>
    match WiredRole.primTyOfRole? role, g.wiredIn.getUnique? role with
    | some p, some info => acc.insertPrimTyInductive p info.name.id
    | _, _ => acc
  let eqId? : Option Unique :=
    (g.wiredIn.getUnique? .typeEq).map (·.name.id)
  let reflInfo? : Option (Soma.Core.QualifiedName × Nat) :=
    (g.wiredIn.getUnique? .refl).map fun info => (info.name, info.ctorTag)
  { withPrims with eqInductiveId := eqId?, reflConstructor := reflInfo? }

end Globals

/-- Information about a type class (represented as a record type) -/
structure ClassInfo where
  /-- The class unique identifier -/
  classId : Unique
  /-- Number of type parameters -/
  numParams : Nat
  /-- Quantity annotations for each type parameter (for QTT) -/
  paramQuantities : Array Quantity := #[]
  /-- The record type representing this class (as a Value) -/
  recordType : Value
  /-- Superclass constraints (class uniques with their parameter indices) -/
  superclasses : Array (Unique × Array Nat)
  /-- Source span for error reporting -/
  span : Span
  deriving Serialize, Deserialize

instance : Inhabited ClassInfo where
  default := {
    classId := { id := 0, module := "", original := "" }
    numParams := 0
    paramQuantities := #[]
    recordType := Value.vType .zero
    superclasses := #[]
    span := Span.uninhabited
  }

namespace ClassInfo

end ClassInfo

/-- Information about a registered instance -/
structure InstanceInfo where
  /-- Unique identifier for this instance -/
  instanceId : Unique
  /-- The class this is an instance for -/
  classId : Unique
  /-- The type arguments to the class (as Values) -/
  args : Array Value
  /-- Quantity annotations for each type argument (for QTT) -/
  argQuantities : Array Quantity := #[]
  /-- Constraints required by this instance (class unique × args) -/
  constraints : Array (Unique × Array Value)
  /-- The instance value (a record value) -/
  value : Value
  /-- Number of leading lambda parameters that are constraint dictionary arguments -/
  constraintDictCount : Nat := 0
  /-- Source span for error reporting -/
  span : Span
  deriving Serialize, Deserialize

instance : Inhabited InstanceInfo where
  default := {
    instanceId := { id := 0, module := "", original := "" }
    classId := { id := 0, module := "", original := "" }
    args := #[]
    argQuantities := #[]
    constraints := #[]
    value := Value.vType .zero
    span := Span.uninhabited
  }

namespace InstanceInfo

end InstanceInfo

/-- Structural discrimination key for a `Value` -/
inductive DiscrKey where
  | dataType (id : Soma.Unique)
  | type_ (lvl : Nat)
  | rowSort
  | labelSort
  | rowEmpty
  | pi | lam
  | record | variant | rowExtend
  | labelLit (s : String)
  | intLit (n : Int)
  | floatLit
  | strLit
  | boolLit
  | constHead (qn : Soma.Core.QualifiedName)
  | boundVar (lvl : Nat)
  | equality | refl_ | transport
  /-- Meta variables and anything we can't meaningfully discriminate -/
  | wildcard
  deriving BEq, Hashable, Inhabited, Repr

namespace DiscrKey

/-- Compute the discrimination key of a value -/
partial def ofValue : Value → DiscrKey
  | .vDataType id _ => .dataType id
  | .vType (.lit n) => .type_ n
  | .vType _ => .type_ 0
  | .vRowSort => .rowSort
  | .vLabelSort => .labelSort
  | .vRowEmpty => .rowEmpty
  | .vLabelLit s => .labelLit s
  | .vIntLit n => .intLit n
  | .vFloatLit _ => .floatLit
  | .vStringLit _ => .strLit
  | .vPi _ _ _ _ _ => .pi
  | .vLam _ _ _ => .lam
  | .vRecord _ => .record
  | .vVariant _ => .variant
  | .vRowExtend _ _ _ => .rowExtend
  | .vNeutral _ neu =>
    match neu.head with
    | .hConst qn _ => .constHead qn
    | .hVar bv => .boundVar bv.level.lvl
    | _ => .wildcard
  | _ => .wildcard

/-- Is this key the wildcard -/
def isWildcard : DiscrKey → Bool
  | .wildcard => true
  | _ => false

end DiscrKey

/-- Per-class discrimination tree -/
inductive DiscrTree where
  | leaf (instances : Array InstanceInfo)
  | branch (children : Array (DiscrKey × DiscrTree)) (wildcard : Option DiscrTree)
  deriving Inhabited

namespace DiscrTree

/-- Empty leaf -/
def empty : DiscrTree := .leaf #[]

/-- Look up a child by key in an association-array children list -/
private def findChild? (children : Array (DiscrKey × DiscrTree)) (k : DiscrKey)
    : Option DiscrTree := Id.run do
  for (k', sub) in children do
    if k' == k then return some sub
  return none

/-- Replace (or insert) a child by key in an association-array children list -/
private def setChild (children : Array (DiscrKey × DiscrTree))
    (k : DiscrKey) (sub : DiscrTree) : Array (DiscrKey × DiscrTree) := Id.run do
  let mut replaced := false
  let mut out : Array (DiscrKey × DiscrTree) := Array.mkEmpty children.size
  for (k', s) in children do
    if k' == k then
      out := out.push (k, sub); replaced := true
    else
      out := out.push (k', s)
  if replaced then out else out.push (k, sub)

/-- Insert an instance into the trie along the key path derived from its arguments -/
partial def insertAt (keys : List DiscrKey) (inst : InstanceInfo) : DiscrTree → DiscrTree
  | .leaf insts =>
    match keys with
    | [] => .leaf (insts.push inst)
    | k :: ks =>
      let subtree := (DiscrTree.empty).insertAt ks inst
      if k.isWildcard then
        .branch #[] (some subtree)
      else
        .branch #[(k, subtree)] none
  | .branch children wildcard =>
    match keys with
    | [] =>
      let wc' := (wildcard.getD .empty).insertAt [] inst
      .branch children (some wc')
    | k :: ks =>
      if k.isWildcard then
        let wc' := (wildcard.getD .empty).insertAt ks inst
        .branch children (some wc')
      else
        let sub  := (findChild? children k).getD .empty
        let sub' := sub.insertAt ks inst
        .branch (setChild children k sub') wildcard

/-- Insert an instance given its full arg list -/
def insert (tree : DiscrTree) (inst : InstanceInfo) : DiscrTree :=
  let keys := inst.args.toList.map DiscrKey.ofValue
  tree.insertAt keys inst

/-- Walk the trie collecting every instance reachable under `keys` -/
partial def queryAt : List DiscrKey → DiscrTree → Array InstanceInfo
  | [], .leaf insts => insts
  | [], .branch _ _ => #[]
  | _ :: _, .leaf insts => insts
  | k :: ks, .branch children wildcard =>
    let byKey : Array InstanceInfo :=
      if k.isWildcard then
        children.foldl (init := #[]) fun acc (_, sub) => acc ++ sub.queryAt ks
      else
        match findChild? children k with
        | some sub => sub.queryAt ks
        | none     => #[]
    let byWild : Array InstanceInfo :=
      wildcard.map (·.queryAt ks) |>.getD #[]
    byKey ++ byWild

/-- Query with a full list of arg keys -/
def query (tree : DiscrTree) (keys : List DiscrKey) : Array InstanceInfo :=
  tree.queryAt keys

/-- Every instance in the trie, flattened. Deterministic post-order -/
partial def flatten : DiscrTree → Array InstanceInfo
  | .leaf insts => insts
  | .branch children wildcard =>
    let fromChildren : Array InstanceInfo :=
      children.foldl (init := #[]) fun acc (_, sub) => acc ++ sub.flatten
    let fromWild : Array InstanceInfo :=
      wildcard.map DiscrTree.flatten |>.getD #[]
    fromChildren ++ fromWild

/-- Merge two tries -/
partial def merge : DiscrTree → DiscrTree → DiscrTree
  | .leaf a, .leaf b => .leaf (a ++ b)
  | .leaf a, .branch cs wc =>
    .branch cs (some ((wc.getD .empty).merge (.leaf a)))
  | .branch cs wc, .leaf b =>
    .branch cs (some ((wc.getD .empty).merge (.leaf b)))
  | .branch ac aw, .branch bc bw =>
    let merged : Array (DiscrKey × DiscrTree) :=
      ac.foldl (init := bc) fun acc (k, asub) =>
        match findChild? acc k with
        | none      => acc.push (k, asub)
        | some bsub => setChild acc k (bsub.merge asub)
    let wildcard := match aw, bw with
      | none,   bw => bw
      | aw,     none => aw
      | some a, some b => some (a.merge b)
    .branch merged wildcard

/-- Total instance count -/
partial def size : DiscrTree → Nat
  | .leaf insts => insts.size
  | .branch children wildcard =>
    let childSize := children.foldl (init := 0) fun acc (_, s) => acc + s.size
    let wcSize := wildcard.map size |>.getD 0
    childSize + wcSize

end DiscrTree

/-- Environment tracking all type classes and their instances -/
structure InstanceEnv where
  /-- All registered classes, indexed by unique id -/
  classes : Std.HashMap Unique ClassInfo := {}
  /-- All registered instances, indexed by class unique -/
  instances : Std.HashMap Unique (Array InstanceInfo) := {}
  /-- Per-class discrimination trees, kept in sync with `instances` -/
  indices : Std.HashMap Unique DiscrTree := {}
  /-- Next instance ID counter (for generating synthetic instance uniques) -/
  nextInstanceId : Nat := 0
  /-- Module name for generating instance uniques -/
  moduleName : String := ""
  deriving Inhabited

namespace InstanceEnv

/-- Create an empty instance environment -/
def empty : InstanceEnv := {}

/-- Create an instance environment for a module -/
def forModule (moduleName : String) : InstanceEnv :=
  { moduleName := moduleName }

/-- Register a new type class -/
def addClass (env : InstanceEnv) (info : ClassInfo) : InstanceEnv :=
  { env with classes := env.classes.insert info.classId info }

/-- Register a new instance with explicit unique -/
def addInstanceWithId (env : InstanceEnv) (info : InstanceInfo) : InstanceEnv :=
  let existing := env.instances.getD info.classId #[]
  let existingIdx := env.indices.getD info.classId DiscrTree.empty
  { env with
    instances := env.instances.insert info.classId (existing.push info)
    indices := env.indices.insert info.classId (existingIdx.insert info) }

/-- Replace an existing instance (matched by `instanceId`) with a new `InstanceInfo` -/
def replaceInstanceWithId (env : InstanceEnv) (info : InstanceInfo) : InstanceEnv := Id.run do
  let existing := env.instances.getD info.classId #[]
  let mut found := false
  let mut updated : Array InstanceInfo := Array.mkEmpty existing.size
  for inst in existing do
    if inst.instanceId == info.instanceId then
      updated := updated.push info
      found := true
    else
      updated := updated.push inst
  if !found then
    return env.addInstanceWithId info
  let newTree := updated.foldl (init := DiscrTree.empty) DiscrTree.insert
  return { env with
    instances := env.instances.insert info.classId updated
    indices := env.indices.insert info.classId newTree }

/-- Register a new instance, generating a unique if not provided -/
def addInstance (env : InstanceEnv) (classId : Unique) (args : Array Value)
    (argQuantities : Array Quantity)
    (constraints : Array (Unique × Array Value)) (value : Value)
    (instanceName : Option String := none) (span : Span := Span.uninhabited) : InstanceEnv :=
  let name := instanceName.getD s!"$inst_{classId.original}_{env.nextInstanceId}"
  let instId : Unique := {
    id := env.nextInstanceId
    module := env.moduleName
    original := name
  }
  let info : InstanceInfo := {
    instanceId := instId
    classId := classId
    args := args
    argQuantities := argQuantities
    constraints := constraints
    value := value
    span := span
  }
  let existing := env.instances.getD classId #[]
  let existingIdx := env.indices.getD classId DiscrTree.empty
  { env with
    instances := env.instances.insert classId (existing.push info)
    indices := env.indices.insert classId (existingIdx.insert info)
    nextInstanceId := env.nextInstanceId + 1
  }

/-- Check if a class exists -/
def hasClass (env : InstanceEnv) (classId : Unique) : Bool :=
  env.classes.contains classId

/-- Get total number of instances -/
def instanceCount (env : InstanceEnv) : Nat :=
  env.instances.fold (fun acc _ insts => acc + insts.size) 0

/-- Look up a class by unique -/
def getClass (env : InstanceEnv) (classId : Unique) : Option ClassInfo :=
  env.classes.get? classId

/-- Look up all instances for a class -/
def getInstances (env : InstanceEnv) (classId : Unique) : Array InstanceInfo :=
  env.instances.getD classId #[]

/-- Narrow the candidate instances for a goal via the discrimination tree -/
def getCandidateInstances (env : InstanceEnv) (classId : Unique)
    (args : Array Value) : Array InstanceInfo :=
  match env.indices.get? classId with
  | none => env.getInstances classId
  | some tree =>
    let keys := args.toList.map DiscrKey.ofValue
    tree.query keys

end InstanceEnv

/-- Enrich a GlobalEnv with class record types from an InstanceEnv.
    This enables pure `typeOfWith` to resolve field access on class dictionary types
    (e.g., `vDataType(Monad, [IO])`) without needing the TCM monad. -/
def enrichGlobalEnvWithClasses (env : Soma.Core.GlobalEnv) (instanceEnv : InstanceEnv) : Soma.Core.GlobalEnv :=
  instanceEnv.classes.fold (init := env) fun acc classId classInfo =>
    acc.insertClassRecordType classId classInfo.recordType

/-- Convert Globals to GlobalEnv enriched with class record types -/
def Globals.toGlobalEnvWithClasses (g : Globals) (instanceEnv : InstanceEnv) : Soma.Core.GlobalEnv :=
  enrichGlobalEnvWithClasses g.toGlobalEnv instanceEnv

/-- Elaborated type abbreviation -/
structure AbbrevInfo where
  /-- Unique identifier for this abbreviation -/
  abbrevId : Unique
  /-- Number of type parameters -/
  arity : Nat
  /-- The elaborated expansion, pi-wrapped if parametized -/
  expansion : Value
  /-- Source span for error reporting -/
  span : Span
  deriving Serialize, Deserialize

instance : Inhabited AbbrevInfo where
  default := {
    abbrevId := { id := 0, module := "", original := "" }
    arity := 0
    expansion := Value.vType Level.zero
    span := Span.uninhabited
  }

namespace AbbrevInfo

end AbbrevInfo

abbrev AbbrevEnv := Std.HashMap Soma.Core.QualifiedName AbbrevInfo

namespace AbbrevEnv
def empty : AbbrevEnv := {}
def merge (a b : AbbrevEnv) : AbbrevEnv :=
  b.fold (init := a) fun acc k v => acc.insert k v
end AbbrevEnv

/-- A pending instance constraint to be resolved -/
structure PendingInstance where
  /-- The metavariable that needs an instance -/
  metaId : MetaId
  /-- The class unique -/
  classId : Unique
  /-- The class arguments -/
  args : Array Value
  /-- Where this constraint came from -/
  span : Span

instance : Inhabited PendingInstance where
  default := {
    metaId := ⟨0⟩
    classId := { id := 0, module := "", original := "" }
    args := #[]
    span := Span.uninhabited
  }

/-- Mutable state for type checking -/
structure TCState where
  /-- Metavariable state -/
  metas : MetaState := MetaState.empty
  /-- Level variable solutions -/
  levelSolutions : Std.HashMap Nat Level := {}
  /-- Next level variable ID -/
  nextLevelVar : Nat := 0
  /-- Unified constraint queue — all outstanding solver work -/
  postponed : Array TrackedConstraint := #[]
  /-- Worklist of constraint IDs to retry (populated when metas are solved) -/
  worklist : Array ConstraintId := #[]
  /-- Set by `unify` / `unifyLevel` / `subtypeUnify` when they cannot make
      progress on a stuck case (flex-flex rows, projection metas, stuck `max`
      levels, etc.). The constraint dispatcher reads this and converts it into
      a `.blocked` outcome. Cleared at the start of every dispatch call.
      A non-`none` value at the end of an outer `unify` means "the operation
      made whatever progress it could, but the overall constraint is stuck on
      these dependencies." -/
  stuckSignal : Option (Array MetaId × Array LevelVarId) := none
  /-- Pattern-context unification buffer -/
  patternRefinementsBuffer? : Option (Std.HashMap Nat Value) := none
  /-- Accumulated errors -/
  errors : Array TCError := #[]
  /-- Accumulated warnings -/
  warnings : Array TCWarning := #[]
  /-- Fresh name counter -/
  freshCounter : Nat := 0
  /-- Variable usage counts for QTT tracking (Unique -> exact count) -/
  usages : Std.HashMap Unique Nat := {}
  /-- Unique supply for generating compiler-internal names -/
  uniqueSupply : Soma.UniqueSupply := Soma.UniqueSupply.initial ""
  /-- Dependencies on global definitions (for incremental checking) -/
  globalDeps : Std.HashSet Soma.Core.QualifiedName := {}
  /-- Elaborated types of local bindings, keyed by the start byte offset of the binding's name span -/
  localTypes : Std.HashMap Nat Value := {}
  deriving Inhabited

namespace TCState

def empty : TCState := {}

/-- Create an initial state for a module -/
def forModule (moduleName : String) : TCState :=
  { uniqueSupply := Soma.UniqueSupply.initial moduleName }

/-- Create a fresh metavariable -/
def freshMeta (s : TCState) (ty : Value) (ctx : List CtxEntry)
    (piLevel : Option Nat := none) (origin : Soma.Core.MetaOrigin := .user)
    (displayHint : Option String := none)
    : MetaId × TCState :=
  let ctxList := ctx.map fun e => (e.name, e.type, e.qty)
  let (id, metas') := s.metas.fresh ty ctxList
    (piLevel := piLevel) (origin := origin) (displayHint := displayHint)
  (id, { s with metas := metas' })

/-- Create a fresh level variable -/
def freshLevelVar (s : TCState) (name : String := "") : LevelVarId × TCState :=
  let id : LevelVarId := ⟨s.nextLevelVar, name⟩
  (id, { s with nextLevelVar := s.nextLevelVar + 1 })

/-- Solve a metavariable -/
def solveMeta (s : TCState) (id : MetaId) (v : Value) : TCState :=
  { s with metas := s.metas.solve id v }

/-- Look up a metavariable -/
def lookupMeta (s : TCState) (id : MetaId) : Option MetaInfo :=
  s.metas.lookup id

/-- Add a postponed constraint with full dependency tracking -/
def postponeTracked (s : TCState) (c : Constraint)
    (metas : Array MetaId)
    (levelVars : Array LevelVarId := #[])
    (origin : ConstraintOrigin := .unknown)
    (parents : Array ConstraintId := #[])
    : ConstraintId × TCState :=
  let (cid, metas') := s.metas.registerConstraint metas levelVars
  let tc : TrackedConstraint := {
    constraint := c
    constraintId := cid
    metas := metas
    levelVars := levelVars
    origin := origin
    parentConstraints := parents
  }
  (cid, { s with metas := metas', postponed := s.postponed.push tc })

/-- Add a postponed constraint -/
def postpone (s : TCState) (c : Constraint) : TCState :=
  (s.postponeTracked c c.referencedMetas c.referencedLevelVars).2

/-- Remove a constraint by ID (after it's been solved) -/
def removeConstraint (s : TCState) (cid : ConstraintId) : TCState :=
  let postponed' := s.postponed.filter (·.constraintId != cid)
  let metas' := s.metas.removeConstraint cid
  { s with postponed := postponed', metas := metas' }

/-- Add an error -/
def addError (s : TCState) (e : TCError) : TCState :=
  { s with errors := s.errors.push e }

/-- Generate a fresh unique identifier -/
def freshUnique (s : TCState) (original : String) : Unique × TCState :=
  let (u, supply') := s.uniqueSupply.fresh original
  (u, { s with uniqueSupply := supply' })

/-- Record usage of a variable (increments count by given amount, default 1) -/
def useVar (s : TCState) (bindingId : Unique) (count : Nat := 1) : TCState :=
  let current := s.usages.getD bindingId 0
  { s with usages := s.usages.insert bindingId (current + count) }

/-- Get the usage count of a variable -/
def getUsage (s : TCState) (bindingId : Unique) : Nat :=
  s.usages.getD bindingId 0

/-- Clear usages (for starting a new scope) -/
def clearUsages (s : TCState) : TCState :=
  { s with usages := {} }

/-- Save current usages -/
def saveUsages (s : TCState) : Std.HashMap Unique Nat :=
  s.usages

/-- Restore usages -/
def restoreUsages (s : TCState) (usages : Std.HashMap Unique Nat) : TCState :=
  { s with usages := usages }

/-- Add a pending instance constraint to the unified queue -/
def addPendingInstance (s : TCState) (p : PendingInstance) : TCState :=
  s.postpone (.resolveInstance p.metaId p.classId p.args p.span)

/-- Get all pending instance constraints from the unified queue -/
def getPendingInstances (s : TCState) : Array PendingInstance :=
  s.postponed.filterMap fun tc =>
    match tc.constraint with
    | .resolveInstance metaId classId args span =>
      some { metaId := metaId, classId := classId, args := args, span := span }
    | _ => none

/-- Enqueue a deferred instance meta on the unified queue -/
def addDeferredInstanceMeta (s : TCState) (metaId : MetaId) (domTy : Value) (span : Span) : TCState :=
  s.postpone (.deferredInstance metaId domTy span)

end TCState

/-- Immutable context for type checking -/
structure TCContext where
  /-- Local typing context (most recent binding first) -/
  locals : List CtxEntry := []
  /-- HashMap index for O(1) local lookup by name -/
  localsByName : Std.HashMap String CtxEntry := {}
  /-- NbE environment (values for bound variables) -/
  env : Env := Env.empty
  /-- Global definitions -/
  globals : Globals := Globals.empty
  /-- Current namespace path for registration -/
  currentNamespace : Array String := #[]
  /-- Instance environment (type classes and instances) -/
  instanceEnv : InstanceEnv := InstanceEnv.empty
  /-- Type abbreviations (elaborated, merged from dependencies) -/
  abbrevEnv : AbbrevEnv := {}
  /-- Unqualified-name overrides -/
  methodSelfRefs : Std.HashMap String (Soma.Core.QualifiedName × Value) := {}
  /-- Current span (for error reporting) -/
  currentSpan : Span := Span.uninhabited
  /-- Current constraint origin -/
  currentOrigin : Option ConstraintOrigin := none
  /-- Current structural path the unifier has walked -/
  currentPath : Path := Path.empty
  /-- The two root values for an in-progress unification -/
  currentUnifyRoot : Option (Soma.Core.Value × Soma.Core.Value) := none
  /-- Whether we are already inside an application chain  -/
  inApplicationChain : Bool := false
  /-- Whether we know we are descending into an injective head -/
  inInjectiveDescent : Bool := false
  /-- Implicit arguments inserted most recently -/
  currentImplicits : Option (String × Array (Soma.Core.MetaId × Soma.Core.Value × String)) := none
  /-- Are we in erased context? (under a 0-quantity binder) -/
  inErased : Bool := false
  /-- Current multiplier for quantity tracking (for nested binders) -/
  qtyMultiplier : Quantity := .omega
  /-- Debug mode: print inference trace -/
  debug : Bool := false
  /-- Current indentation level for debug output -/
  debugIndent : Nat := 0
  deriving Inhabited

namespace TCContext

def empty : TCContext := {}

/-- Increase debug indentation -/
def indent (ctx : TCContext) : TCContext :=
  { ctx with debugIndent := ctx.debugIndent + 1 }

/-- Get the current De Bruijn level -/
def level (ctx : TCContext) : DeBruijnLvl :=
  ctx.env.level

/-- Number of local bindings -/
def size (ctx : TCContext) : Nat :=
  ctx.locals.length

/-- Look up a local variable by name (O(1) via HashMap) -/
def lookupLocal (ctx : TCContext) (name : String) : Option CtxEntry :=
  ctx.localsByName.get? name

/-- Look up a local variable by De Bruijn level -/
def lookupLevel (ctx : TCContext) (lvl : DeBruijnLvl) : Option CtxEntry :=
  -- Level 0 is oldest, level (size-1) is newest
  -- List is newest first, so we need to reverse index
  let idx := ctx.size - lvl.lvl - 1
  ctx.locals[idx]?

/-- Look up a type abbreviation by QualifiedName -/
def lookupAbbrev (ctx : TCContext) (qn : Soma.Core.QualifiedName) : Option AbbrevInfo :=
  ctx.abbrevEnv.get? qn

/-- Extend context with a new binding, using a caller-supplied NbE value -/
def extendWith (ctx : TCContext) (name : String) (bindingId : Unique)
    (ty : Value) (qty : Quantity) (binder : BinderInfo) (span : Span)
    (nbeValue : Value) : TCContext :=
  let lvl := ctx.level
  let entry : CtxEntry := {
    name := name
    bindingId := bindingId
    fvarId := { id := bindingId.id, module := bindingId.module, original := name }
    type := ty
    qty := qty
    level := lvl
    binder := binder
    span := span
  }
  { ctx with
    locals := entry :: ctx.locals
    localsByName := ctx.localsByName.insert name entry
    env := ctx.env.extend name nbeValue
  }

/-- Extend context with a new binding whose NbE value is a fresh neutral -/
def extend (ctx : TCContext) (name : String) (bindingId : Unique)
    (ty : Value) (qty : Quantity) (binder : BinderInfo) (span : Span) : TCContext :=
  let varVal := Value.vNeutral ty (Neutral.nVar ⟨name, ctx.level⟩)
  ctx.extendWith name bindingId ty qty binder span varVal

/-- Update the current span -/
def withSpan (ctx : TCContext) (span : Span) : TCContext :=
  { ctx with currentSpan := span }

end TCContext

/-- Type checking monad: Reader + State + Except -/
abbrev TCM := ReaderT TCContext (StateT TCState (Except TCError))

namespace TCM

/-- Run the TCM with initial context and state -/
def run (m : TCM α) (ctx : TCContext := TCContext.empty)
    (state : TCState := TCState.empty) : Except TCError (α × TCState) :=
  m ctx state

/-- Get the current context -/
def getCtx : TCM TCContext := read

/-- Get the current state -/
def getState : TCM TCState := get

/-- Modify the state -/
def modifyState (f : TCState → TCState) : TCM Unit := modify f

/-- Postpone a constraint for later solving (simple version) -/
def postpone (c : Constraint) : TCM Unit := do
  modifyState (·.postpone c)

/-- Get the current span -/
def getSpan : TCM Span := do
  let ctx ← getCtx
  return ctx.currentSpan

/-- Run with a different span -/
def withSpan (span : Span) (m : TCM α) : TCM α :=
  withReader (·.withSpan span) m

/-- Get the current `ConstraintOrigin` -/
def getOrigin : TCM (Option ConstraintOrigin) := do
  let ctx ← getCtx
  return ctx.currentOrigin

/-- Run an action with a specific `ConstraintOrigin` in scope -/
def withOrigin (origin : ConstraintOrigin) (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with currentOrigin := some origin }) m

/-- Read the current `Path` accumulated by recursive `Value`-descent -/
def getPath : TCM Path := do
  let ctx ← getCtx
  return ctx.currentPath

/-- Run an action with a structural `PathStep` pushed onto `currentPath` -/
def withPathStep (step : PathStep) (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with currentPath := ctx.currentPath.push step }) m

/-- Run an action with a reset path -/
def withFreshPath (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with currentPath := Path.empty }) m

/-- Read the two values currently being unified at the root -/
def getUnifyRoot : TCM (Option (Soma.Core.Value × Soma.Core.Value)) := do
  let ctx ← getCtx
  return ctx.currentUnifyRoot

/-- Run an action with the given values pinned as the root unification targets -/
def withUnifyRoot (v1 v2 : Soma.Core.Value) (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with currentUnifyRoot := some (v1, v2) }) m

/-- Read whether we are already inside an outer-recognised application chain -/
def inApplicationChain : TCM Bool := do
  let ctx ← getCtx
  return ctx.inApplicationChain

/-- Mark a TCM action as running inside an application chain -/
def withInApplicationChain (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with inApplicationChain := true }) m

/-- Bring an inserted-implicits view into scope -/
def withImplicits (surface : String)
    (impls : Array (Soma.Core.MetaId × Soma.Core.Value × String))
    (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with currentImplicits := some (surface, impls) }) m

def getImplicits : TCM (Option (String × Array (Soma.Core.MetaId × Soma.Core.Value × String))) := do
  let ctx ← getCtx
  return ctx.currentImplicits

/-- Run with an extended context -/
def withBinding (name : String) (bindingId : Unique) (ty : Value)
    (qty : Quantity) (binder : BinderInfo) (span : Span) (m : TCM α) : TCM α :=
  withReader (·.extend name bindingId ty qty binder span) m

/-- Run with an extended context that binds `name` to a caller-supplied NbE value -/
def withBindingValue (name : String) (bindingId : Unique) (ty : Value)
    (qty : Quantity) (binder : BinderInfo) (span : Span)
    (nbeValue : Value) (m : TCM α) : TCM α :=
  withReader (·.extendWith name bindingId ty qty binder span nbeValue) m

/-- Record the elaborated type of a local binding, keyed by the start byte offset of the binding's name span -/
def recordLocalBindingType (nameSpan : Span) (ty : Value) : TCM Unit := do
  modifyState fun s =>
    { s with localTypes := s.localTypes.insert nameSpan.start.byteOffset ty }

/-- Look up a local variable -/
def lookupLocal (name : String) : TCM (Option CtxEntry) := do
  let ctx ← getCtx
  return ctx.lookupLocal name

/-- Install a batch of method self-reference overrides for the duration of `m` -/
def withMethodSelfRefs (entries : Array (String × Soma.Core.QualifiedName × Value))
    (m : TCM α) : TCM α :=
  withReader (fun ctx =>
    let merged := entries.foldl (init := ctx.methodSelfRefs) fun acc (name, qn, ty) =>
      acc.insert name (qn, ty)
    { ctx with methodSelfRefs := merged }) m

/-- Look up a method self-reference override by unqualified name -/
def lookupMethodSelfRef (name : String)
    : TCM (Option (Soma.Core.QualifiedName × Value)) := do
  let ctx ← getCtx
  return ctx.methodSelfRefs.get? name

/-- Record a dependency on a global definition (for incremental checking) -/
def recordGlobalDep (qn : Soma.Core.QualifiedName) : TCM Unit := do
  modifyState fun s => { s with globalDeps := s.globalDeps.insert qn }

/-- Look up a global (and record dependency for incremental checking) -/
def lookupGlobal (path : Array String) (name : String) : TCM (Option GlobalInfo) := do
  let ctx ← getCtx
  match ctx.globals.resolve ctx.currentNamespace path name with
  | some qn =>
    match ctx.globals.getDef qn with
    | some info =>
      recordGlobalDep qn
      return some info
    | none => return none
  | none => return none

/-- Look up a global directly by QualifiedName -/
def lookupGlobalByQN (qn : Soma.Core.QualifiedName) : TCM (Option GlobalInfo) := do
  let ctx ← getCtx
  return ctx.globals.getDef qn

/-- Collect the simple names of all locally-bound variables for typo suggestion -/
def localBindingNames : TCM (Array String) := do
  let ctx ← getCtx
  return ctx.localsByName.toArray.map (·.1)

/-- Collect the simple names of all known global declarations -/
def globalDeclarationNames : TCM (Array String) := do
  let ctx ← getCtx
  let fromTree := ctx.globals.root.collectPaths #[] |>.map (·.2.1)
  let fromImports := ctx.globals.imports.toArray.map (·.1)
  return fromTree ++ fromImports

/-- Suggest names similar to `target` from the local context first, then globals.
    Used to produce "did you mean X?" hints for unbound-identifier errors. -/
def suggestSimilarNames (target : String) (limit : Nat := 3) : TCM (Array String) := do
  let locals ← localBindingNames
  let localHits := Soma.Dependent.Suggest.suggestSimilar target locals limit
  if !localHits.isEmpty then return localHits
  let globals ← globalDeclarationNames
  return Soma.Dependent.Suggest.suggestSimilar target globals limit

/-- Look up all declarations registered under a wired-in role -/
def lookupWiredInAll (role : WiredRole) : TCM (Array GlobalInfo) := do
  let ctx ← getCtx
  return ctx.globals.wiredIn.getAll role

/-- Look up a wired-in role, requiring uniqueness -/
def lookupWiredIn (role : WiredRole) : TCM (Option GlobalInfo) := do
  let ctx ← getCtx
  return ctx.globals.wiredIn.getUnique? role

/-- Resolve primitive representation for a wired type unique when applicable -/
def lookupWiredPrimitiveOfTypeUnique (u : Soma.Unique) : TCM (Option Soma.Core.PrimType) := do
  let ctx ← getCtx
  let role? := ctx.globals.wiredIn.roles.fold (init := none) fun found role infos =>
    match found with
    | some _ => found
    | none =>
      if infos.any (fun info => info.name.id == u) then some role else none
  match role? with
  | some role => pure (WiredRole.primType? role)
  | none => pure none

/-- The `Value` for a wired-in primitive type -/
def primTypeValue? (p : Soma.Core.PrimType) : TCM (Option Value) := do
  let ctx ← getCtx
  let mut found : Option Soma.Unique := none
  for role in WiredRole.all do
    if found.isNone && WiredRole.primTyOfRole? role == some p then
      match ctx.globals.wiredIn.getUnique? role with
      | some info => found := some info.name.id
      | none => pure ()
  pure (found.map fun uid => Value.vDataType uid [])

/-- Like `primTypeValue?` but raises an internal error when the registry has no entry -/
def primTypeValue (p : Soma.Core.PrimType) (span : Soma.Syntax.Span := Soma.Syntax.Span.uninhabited)
    : TCM Value := do
  match ← primTypeValue? p with
  | some v => pure v
  | none =>
    throw (.compilerBug s!"wired primitive `{p.name}` has no `@[wired_in]` declaration in scope" span)

/-- Resolve the wired-in `Bool::True`/`Bool::False` constructor by boolean value -/
def wiredBoolConstructor (b : Bool) (span : Soma.Syntax.Span := Soma.Syntax.Span.uninhabited)
    : TCM (Soma.Core.QualifiedName × Nat × Value) := do
  let ctx ← getCtx
  match ctx.globals.wiredIn.getUnique? .typeBool with
  | none =>
    throw (.compilerBug "wired type `Bool` (role `type.bool`) is not registered" span)
  | some boolInfo =>
    let boolTy : Value := Value.vDataType boolInfo.name.id []
    let targetName : String := if b then "True" else "False"
    match ctx.globals.lookupInductive boolInfo.name with
    | none =>
      throw (.compilerBug s!"wired type `Bool` ({boolInfo.name.display}) has no inductive metadata" span)
    | some indMeta =>
      match indMeta.ctors.find? (fun c => c.simpleName == targetName) with
      | none =>
        throw (.compilerBug s!"wired `Bool` is missing constructor `{targetName}`" span)
      | some ctorMeta =>
        pure (ctorMeta.name, ctorMeta.tag, boolTy)

/-- Look up a type abbreviation by QualifiedName -/
def lookupAbbrev (qn : Soma.Core.QualifiedName) : TCM (Option AbbrevInfo) := do
  let ctx ← getCtx
  return ctx.lookupAbbrev qn

/-- Run with updated globals -/
def withGlobals (globals : Globals) (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with globals := globals }) m

/-- Get the current namespace path -/
def getCurrentNamespace : TCM (Array String) := do
  let ctx ← getCtx
  return ctx.currentNamespace

/-- Resolve a name to its QualifiedName through the namespace tree -/
def resolve (path : Array String) (name : String) : TCM (Option Soma.Core.QualifiedName) := do
  let ctx ← getCtx
  return ctx.globals.resolve ctx.currentNamespace path name

/-- Get the current De Bruijn level -/
def currentLevel : TCM DeBruijnLvl := do
  let ctx ← getCtx
  return ctx.level

-- todo: remove
/-- Throw a type checking error -/
def throw (e : TCError) : TCM α :=
  Except.error e

/-- Add an error but continue (for error recovery) -/
def addError (e : TCError) : TCM Unit := do
  modifyState (·.addError e)

/-- Create a fresh metavariable of the given type -/
def freshMeta (ty : Value) (piLevel : Option Nat := none)
    (origin : Soma.Core.MetaOrigin := .user)
    (displayHint : Option String := none) : TCM MetaId := do
  let ctx ← getCtx
  let state ← getState
  let (id, state') := state.freshMeta ty ctx.locals
    (piLevel := piLevel) (origin := origin) (displayHint := displayHint)
  set state'
  return id

/-- Create a fresh metavariable and return it as a Value -/
def freshMetaVal (ty : Value) (origin : Soma.Core.MetaOrigin := .user)
    (displayHint : Option String := none) : TCM Value := do
  let id ← freshMeta ty (origin := origin) (displayHint := displayHint)
  return .vNeutral ty (.nMeta id)

/-- Force-cycle detection -/
partial def wouldFormForceCycle (id : MetaId) (v : Value) : TCM Bool := do
  goVal v {}
where
  goVal (v : Value) (visited : Std.HashSet Nat) : TCM Bool := do
    match v with
    | .vType _ | .vIntLit _ | .vFloatLit _ | .vStringLit _
    | .vRowEmpty | .vLabelLit _ | .vRowSort | .vLabelSort => return false
    | .vPi _ _ _ dom _ => goVal dom visited
    | .vLam _ _ _ => return false
    | .vRowExtend label ty tail =>
      if ← goVal label visited then return true
      if ← goVal ty visited then return true
      goVal tail visited
    | .vRecord row | .vVariant row => goVal row visited
    | .vRecordVal fields => fields.anyM fun (_, v) => goVal v visited
    | .vDataType _ params => params.anyM fun p => goVal p visited
    | .vConstructor _ _ args _ => args.anyM fun a => goVal a visited
    | .vNeutral _ neu => goNeutral neu visited

  goNeutral (neu : Neutral) (visited : Std.HashSet Nat) : TCM Bool := do
    if ← goHead neu.head visited then return true
    neu.spine.anyM fun e =>
      match e with
      | .eApp arg => goVal arg visited
      | .eField _ => pure false

  goHead (h : Head) (visited : Std.HashSet Nat) : TCM Bool := do
    match h with
    | .hVar _ | .hConst _ _ | .hErrored => return false
    | .hMeta mid =>
      if mid == id then return true
      if visited.contains mid.id then return false
      let visited' := visited.insert mid.id
      let state ← getState
      match state.lookupMeta mid with
      | none => return false
      | some info =>
        match info.solution with
        | none => return false
        | some sol => goVal sol visited'
    | .hCase scruts motive _ =>
      if ← scruts.anyM fun s => goVal s visited then return true
      goVal motive visited

/-- Solve a metavariable -/
def solveMeta (id : MetaId) (v : Value) (callerTag : String := "?") : TCM Unit := do
  let _ := callerTag
  if ← wouldFormForceCycle id v then
    let span ← getSpan
    throw (.unificationFailed (.occursCheck id v Path.empty none) .general span #[] #[id])
  modifyState (·.solveMeta id v)

/-- Update metavariable solution for path compression -/
def updateMetaSolution (id : MetaId) (v : Value) : TCM Unit := do
  modifyState (·.solveMeta id v)

/-- Look up metavariable info -/
def lookupMeta (id : MetaId) : TCM (Option MetaInfo) := do
  let state ← getState
  return state.lookupMeta id

/-- Check if a metavariable is solved -/
def isMetaSolved (id : MetaId) : TCM Bool := do
  let state ← getState
  return state.metas.isSolved id

/-- Create a fresh level variable -/
def freshLevelVar (name : String := "") : TCM LevelVarId := do
  let state ← getState
  let (id, state') := state.freshLevelVar name
  set state'
  return id

/-- Create a fresh level and return it -/
def freshLevel (name : String := "") : TCM Level := do
  let id ← freshLevelVar name
  return .var id

/-- Install a solution for a level variable -/
def solveLevelVar (id : LevelVarId) (l : Level) : TCM Unit := do
  modifyState fun s => { s with levelSolutions := s.levelSolutions.insert id.id l }

/-- Apply current level solutions to a level-/
partial def zonkLevel (l : Level) : TCM Level := do
  let state ← getState
  let sols := state.levelSolutions
  return go sols l
where
  go (sols : Std.HashMap Nat Level) : Level → Level
    | .prop => .prop
    | .lit n => .lit n
    | .var v =>
      match sols.get? v.id with
      | some l' => go sols l'
      | none => .var v
    | .max l1 l2 => Level.mkMax (go sols l1) (go sols l2)
    | .succ l' => Level.mkSucc (go sols l')

/-- Get all postponed constraints (returns TrackedConstraints) -/
def getPostponedTracked : TCM (Array TrackedConstraint) := do
  let state ← getState
  return state.postponed

/-- Mark the current operation as stuck on the given dependency set -/
def markStuck (metas : Array MetaId) (levelVars : Array LevelVarId) : TCM Unit :=
  modifyState fun s => { s with stuckSignal := some (metas, levelVars) }

/-- Clear any pending stuck signal -/
def clearStuckSignal : TCM Unit :=
  modifyState fun s => { s with stuckSignal := none }

/-- Read the current stuck signal -/
def getStuckSignal : TCM (Option (Array MetaId × Array LevelVarId)) := do
  return (← getState).stuckSignal

/-- Whether we are currently collecting pattern-unification refinements -/
def isPatternUnifyMode : TCM Bool := do
  return (← getState).patternRefinementsBuffer?.isSome

/-- Whether we are currently descending through a known-injective head -/
def isInInjectiveDescent : TCM Bool := do
  return (← getCtx).inInjectiveDescent

/-- Run an action with `inInjectiveDescent` set -/
def withInjectiveDescent (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with inInjectiveDescent := true }) m

/-- Run an action with `inInjectiveDescent` cleared -/
def withoutInjectiveDescent (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with inInjectiveDescent := false }) m

/-- Record an index-equality refinement learned during pattern unification -/
def recordPatternRefinement (lvl : DeBruijnLvl) (replacement : Value) : TCM Unit := do
  modifyState fun s =>
    match s.patternRefinementsBuffer? with
    | some buf =>
      { s with patternRefinementsBuffer? := some (buf.insert lvl.lvl replacement) }
    | none => s

/-- Run `m` in pattern-unify mode and return the collected refinements alongside its result -/
def withPatternRefinements (m : TCM α) : TCM (α × Std.HashMap Nat Value) := do
  let savedBuffer := (← getState).patternRefinementsBuffer?
  modifyState fun s => { s with patternRefinementsBuffer? := some {} }
  try
    let a ← m
    let collected := (← getState).patternRefinementsBuffer?.getD {}
    modifyState fun s => { s with patternRefinementsBuffer? := savedBuffer }
    return (a, collected)
  catch e =>
    modifyState fun s => { s with patternRefinementsBuffer? := savedBuffer }
    throw e

/-- Generate a fresh unique identifier -/
def freshUnique (original : String) : TCM Unique := do
  let state ← getState
  let (u, state') := state.freshUnique original
  set state'
  return u

/-- Generate a fresh local Unique for a binding site -/
def freshLocalId (name : String) : TCM Unique :=
  freshUnique name

/-- Record usage of a variable. In erased context, usages don't count (compile-time only). -/
def useVar (bindingId : Unique) (count : Nat := 1) : TCM Unit := do
  let ctx ← getCtx
  -- In erased context, usages don't count towards runtime
  if ctx.qtyMultiplier != .zero then
    modifyState (·.useVar bindingId count)

/-- Get the recorded usage count of a variable -/
def getUsage (bindingId : Unique) : TCM Nat := do
  let state ← getState
  return state.getUsage bindingId

/-- Convert usage count to Quantity for compatibility checks -/
def countToQuantity (n : Nat) : Quantity :=
  match n with
  | 0 => .zero
  | 1 => .one
  | _ => .omega

/-- Run an action in erased context (quantity 0) -/
def inErasedContext (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with inErased := true, qtyMultiplier := .zero }) m

/-- Evaluate a Core.Expr to a Value using the current environment. -/
def evalExpr (e : Soma.Core.Expr) : TCM Value := do
  let ctx ← getCtx
  let state ← getState
  let evalCtx : EvalCtx := {
    env := ctx.env
    globals := ctx.globals.toGlobalEnvWithClasses ctx.instanceEnv
    metas := state.metas
  }
  return Soma.Core.evalCoreExpr evalCtx e

/-- Evaluate a Core.Expr to a Value using a specific environment -/
def evalExprInEnv (env : Env) (e : Soma.Core.Expr) : TCM Value := do
  let ctx ← getCtx
  let state ← getState
  let evalCtx : EvalCtx := {
    env := env
    globals := ctx.globals.toGlobalEnvWithClasses ctx.instanceEnv
    metas := state.metas
  }
  return Soma.Core.evalCoreExpr evalCtx e

/-- Print a debug message if debug mode is enabled -/
def debug (msg : String) : TCM Unit := do
  let ctx ← getCtx
  if ctx.debug then
    let indent := String.ofList (List.replicate (ctx.debugIndent * 2) ' ')
    dbg_trace s!"{indent}{msg}"
    pure ()

/-- Run an action with increased debug indentation -/
def withDebugIndent (m : TCM α) : TCM α :=
  withReader (·.indent) m

/-- Debug trace entering a function with its expression kind -/
def debugEnter (kind : String) (info : String := "") : TCM Unit := do
  if info.isEmpty then
    debug s!"┌─ {kind}"
  else
    debug s!"┌─ {kind}: {info}"

/-- Debug trace leaving a function with result -/
def debugLeave (kind : String) (result : String) : TCM Unit := do
  debug s!"└─ {kind} => {result}"

/-- Get the instance environment -/
def getInstanceEnv : TCM InstanceEnv := do
  let ctx ← getCtx
  return ctx.instanceEnv

/-- Run with a modified instance environment -/
def withInstanceEnv (env : InstanceEnv) (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with instanceEnv := env }) m

/-- Add a pending instance constraint -/
def addPendingInstance (classId : Unique) (args : Array Value) (metaId : MetaId)
    (span : Span) : TCM Unit := do
  let pending : PendingInstance := {
    metaId := metaId
    classId := classId
    args := args
    span := span
  }
  modifyState (·.addPendingInstance pending)

/-- Get all pending instance constraints -/
def getPendingInstances : TCM (Array PendingInstance) := do
  let state ← getState
  return state.getPendingInstances

/-- Add a deferred instance meta -/
def addDeferredInstanceMeta (metaId : MetaId) (domTy : Value) (span : Span) : TCM Unit := do
  modifyState (·.addDeferredInstanceMeta metaId domTy span)

/-- Look up a class by unique -/
def lookupClass (classId : Unique) : TCM (Option ClassInfo) := do
  let env ← getInstanceEnv
  return env.getClass classId

/-- Narrowed candidate instances via the discrimination tree -/
def getCandidateInstances (classId : Unique) (args : Array Value)
    : TCM (Array InstanceInfo) := do
  let env ← getInstanceEnv
  return env.getCandidateInstances classId args

/-- Try an action, rolling back state if it fails -/
def tryWithRollback (action : TCM α) : TCM (Option α) := do
  let stateBefore ← getState
  try
    let result ← action
    return some result
  catch _ =>
    set stateBefore
    return none

/-- Result of an action that may fail but should continue with a default -/
inductive RecoverResult (α : Type) where
  /-- Action succeeded with a value -/
  | ok (value : α)
  /-- Action failed, using default value -/
  | recovered (value : α) (error : TCError)
  deriving Inhabited

namespace RecoverResult

def value : RecoverResult α → α
  | .ok v => v
  | .recovered v _ => v

end RecoverResult

/-- Run an action, recovering with a default value on failure.
    The error is added to the error list but execution continues. -/
def recover (action : TCM α) (default : α) : TCM (RecoverResult α) := do
  let stateBefore ← getState
  try
    let result ← action
    return .ok result
  catch e =>
    -- Restore state to before the failed action
    set stateBefore
    -- But record the error for later reporting
    addError e
    return .recovered default e

/-- Run an action, recovering with a default value on failure.
    Returns just the value (error is still recorded). -/
def recoverWith (action : TCM α) (default : α) : TCM α := do
  let result ← recover action default
  return result.value

/-- Run an action, recovering with a lazily-computed default on failure. -/
def recoverWithM (action : TCM α) (mkDefault : TCM α) : TCM α := do
  let stateBefore ← getState
  try
    action
  catch e =>
    set stateBefore
    addError e
    mkDefault

/-- Create an error-recovery value at the given type -/
def errorPlaceholder (ty : Value) (_span : Span) : TCM Value := do
  return .vNeutral ty (Neutral.ofHead .hErrored)

/-- Create a Type placeholder for when we can't infer a type -/
def typePlaceholder (span : Span) : TCM Value := do
  errorPlaceholder (.vType .zero) span

/-- Run an action that might throw, converting throws to accumulated errors.
    Always returns a value (the default on failure). This is the primary
    mechanism for making type checking infallible. -/
def infallible (action : TCM α) (default : α) : TCM α := do
  recoverWith action default

/-- Like infallible but for actions that produce elaborated expressions.
    Creates a panic expression on failure. -/
def infallibleExpr (action : TCM (Value × Soma.Core.Expr))
    (span : Span) : TCM (Value × Soma.Core.Expr) := do
  let stateBefore ← getState
  try
    action
  catch e =>
    set stateBefore
    addError e
    let placeholderTy ← typePlaceholder span
    return (placeholderTy, .panic "_error")

end TCM

end Soma.Dependent
