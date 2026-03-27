import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Core.Expr
import Soma.Core.Intrinsic
import Soma.Dependent.Error
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

/-- A constraint that couldn't be solved immediately -/
inductive Constraint where
  /-- Unify two values -/
  | unify (v1 v2 : Value) (span : Span)
  /-- Check that v1 is a subtype of v2 -/
  | subtype (v1 v2 : Value) (span : Span)
  /-- Solve a level constraint -/
  | levelEq (l1 l2 : Level)
  /-- Solve a level ordering -/
  | levelLe (l1 l2 : Level)
  deriving Inhabited

namespace Constraint

/-- Get the span of a constraint -/
def span : Constraint → Span
  | .unify _ _ s => s
  | .subtype _ _ s => s
  | .levelEq _ _ => Span.uninhabited
  | .levelLe _ _ => Span.uninhabited

/-- Get a human-readable description of the constraint -/
def describe : Constraint → String
  | .unify v1 v2 _ => s!"unify `{v1}` with `{v2}`"
  | .subtype v1 v2 _ => s!"`{v1}` <: `{v2}`"
  | .levelEq l1 l2 => s!"level `{l1}` = `{l2}`"
  | .levelLe l1 l2 => s!"level `{l1}` ≤ `{l2}`"

end Constraint

/-- A tracked constraint with its ID, metas, and provenance -/
structure TrackedConstraint where
  /-- The underlying constraint -/
  constraint : Constraint
  /-- Constraint ID for dependency tracking -/
  constraintId : ConstraintId
  /-- Metas referenced by this constraint (cached for efficiency) -/
  metas : Array MetaId
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
  | typeDecl
  | constructor
  | projection
  | traitMethod
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

def qualifiedName (info : GlobalInfo) : Soma.Core.QualifiedName :=
  info.name

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
  deriving Inhabited, BEq, DecidableEq, Hashable, Repr, Serialize, Deserialize

namespace WiredRole

def canonical : WiredRole → String
  | .pair => "pair"
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

instance : ToString WiredRole := ⟨canonical⟩

def fromString? : String → Option WiredRole
  | "pair" => some .pair
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
  | _ => none

/-- Map wired type roles to canonical primitive representations when applicable -/
def primType? : WiredRole → Option Soma.Core.PrimType
  | .typeInt => some .int
  | .typeBool => some .bool
  | .typeString => none
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

/-- Scan attributes for @[wired_in "role"] and register if found (todo: register lazily) -/
def tryRegisterFromAttrs (w : WiredIn) (attrs : Array Soma.Syntax.Attribute) (info : GlobalInfo) : WiredIn :=
  attrs.foldl (init := w) fun acc attr =>
    if attr.name.name == "wired_in" then
      if h : 0 < attr.args.size then
        match attr.args[0] with
        | .lit (.string role _) =>
          match WiredRole.fromString? role with
          | some r => acc.register r info
          | none => acc
        | _ => acc
      else acc
    else acc

def pair (w : WiredIn) : Option GlobalInfo := w.getUnique? .pair
def cons (w : WiredIn) : Option GlobalInfo := w.getUnique? .cons
def nil  (w : WiredIn) : Option GlobalInfo := w.getUnique? .nil

/-- Find the wired role assigned to a particular global name -/
def roleOf? (w : WiredIn) (qn : Soma.Core.QualifiedName) : Option WiredRole :=
  w.roles.fold (init := none) fun found role infos =>
    match found with
    | some _ => found
    | none => if infos.any (fun info => info.name == qn) then some role else none

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

/-- Register intrinsic metadata for a qualified name -/
def registerIntrinsic (g : Globals) (name : Soma.Core.QualifiedName)
    (intrinsic : Soma.Core.Intrinsic) : Globals :=
  { g with intrinsics := g.intrinsics.insert name intrinsic }

/-- Look up intrinsic metadata by qualified name -/
def lookupIntrinsic (g : Globals) (name : Soma.Core.QualifiedName)
    : Option Soma.Core.Intrinsic :=
  g.intrinsics.get? name

/-- Register or refresh top-level inductive metadata for a type name -/
def registerInductive (g : Globals) (qn : Soma.Core.QualifiedName)
    (kind : InductiveKind) (typeVarNames : Array String := #[])
    (fieldNames : Array String := #[]) : Globals :=
  let metaInfo : InductiveMeta := match g.inductives.get? qn with
    | some existing =>
      { existing with
        kind := kind
        typeVarNames := typeVarNames
        fieldNames := fieldNames }
    | none =>
      { kind := kind
        typeVarNames := typeVarNames
        fieldNames := fieldNames }
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
  g.defs.fold (init := GlobalEnv.empty) fun acc qn info =>
    match info.value with
    | some v => acc.insert qn v
    | none => acc

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

/-- Display name for error messages -/
def displayName (c : ClassInfo) : String := c.classId.original

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

/-- Check if this instance has no constraints (is a ground instance) -/
def isGround (i : InstanceInfo) : Bool :=
  i.constraints.isEmpty

/-- Display name for error messages -/
def displayName (i : InstanceInfo) : String := i.instanceId.original

end InstanceInfo

/-- Environment tracking all type classes and their instances -/
structure InstanceEnv where
  /-- All registered classes, indexed by unique id -/
  classes : Std.HashMap Unique ClassInfo := {}
  /-- All registered instances, indexed by class unique -/
  instances : Std.HashMap Unique (Array InstanceInfo) := {}
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
  { env with instances := env.instances.insert info.classId (existing.push info) }

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
  { env with
    instances := env.instances.insert classId (existing.push info)
    nextInstanceId := env.nextInstanceId + 1
  }

/-- Look up a class by unique -/
def getClass (env : InstanceEnv) (classId : Unique) : Option ClassInfo :=
  env.classes.get? classId

/-- Look up all instances for a class -/
def getInstances (env : InstanceEnv) (classId : Unique) : Array InstanceInfo :=
  env.instances.getD classId #[]

/-- Check if a class exists -/
def hasClass (env : InstanceEnv) (classId : Unique) : Bool :=
  env.classes.contains classId

/-- Get total number of instances -/
def instanceCount (env : InstanceEnv) : Nat :=
  env.instances.fold (fun acc _ insts => acc + insts.size) 0

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

/-- Display name for error messages -/
def displayName (a : AbbrevInfo) : String := a.abbrevId.original

/-- Is this a parameterized abbreviation? -/
def isParameterized (a : AbbrevInfo) : Bool := a.arity > 0

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
  /-- Postponed constraints (tracked with IDs and meta references) -/
  postponed : Array TrackedConstraint := #[]
  /-- Worklist of constraint IDs to retry (populated when metas are solved) -/
  worklist : Array ConstraintId := #[]
  /-- Accumulated errors -/
  errors : Array TCError := #[]
  /-- Accumulated warnings -/
  warnings : Array TCWarning := #[]
  /-- Fresh name counter -/
  freshCounter : Nat := 0
  /-- Variable usage counts for QTT tracking (Unique -> exact count) -/
  usages : Std.HashMap Unique Nat := {}
  /-- Pending instance constraints to be resolved -/
  pendingInstances : Array PendingInstance := #[]
  /-- Deferred instance metas where class info couldn't be extracted yet -/
  deferredInstanceMetas : Array (MetaId × Value × Span) := #[]
  /-- Unique supply for generating compiler-internal names -/
  uniqueSupply : Soma.UniqueSupply := Soma.UniqueSupply.initial ""
  /-- Dependencies on global definitions (for incremental checking) -/
  globalDeps : Std.HashSet Soma.Core.QualifiedName := {}
  deriving Inhabited

namespace TCState

def empty : TCState := {}

/-- Create an initial state for a module -/
def forModule (moduleName : String) : TCState :=
  { uniqueSupply := Soma.UniqueSupply.initial moduleName }

/-- Create a fresh metavariable -/
def freshMeta (s : TCState) (ty : Value) (ctx : List CtxEntry) : MetaId × TCState :=
  let ctxList := ctx.map fun e => (e.name, e.type, e.qty)
  let (id, metas') := s.metas.fresh ty ctxList
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

/-- Add a postponed constraint (simple version, for backward compatibility) -/
def postpone (s : TCState) (c : Constraint) : TCState :=
  -- Create a tracked constraint with empty metas (will be populated by caller)
  let tc : TrackedConstraint := {
    constraint := c
    constraintId := ⟨0⟩ -- will be assigned when properly tracked
    metas := #[]
    origin := .unknown
    parentConstraints := #[]
  }
  { s with postponed := s.postponed.push tc }

/-- Add a postponed constraint with full dependency tracking -/
def postponeTracked (s : TCState) (c : Constraint) (metas : Array MetaId)
    (origin : ConstraintOrigin := .unknown) (parents : Array ConstraintId := #[])
    : ConstraintId × TCState :=
  -- Register the constraint in the dependency system
  let (cid, metas') := s.metas.registerConstraint metas
  let tc : TrackedConstraint := {
    constraint := c
    constraintId := cid
    metas := metas
    origin := origin
    parentConstraints := parents
  }
  (cid, { s with metas := metas', postponed := s.postponed.push tc })

/-- Add constraint IDs to the worklist (to be retried after a meta is solved) -/
def wakeConstraints (s : TCState) (cids : Array ConstraintId) : TCState :=
  { s with worklist := s.worklist ++ cids }

/-- Pop a constraint ID from the worklist -/
def popWorklist (s : TCState) : Option ConstraintId × TCState :=
  if s.worklist.isEmpty then
    (none, s)
  else
    let cid := s.worklist[0]!
    (some cid, { s with worklist := s.worklist.extract 1 s.worklist.size })

/-- Get a tracked constraint by ID -/
def getConstraint (s : TCState) (cid : ConstraintId) : Option TrackedConstraint :=
  s.postponed.find? (·.constraintId == cid)

/-- Remove a constraint by ID (after it's been solved) -/
def removeConstraint (s : TCState) (cid : ConstraintId) : TCState :=
  let postponed' := s.postponed.filter (·.constraintId != cid)
  let metas' := s.metas.removeConstraint cid
  { s with postponed := postponed', metas := metas' }

/-- Add an error -/
def addError (s : TCState) (e : TCError) : TCState :=
  { s with errors := s.errors.push e }

/-- Add a warning -/
def addWarning (s : TCState) (w : TCWarning) : TCState :=
  { s with warnings := s.warnings.push w }

/-- Generate a fresh name -/
def freshName (s : TCState) (base : String) : String × TCState :=
  let name := s!"{base}_{s.freshCounter}"
  (name, { s with freshCounter := s.freshCounter + 1 })

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

/-- Add a pending instance constraint -/
def addPendingInstance (s : TCState) (p : PendingInstance) : TCState :=
  { s with pendingInstances := s.pendingInstances.push p }

/-- Get all pending instances -/
def getPendingInstances (s : TCState) : Array PendingInstance :=
  s.pendingInstances

/-- Clear pending instances -/
def clearPendingInstances (s : TCState) : TCState :=
  { s with pendingInstances := #[] }

/-- Add a deferred instance meta -/
def addDeferredInstanceMeta (s : TCState) (metaId : MetaId) (domTy : Value) (span : Span) : TCState :=
  { s with deferredInstanceMetas := s.deferredInstanceMetas.push (metaId, domTy, span) }

/-- Get deferred instance metas -/
def getDeferredInstanceMetas (s : TCState) : Array (MetaId × Value × Span) :=
  s.deferredInstanceMetas

/-- Clear deferred instance metas -/
def clearDeferredInstanceMetas (s : TCState) : TCState :=
  { s with deferredInstanceMetas := #[] }

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
  /-- Current span (for error reporting) -/
  currentSpan : Span := Span.uninhabited
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

/-- Create a context with debug mode enabled -/
def withDebug (ctx : TCContext) : TCContext :=
  { ctx with debug := true }

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

/-- Look up a global by resolving through the namespace tree, then fetching from defs -/
def lookupGlobal (ctx : TCContext) (path : Array String) (name : String) : Option GlobalInfo :=
  match ctx.globals.resolve ctx.currentNamespace path name with
  | some qn => ctx.globals.getDef qn
  | none => none

/-- Look up a global directly by QualifiedName -/
def lookupGlobalByQN (ctx : TCContext) (qn : Soma.Core.QualifiedName) : Option GlobalInfo :=
  ctx.globals.getDef qn

/-- Look up a type abbreviation by QualifiedName -/
def lookupAbbrev (ctx : TCContext) (qn : Soma.Core.QualifiedName) : Option AbbrevInfo :=
  ctx.abbrevEnv.get? qn

/-- Extend context with a new binding -/
def extend (ctx : TCContext) (name : String) (bindingId : Unique)
    (ty : Value) (qty : Quantity) (binder : BinderInfo) (span : Span) : TCContext :=
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
  -- Create a neutral variable for NbE
  let varVal := Value.vNeutral ty (Neutral.nVar ⟨name, lvl⟩)
  -- When entering a zero-quantity binder, we enter erased context
  -- and set the quantity multiplier to zero (all usages become erased)
  let enteringErased := qty == .zero
  { ctx with
    locals := entry :: ctx.locals
    localsByName := ctx.localsByName.insert name entry
    env := ctx.env.extend name varVal
    inErased := ctx.inErased || enteringErased
    qtyMultiplier := if enteringErased then .zero else ctx.qtyMultiplier
  }

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

/-- Run and extract just the result -/
def run' (m : TCM α) (ctx : TCContext := TCContext.empty)
    (state : TCState := TCState.empty) : Except TCError α :=
  (m.run ctx state).map (·.1)

/-- Get the current context -/
def getCtx : TCM TCContext := read

/-- Get the current state -/
def getState : TCM TCState := get

/-- Modify the state -/
def modifyState (f : TCState → TCState) : TCM Unit := modify f

/-- Get the current span -/
def getSpan : TCM Span := do
  let ctx ← getCtx
  return ctx.currentSpan

/-- Run with a different span -/
def withSpan (span : Span) (m : TCM α) : TCM α :=
  withReader (·.withSpan span) m

/-- Run with an extended context -/
def withBinding (name : String) (bindingId : Unique) (ty : Value)
    (qty : Quantity) (binder : BinderInfo) (span : Span) (m : TCM α) : TCM α :=
  withReader (·.extend name bindingId ty qty binder span) m

/-- Look up a local variable -/
def lookupLocal (name : String) : TCM (Option CtxEntry) := do
  let ctx ← getCtx
  return ctx.lookupLocal name

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

/-- Look up a global without recording a dependency -/
def lookupGlobalNoDep (path : Array String) (name : String) : TCM (Option GlobalInfo) := do
  let ctx ← getCtx
  return ctx.lookupGlobal path name

/-- Look up a global directly by QualifiedName -/
def lookupGlobalByQN (qn : Soma.Core.QualifiedName) : TCM (Option GlobalInfo) := do
  let ctx ← getCtx
  return ctx.globals.getDef qn


/-- Look up all declarations registered under a wired-in role -/
def lookupWiredInAll (role : WiredRole) : TCM (Array GlobalInfo) := do
  let ctx ← getCtx
  return ctx.globals.wiredIn.getAll role

/-- Look up a wired-in role, requiring uniqueness -/
def lookupWiredIn (role : WiredRole) : TCM (Option GlobalInfo) := do
  let ctx ← getCtx
  return ctx.globals.wiredIn.getUnique? role

/-- Look up a wired-in role by textual role name -/
def lookupWiredInByName (role : String) : TCM (Option GlobalInfo) := do
  match WiredRole.fromString? role with
  | some r => lookupWiredIn r
  | none => pure none

/-- Resolve the wired role associated with a global declaration name -/
def lookupWiredRoleOfGlobal (qn : Soma.Core.QualifiedName) : TCM (Option WiredRole) := do
  let ctx ← getCtx
  return ctx.globals.wiredIn.roleOf? qn

/-- Resolve primitive representation for a wired global type declaration when applicable -/
def lookupWiredPrimitiveOfGlobal (qn : Soma.Core.QualifiedName) : TCM (Option Soma.Core.PrimType) := do
  match ← lookupWiredRoleOfGlobal qn with
  | some role => pure (WiredRole.primType? role)
  | none => pure none

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

/-- Look up a type abbreviation by QualifiedName -/
def lookupAbbrev (qn : Soma.Core.QualifiedName) : TCM (Option AbbrevInfo) := do
  let ctx ← getCtx
  return ctx.lookupAbbrev qn

/-- Get all recorded global dependencies -/
def getGlobalDeps : TCM (Std.HashSet Soma.Core.QualifiedName) := do
  let state ← getState
  return state.globalDeps

/-- Clear recorded global dependencies (call at start of checking a new definition) -/
def clearGlobalDeps : TCM Unit := do
  modifyState fun s => { s with globalDeps := {} }

/-- Run an action and collect its global dependencies -/
def withDependencyTracking (action : TCM α) : TCM (α × Std.HashSet Soma.Core.QualifiedName) := do
  clearGlobalDeps
  let result ← action
  let deps ← getGlobalDeps
  return (result, deps)

/-- Run with updated globals -/
def withGlobals (globals : Globals) (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with globals := globals }) m

/-- Run with updated abbreviations -/
def withAbbrevEnv (abbrevEnv : AbbrevEnv) (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with abbrevEnv := abbrevEnv }) m

/-- Run with both globals and abbreviations -/
def withGlobalsAndAbbrevs (globals : Globals) (abbrevEnv : AbbrevEnv)
    (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with globals := globals, abbrevEnv := abbrevEnv }) m

/-- Run inside a child namespace -/
def withNamespace (name : String) (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with currentNamespace := ctx.currentNamespace.push name }) m

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

/-- Get the NbE environment -/
def getEnv : TCM Env := do
  let ctx ← getCtx
  return ctx.env

/-- Get all local bindings as a list for metavariable context -/
def getLocals : TCM (List CtxEntry) := do
  let ctx ← getCtx
  return ctx.locals

-- todo: remove
/-- Throw a type checking error -/
def throw (e : TCError) : TCM α :=
  Except.error e

/-- Add an error but continue (for error recovery) -/
def addError (e : TCError) : TCM Unit := do
  modifyState (·.addError e)

/-- Add a warning -/
def addWarning (w : TCWarning) : TCM Unit := do
  modifyState (·.addWarning w)

/-- Check if there are errors -/
def hasErrors : TCM Bool := do
  let state ← getState
  return !state.errors.isEmpty

/-- Get all errors -/
def getErrors : TCM (Array TCError) := do
  let state ← getState
  return state.errors

/-- Create a fresh metavariable of the given type -/
def freshMeta (ty : Value) : TCM MetaId := do
  let ctx ← getCtx
  let state ← getState
  let (id, state') := state.freshMeta ty ctx.locals
  set state'
  return id

def getMetaCount : TCM Nat := do
  let state ← getState
  return state.metas.nextId

/-- Create a fresh metavariable and return it as a Value -/
def freshMetaVal (ty : Value) : TCM Value := do
  let id ← freshMeta ty
  return .vNeutral ty (.nMeta id)

/-- Solve a metavariable -/
def solveMeta (id : MetaId) (v : Value) : TCM Unit := do
  modifyState (·.solveMeta id v)

/-- Clear a metavariable's solution, making it unsolved again -/
def unsolvedMeta (id : MetaId) : TCM Unit := do
  modifyState fun s => { s with metas := s.metas.unsolve id }

/-- Update metavariable solution for path compression.
    This is a lightweight version of solveMeta that just updates the solution
    without any side effects. Used by `force` to implement union-find style
    path compression. -/
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

/-- Postpone a constraint for later solving (simple version) -/
def postpone (c : Constraint) : TCM Unit := do
  modifyState (·.postpone c)

/-- Postpone a constraint with full dependency tracking -/
def postponeTracked (c : Constraint) (metas : Array MetaId)
    (origin : ConstraintOrigin := .unknown) (parents : Array ConstraintId := #[])
    : TCM ConstraintId := do
  let state ← getState
  let (cid, state') := state.postponeTracked c metas origin parents
  set state'
  return cid

/-- Postpone a constraint with origin derived from current context -/
def postponeWithOrigin (c : Constraint) (metas : Array MetaId)
    (origin : ConstraintOrigin) : TCM ConstraintId := do
  postponeTracked c metas origin #[]

/-- Get the constraint chain leading to a constraint (for error reporting) -/
def getConstraintChain (cid : ConstraintId) : TCM (Array ConstraintInfo) := do
  let state ← getState
  let mut chain : Array ConstraintInfo := #[]
  let mut visited : Std.HashSet Nat := {}
  let mut queue : Array ConstraintId := #[cid]

  while h : queue.size > 0 do
    let current := queue[0]'h
    queue := queue.extract 1 queue.size

    if visited.contains current.id then
      continue
    visited := visited.insert current.id

    match state.getConstraint current with
    | some tc =>
      chain := chain.push tc.toInfo
      for parent in tc.parentConstraints do
        if !visited.contains parent.id then
          queue := queue.push parent
    | none => pure ()

  return chain

/-- Build constraint info for all constraints involving a metavariable -/
def getMetaConstraintInfo (mid : MetaId) : TCM (Array MetaConstraintInfo) := do
  let state ← getState
  let mut infos : Array MetaConstraintInfo := #[]

  for tc in state.postponed do
    if tc.metas.contains mid then
      -- Check if this constraint is blocked
      let isBlocked ← do
        let mut blocked := false
        for m in tc.metas do
          let solved ← isMetaSolved m
          if !solved && m != mid then
            blocked := true
            break
        pure blocked

      infos := infos.push {
        description := tc.constraint.describe
        origin := tc.origin
        isBlocked := isBlocked
      }

  return infos

/-- Get all postponed constraints (returns TrackedConstraints) -/
def getPostponedTracked : TCM (Array TrackedConstraint) := do
  let state ← getState
  return state.postponed

/-- Get all postponed constraints (returns just Constraints for backward compat) -/
def getPostponed : TCM (Array Constraint) := do
  let state ← getState
  return state.postponed.map (·.constraint)

/-- Clear postponed constraints -/
def clearPostponed : TCM Unit := do
  modifyState fun s => { s with postponed := #[], worklist := #[] }

/-- Wake up constraints that depend on a solved metavariable -/
def wakeConstraintsFor (mid : MetaId) : TCM Unit := do
  let state ← getState
  let affectedCids := state.metas.getAffectedConstraints mid
  modifyState (·.wakeConstraints affectedCids)

/-- Pop a constraint from the worklist -/
def popWorklist : TCM (Option ConstraintId) := do
  let state ← getState
  let (cid?, state') := state.popWorklist
  set state'
  return cid?

/-- Get a constraint by ID -/
def getConstraintById (cid : ConstraintId) : TCM (Option TrackedConstraint) := do
  let state ← getState
  return state.getConstraint cid

/-- Remove a solved constraint -/
def removeConstraint (cid : ConstraintId) : TCM Unit := do
  modifyState (·.removeConstraint cid)

/-- Get constraint complexity (number of unsolved metas) -/
def constraintComplexity (cid : ConstraintId) : TCM Nat := do
  let state ← getState
  return state.metas.constraintComplexity cid

/-- Generate a fresh name -/
def freshName (base : String := "x") : TCM String := do
  let state ← getState
  let (name, state') := state.freshName base
  set state'
  return name

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

/-- Check that a variable's usage is compatible with its declared quantity -/
def checkUsage (bindingId : Unique) (declared : Quantity) (span : Span) : TCM Unit := do
  let count ← getUsage bindingId
  let actual := countToQuantity count
  -- Check: actual ≤ declared (in the quantity semiring ordering)
  if !actual.le declared then
    throw (.quantityMismatch declared actual bindingId.original span)

/-- Check all linear variables in scope are used exactly once -/
def checkLinearVarsUsed : TCM Unit := do
  let ctx ← getCtx
  for entry in ctx.locals do
    if entry.qty == .one then
      let count ← getUsage entry.bindingId
      if count == 0 then
        throw (.linearNotUsed entry.name entry.span)
      else if count != 1 then
        -- Used more than once
        let actual := countToQuantity count
        addError (.quantityMismatch .one actual entry.name entry.span)

/-- Run an action with quantity multiplier set (for checking under binders) -/
def withQtyMultiplier (qty : Quantity) (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with qtyMultiplier := ctx.qtyMultiplier.mul qty }) m

/-- Run an action in erased context (quantity 0) -/
def inErasedContext (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with inErased := true, qtyMultiplier := .zero }) m

/-- Run an action with fresh usage tracking, returning the usage counts -/
def withFreshUsages (m : TCM α) : TCM (α × Std.HashMap Unique Nat) := do
  let state ← getState
  let savedUsages := state.saveUsages
  modifyState (·.clearUsages)
  let result ← m
  let state' ← getState
  let newUsages := state'.usages
  modifyState (·.restoreUsages savedUsages)
  return (result, newUsages)

/-! ## Evaluation -/

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

/-- Create a Pi type value -/
def mkPi (qty : Quantity) (binder : BinderInfo) (name : String) (domain : Value)
    (codomain : Closure) : Value :=
  .vPi qty binder name domain codomain

/-- Create a simple (non-dependent) function type -/
def mkArrow (domain codomain : Value) : TCM Value := do
  -- For non-dependent function types, use HOAS-style closure
  -- The codomain doesn't depend on the argument, so just store it directly
  return .vPi .omega .explicit "_" domain (Closure.const "_" codomain)

/-- Check if we're currently in erased context -/
def isInErasedContext : TCM Bool := do
  let ctx ← getCtx
  return ctx.inErased

/-- Check if debug mode is enabled -/
def isDebug : TCM Bool := do
  let ctx ← getCtx
  return ctx.debug

/-- Get the current indentation string -/
def debugIndentStr : TCM String := do
  let ctx ← getCtx
  return String.ofList (List.replicate (ctx.debugIndent * 2) ' ')

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

/-- Debug trace for intermediate steps -/
def debugStep (msg : String) : TCM Unit := do
  debug s!"│  {msg}"

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

/-- Clear pending instance constraints -/
def clearPendingInstances : TCM Unit := do
  modifyState (·.clearPendingInstances)

/-- Add a deferred instance meta -/
def addDeferredInstanceMeta (metaId : MetaId) (domTy : Value) (span : Span) : TCM Unit := do
  modifyState (·.addDeferredInstanceMeta metaId domTy span)

/-- Get deferred instance metas -/
def getDeferredInstanceMetas : TCM (Array (MetaId × Value × Span)) := do
  let state ← getState
  return state.getDeferredInstanceMetas

/-- Clear deferred instance metas -/
def clearDeferredInstanceMetas : TCM Unit := do
  modifyState (·.clearDeferredInstanceMetas)

/-- Look up a class by unique -/
def lookupClass (classId : Unique) : TCM (Option ClassInfo) := do
  let env ← getInstanceEnv
  return env.getClass classId

/-- Get all instances for a class -/
def getClassInstances (classId : Unique) : TCM (Array InstanceInfo) := do
  let env ← getInstanceEnv
  return env.getInstances classId

/-- Check if a class exists -/
def hasClass (classId : Unique) : TCM Bool := do
  let env ← getInstanceEnv
  return env.hasClass classId

/-- Create a fresh metavariable for an instance argument -/
def freshInstanceMeta (classId : Unique) (args : Array Value) (span : Span) : TCM Value := do
  -- Create a placeholder type for the instance
  -- todo: make this the actual class record type
  let instTy := Value.vType .zero
  let metaId ← freshMeta instTy
  -- Register this as a pending instance to resolve
  addPendingInstance classId args metaId span
  return .vNeutral instTy (.nMeta metaId)

/-- Create a constant closure (for non-dependent types) -/
def mkConstClosure (name : String) (result : Value) : TCM Closure := do
  return Closure.const name result

/-- Create an empty/placeholder closure from the current environment -/
def mkEmptyClosure (name : String) : TCM Closure := do
  let ctx ← getCtx
  return Closure.mkEmpty name ctx.env

/-- Create a closure with a specific Expr body -/
def mkClosureWithExpr (name : String) (body : Soma.Core.Expr) : TCM Closure := do
  let ctx ← getCtx
  return Closure.mkWithBody name ctx.env body

/-- Run an action, rolling back state if it throws an error -/
def withRollbackOnFailure (action : TCM α) : TCM α := do
  let stateBefore ← getState
  try
    action
  catch e =>
    set stateBefore
    throw e

/-- Try an action, rolling back state if it fails -/
def tryWithRollback (action : TCM α) : TCM (Option α) := do
  let stateBefore ← getState
  try
    let result ← action
    return some result
  catch _ =>
    set stateBefore
    return none

/-- Run an action speculatively: if it succeeds, keep the state changes,
    If it fails, rollback state and return the given default value -/
def speculatively (action : TCM α) (default : α) : TCM α := do
  let stateBefore ← getState
  try
    action
  catch _ =>
    set stateBefore
    return default

/-- Try multiple alternatives in order, with state rollback between attempts -/
def tryAlternatives (actions : List (TCM α)) : TCM α := do
  let stateBefore ← getState
  let mut lastError : Option TCError := none
  for action in actions do
    try
      let result ← action
      return result
    catch e =>
      set stateBefore
      lastError := some e
  match lastError with
  | some e => throw e
  | none => throw (.internalError "tryAlternatives: empty action list" Span.uninhabited)

/-! ## Error Recovery Infrastructure

These utilities support infallible type checking by:
1. Collecting errors without stopping execution
2. Providing placeholder values when errors occur
3. Bounding recursion to prevent stack overflows
4. Enabling partial results even when some definitions fail
-/

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

def isOk : RecoverResult α → Bool
  | .ok _ => true
  | .recovered _ _ => false

def error? : RecoverResult α → Option TCError
  | .ok _ => none
  | .recovered _ e => some e

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

/-- Create an error placeholder value (a neutral with an error meta).
    Used when type checking fails but we need to continue. -/
def errorPlaceholder (ty : Value) (_span : Span) : TCM Value := do
  let metaId ← freshMeta ty
  return .vNeutral ty (.nMeta metaId)

/-- Create a Type placeholder for when we can't infer a type -/
def typePlaceholder (span : Span) : TCM Value := do
  errorPlaceholder (.vType .zero) span

/-- Run an action with bounded recursion depth.
    Returns default if depth is exceeded. -/
def withFuel [Inhabited α] (fuel : Nat) (action : Nat → TCM α) (span : Span) : TCM α := do
  if fuel == 0 then
    addError (.internalError "recursion limit exceeded" span)
    return default
  else
    action (fuel - 1)

/-- Default recursion fuel for deep operations -/
def defaultFuel : Nat := 1000

/-- Run a potentially deep recursive action with default fuel -/
def bounded [Inhabited α] (action : Nat → TCM α) (span : Span) : TCM α :=
  withFuel defaultFuel action span

/-- Collect results from multiple actions, continuing even if some fail.
    Returns all successful results and records all errors. -/
def collectResults (actions : Array (TCM α)) (default : α) : TCM (Array α) := do
  let mut results := #[]
  for action in actions do
    let result ← recover action default
    results := results.push result.value
  return results

/-- Map over an array with error recovery for each element -/
def mapRecover (arr : Array α) (f : α → TCM β) (default : β) : TCM (Array β) := do
  let mut results := #[]
  for x in arr do
    let result ← recover (f x) default
    results := results.push result.value
  return results

/-- Fold over an array with error recovery, continuing on failures -/
def foldRecover (arr : Array α) (init : β) (f : β → α → TCM β) : TCM β := do
  let mut acc := init
  for x in arr do
    match ← recover (f acc x) acc with
    | .ok newAcc => acc := newAcc
    | .recovered _ _ => pure ()  -- Keep old accumulator on failure
  return acc

/-- Check if we're in error recovery mode (have accumulated errors) -/
def inRecoveryMode : TCM Bool := do
  let state ← getState
  return !state.errors.isEmpty

/-- Get all accumulated errors so far -/
def getAccumulatedErrors : TCM (Array TCError) := do
  let state ← getState
  return state.errors

/-- Clear accumulated errors (use with caution, mainly for testing) -/
def clearAccumulatedErrors : TCM Unit := do
  modifyState fun s => { s with errors := #[] }

/-- Run an action in a "sandbox" - errors are collected but not propagated to parent.
    Returns (result, errors collected during action). -/
def sandbox (action : TCM α) (default : α) : TCM (α × Array TCError) := do
  let errorsBefore ← getAccumulatedErrors
  clearAccumulatedErrors
  let result ← recoverWith action default
  let newErrors ← getAccumulatedErrors
  modifyState fun s => { s with errors := errorsBefore }
  return (result, newErrors)

/-- Require that an action succeeds, but if it fails, add error and return default.
    Unlike `recover`, this is for "soft" requirements that shouldn't stop checking. -/
def softRequire (action : TCM α) (default : α) (errorMsg : String) (span : Span) : TCM α := do
  match ← tryWithRollback action with
  | some result => return result
  | none =>
    addError (.internalError errorMsg span)
    return default

/-- Assert a condition, adding an error if false but continuing execution -/
def softAssert (cond : Bool) (errorMsg : String) (span : Span) : TCM Unit := do
  if !cond then
    addError (.internalError errorMsg span)

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
