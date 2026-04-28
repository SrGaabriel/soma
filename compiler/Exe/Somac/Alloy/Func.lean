import Somac.Alloy.Block
import Kenosis

namespace Somac.Alloy

/-- Function parameter -/
structure Param (n : Nat) where
  id : LocalId
  name : String
  ty : Ty n
  deriving Inhabited

namespace Param

def instantiate (p : Param n) (env : TyEnv n) : Param 0 :=
  { id := p.id, name := p.name, ty := Somac.Alloy.instantiate p.ty env }

private def toStringAux : Param n → String
  | p => s!"{p.id}: {p.ty}"

instance : ToString (Param n) where
  toString := toStringAux

end Param

/-- Monomorphic parameter -/
abbrev ClosedParam := Param 0

/-- Function signature indexed by type variable count -/
structure Signature (n : Nat) where
  name : String
  typeParamNames : Array String := #[]
  params : Array (Param n)
  retTy : Ty n
  isClosure : Bool := false
  deriving Inhabited

namespace Signature

def arity (sig : Signature n) : Nat := sig.params.size

def isPolymorphic (_ : Signature n) : Bool := n > 0

def paramTypes (sig : Signature n) : Array (Ty n) := sig.params.map (·.ty)

/-- Instantiate all types in a signature -/
def instantiate (sig : Signature n) (env : TyEnv n) (newName : String) : Signature 0 :=
  { name := newName
  , typeParamNames := #[]
  , params := sig.params.map (·.instantiate env)
  , retTy := Somac.Alloy.instantiate sig.retTy env
  , isClosure := sig.isClosure
  }

private def toStringAux : Signature n → String
  | sig =>
    let closureStr := if sig.isClosure then " [closure]" else ""
    let typeParamsStr := if sig.typeParamNames.isEmpty then ""
      else s!"<{String.intercalate ", " sig.typeParamNames.toList}>"
    let paramsStr := String.intercalate ", " (sig.params.toList.map ToString.toString)
    s!"fn {sig.name}{typeParamsStr}({paramsStr}) -> {sig.retTy}{closureStr}"

instance : ToString (Signature n) where
  toString := toStringAux

end Signature

/-- Monomorphic signature -/
abbrev ClosedSignature := Signature 0

/-- Function attributes -/
structure FuncAttrs where
  /-- Should be inlined -/
  inline : Bool := false
  /-- Should never be inlined -/
  noInline : Bool := false
  /-- External function (no body) -/
  extern : Option String := none
  /-- Pure function (no side effects) -/
  pure : Bool := false
  /-- Always tail-call optimize -/
  tailCall : Bool := false
  /-- Wired-in function role -/
  wiredRole : Option WiredFunc := none
  deriving Repr, BEq, Inhabited, Serialize, Deserialize

namespace FuncAttrs

def default : FuncAttrs := {}

instance : ToString FuncAttrs where
  toString a :=
    let attrs : List String := []
    let attrs := if a.inline then attrs ++ ["inline"] else attrs
    let attrs := if a.noInline then attrs ++ ["noinline"] else attrs
    let attrs := match a.extern with
      | some name => attrs ++ [s!"extern(\"{name}\")"]
      | none => attrs
    let attrs := if a.pure then attrs ++ ["pure"] else attrs
    let attrs := if a.tailCall then attrs ++ ["tailcall"] else attrs
    let attrs := match a.wiredRole with
      | some role => attrs ++ [s!"wired({repr role})"]
      | none => attrs
    if attrs.isEmpty then "" else s!"[{String.intercalate ", " attrs}]"

end FuncAttrs


/-- A complete function -/
structure Func (n : Nat) where
  id : FuncId
  sig : Signature n
  body : Option (CFG n) := none
  attrs : FuncAttrs := {}
  /-- Next available local ID -/
  nextLocalId : Nat := 0
  localTypes : Std.HashMap Nat (Ty n) := {}
  deriving Inhabited

namespace Func

def extern (id : FuncId) (name : String) (params : Array (Param 0)) (retTy : ClosedTy)
    (externName : String) : Func 0 :=
  { id
  , sig := { name, params, retTy }
  , body := none
  , attrs := { extern := some externName }
  , nextLocalId := params.size
  }

def withBody (id : FuncId) (sig : Signature n) (cfg : CFG n) : Func n :=
  let paramTypes := sig.params.foldl (init := ({} : Std.HashMap Nat (Ty n))) fun acc p =>
    acc.insert p.id.id p.ty
  { id
  , sig
  , body := some cfg
  , nextLocalId := sig.params.size
  , localTypes := paramTypes
  }

def isExtern (f : Func n) : Bool := f.attrs.extern.isSome

def isPolymorphic (_ : Func n) : Bool := n > 0

def numTypeParams (_ : Func n) : Nat := n

def freshLocal (f : Func n) : LocalId × Func n :=
  (⟨f.nextLocalId⟩, { f with nextLocalId := f.nextLocalId + 1 })

def freshLocalTyped (f : Func n) (ty : Ty n) : LocalId × Func n :=
  let id := ⟨f.nextLocalId⟩
  (id, { f with
    nextLocalId := f.nextLocalId + 1
    localTypes := f.localTypes.insert id.id ty
  })

def getLocalType (f : Func n) (id : LocalId) : Option (Ty n) :=
  f.localTypes.get? id.id

def setLocalType (f : Func n) (id : LocalId) (ty : Ty n) : Func n :=
  { f with localTypes := f.localTypes.insert id.id ty }

def updateBody (f : Func n) (update : CFG n → CFG n) : Func n :=
  match f.body with
  | some cfg => { f with body := some (update cfg) }
  | none => f

def blocks (f : Func n) : Array (Block n) :=
  match f.body with
  | some cfg => cfg.allBlocks
  | none => #[]

/-- Instantiate a polymorphic function to produce a monomorphic one -/
def instantiate (f : Func n) (env : TyEnv n) (newId : FuncId) (newName : String) : Func 0 :=
  let newSig := f.sig.instantiate env newName
  let newBody := f.body.map (·.instantiate env)
  let newLocalTypes := f.localTypes.fold
    (init := ({} : Std.HashMap Nat ClosedTy)) fun acc id ty =>
      acc.insert id (Somac.Alloy.instantiate ty env)
  { id := newId
  , sig := newSig
  , body := newBody
  , attrs := f.attrs
  , nextLocalId := f.nextLocalId
  , localTypes := newLocalTypes
  }

private def toStringAux : Func n → String
  | f =>
    let attrsStr := if f.attrs == FuncAttrs.default then ""
      else s!"{f.attrs} "
    let header := s!"{attrsStr}{f.sig}"
    match f.body with
    | none => header
    | some cfg =>
      let bodyStr := String.intercalate "\n\n" (cfg.allBlocks.toList.map ToString.toString)
      s!"{header} \{\n{bodyStr}\n}"

instance : ToString (Func n) where
  toString := toStringAux

end Func

/-- Monomorphic function -/
abbrev ClosedFunc := Func 0

/-- A function with existentially quantified arity -/
abbrev SomeFunc := Σ n, Func n

namespace SomeFunc

def id (f : SomeFunc) : FuncId := f.2.id
def name (f : SomeFunc) : String := f.2.sig.name
def arity (f : SomeFunc) : Nat := f.1
def isPolymorphic (f : SomeFunc) : Bool := f.1 > 0
def isMono (f : SomeFunc) : Bool := f.1 == 0

/-- Get as monomorphic if arity is 0 -/
def asMono? (f : SomeFunc) : Option ClosedFunc :=
  match f with
  | ⟨0, func⟩ => some func
  | _ => none

/-- Wrap a monomorphic function -/
def ofMono (f : ClosedFunc) : SomeFunc := ⟨0, f⟩

instance : ToString SomeFunc where
  toString f := ToString.toString f.2

end SomeFunc

/-! ## Globals -/

/-- A global constant or variable -/
structure Global where
  /-- Global ID -/
  id : GlobalId
  /-- Name -/
  name : String
  ty : ClosedTy
  init : Option Const := none
  /-- Whether this is mutable -/
  mutable : Bool := false
  deriving Inhabited

namespace Global

instance : ToString Global where
  toString g :=
    let mutStr := if g.mutable then "var" else "const"
    let initStr := match g.init with
      | some c => s!" = {c}"
      | none => ""
    s!"{mutStr} {g.id} {g.name}: {g.ty}{initStr}"

end Global

/-! ## Type Definitions -/

/-- A named type definition -/
structure TypeDef where
  /-- Type name -/
  name : String
  ty : ClosedTy
  deriving Inhabited

namespace TypeDef

instance : ToString TypeDef where
  toString td := s!"type {td.name} = {td.ty}"

end TypeDef

/-! ## String Table -/

/-- Interned string table -/
structure StringTable where
  /-- Strings by index -/
  strings : Array String := #[]
  /-- Index by string hash for deduplication -/
  index : Std.HashMap UInt64 Nat := {}
  deriving Inhabited

namespace StringTable

/-- Empty string table -/
def empty : StringTable := {}

/-- Intern a string, returning its index -/
def intern (st : StringTable) (s : String) : Nat × StringTable :=
  let hash := s.hash
  match st.index.get? hash with
  | some idx => (idx, st)
  | none =>
    let idx := st.strings.size
    (idx, { strings := st.strings.push s
          , index := st.index.insert hash idx })

/-- Get a string by index -/
def get (st : StringTable) (idx : Nat) : Option String :=
  st.strings[idx]?

end StringTable

/-- An Alloy module -/
structure Module where
  /-- Module name -/
  name : String
  funcs : Array SomeFunc := #[]
  globals : Array Global := #[]
  /-- Named type definitions -/
  types : Array TypeDef := #[]
  /-- String table -/
  strings : StringTable := {}
  /-- Function name to ID mapping -/
  funcIndex : Std.HashMap String FuncId := {}
  /-- Main function ID (if any) -/
  mainFunc : Option FuncId := none
  /-- Wired-in function roles → FuncIds. Maps each known role to all FuncIds -/
  wiredFuncIds : Std.HashMap WiredFunc (Array FuncId) := {}
  /-- Canonical Alloy layout for the wired-in `type.string` record -/
  stringTy : ClosedTy := .struct #[("data", .rawPtr), ("len", .prim .i64)]
  deriving Inhabited

namespace Module

/-- Create an empty module -/
def empty (name : String) : Module := { name }

/-- Add a function -/
def addFunc (m : Module) (f : SomeFunc) : Module :=
  let wired := match f.2.attrs.wiredRole with
    | some role =>
      let existing := m.wiredFuncIds.getD role #[]
      m.wiredFuncIds.insert role (existing.push f.id)
    | none => m.wiredFuncIds
  { m with
    funcs := m.funcs.push f
    funcIndex := m.funcIndex.insert f.name f.id
    wiredFuncIds := wired
  }

/-- Add a monomorphic function -/
def addMonoFunc (m : Module) (f : ClosedFunc) : Module :=
  m.addFunc (SomeFunc.ofMono f)

def addGlobal (m : Module) (g : Global) : Module :=
  let id := GlobalId.mk m.globals.size
  { m with globals := m.globals.push { g with id } }

/-- Add a type definition -/
def addType (m : Module) (td : TypeDef) : Module :=
  { m with types := m.types.push td }

/-- Intern a string -/
def internString (m : Module) (s : String) : Nat × Module :=
  let (idx, strings') := m.strings.intern s
  (idx, { m with strings := strings' })

/-- Get function by ID -/
def getFunc (m : Module) (id : FuncId) : Option SomeFunc :=
  m.funcs[id.id]?

/-- Get function by name -/
def getFuncByName (m : Module) (name : String) : Option SomeFunc :=
  m.funcIndex.get? name |>.bind m.getFunc

/-- Get monomorphic function by ID -/
def getMonoFunc (m : Module) (id : FuncId) : Option ClosedFunc :=
  m.getFunc id |>.bind SomeFunc.asMono?

def getGlobal (m : Module) (id : GlobalId) : Option Global :=
  m.globals[id.id]?

/-- Set the main function -/
def withMain (m : Module) (id : FuncId) : Module :=
  { m with mainFunc := some id }

/-- Set main by name -/
def withMainByName (m : Module) (name : String) : Module :=
  match m.funcIndex.get? name with
  | some id => { m with mainFunc := some id }
  | none => m

/-- Get all monomorphic functions -/
def monoFuncs (m : Module) : Array ClosedFunc :=
  m.funcs.filterMap SomeFunc.asMono?

/-- Check if module is fully monomorphic -/
def isFullyMonomorphic (m : Module) : Bool :=
  m.funcs.all (·.isMono)

/-- Rebuild the wired function index from FuncAttrs.wiredRole on all functions -/
def rebuildWiredFuncIndex (m : Module) : Module :=
  let idx := m.funcs.foldl (init := ({} : Std.HashMap WiredFunc (Array FuncId))) fun acc sf =>
    match sf.2.attrs.wiredRole with
    | some role => acc.insert role ((acc.getD role #[]).push sf.id)
    | none => acc
  { m with wiredFuncIds := idx }

instance : ToString Module where
  toString m :=
    let header := s!"; Alloy IR Module: {m.name}\n"

    let typesStr := if m.types.isEmpty then ""
      else
        let ts := String.intercalate "\n" (m.types.toList.map ToString.toString)
        s!"; Types\n{ts}\n\n"

    let globalsStr := if m.globals.isEmpty then ""
      else
        let gs := String.intercalate "\n" (m.globals.toList.map ToString.toString)
        s!"; Globals\n{gs}\n\n"

    let funcsStr := String.intercalate "\n\n" (m.funcs.toList.map ToString.toString)

    let mainStr := match m.mainFunc with
      | some id => s!"\n; main = {id}"
      | none => ""

    s!"{header}{typesStr}{globalsStr}; Functions\n{funcsStr}{mainStr}"

end Module

/-- A type-safe specialization request for a function of arity n -/
structure SpecRequest (n : Nat) where
  func : Func n
  typeArgs : Fin n → ClosedTy

namespace SpecRequest

/-- Build a type environment from the request -/
def toEnv (req : SpecRequest n) : TyEnv n := req.typeArgs

/-- Specialize the function -/
def specialize (req : SpecRequest n) (newId : FuncId) (newName : String) : ClosedFunc :=
  req.func.instantiate req.toEnv newId newName

end SpecRequest

/-- Existentially quantified specialization request -/
abbrev SomeSpecRequest := Σ n, SpecRequest n

end Somac.Alloy
