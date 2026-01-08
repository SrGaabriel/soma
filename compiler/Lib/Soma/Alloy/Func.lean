/-
  Alloy IR Functions and Module

  A function contains:
  - A signature (parameters and return type)
  - A control flow graph (basic blocks)
  - Local variable type information

  A module is a collection of functions, globals, and type definitions.
-/

import Soma.Alloy.Block

namespace Soma.Alloy

/-! ## Function Signatures -/

/-- Function parameter -/
structure Param where
  /-- Local ID for parameter (starts at %0, %1, ...) -/
  id : LocalId
  /-- Parameter name (for debugging) -/
  name : String
  /-- Parameter type -/
  ty : Ty
  deriving Repr, Inhabited

namespace Param

instance : ToString Param where
  toString p := s!"{p.id}: {p.ty}"

end Param

/-- Function signature -/
structure Signature where
  /-- Function name -/
  name : String
  /-- Parameters -/
  params : Array Param
  /-- Return type -/
  retTy : Ty
  /-- Is this a closure body (first param is env)? -/
  isClosure : Bool := false
  deriving Repr, Inhabited

namespace Signature

/-- Arity (number of parameters) -/
def arity (sig : Signature) : Nat := sig.params.size

/-- Get parameter types -/
def paramTypes (sig : Signature) : Array Ty := sig.params.map (·.ty)

/-- Convert to function type -/
def toFuncTy (sig : Signature) : Ty :=
  .funcPtr sig.paramTypes sig.retTy

instance : ToString Signature where
  toString sig :=
    let closureStr := if sig.isClosure then " [closure]" else ""
    let paramsStr := String.intercalate ", " (sig.params.toList.map ToString.toString)
    s!"fn {sig.name}({paramsStr}) -> {sig.retTy}{closureStr}"

end Signature

/-! ## Functions -/

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
  deriving Repr, BEq, Inhabited

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
    if attrs.isEmpty then "" else s!"[{String.intercalate ", " attrs}]"

end FuncAttrs

/-- A complete function -/
structure Func where
  /-- Function ID (index in module) -/
  id : FuncId
  /-- Function signature -/
  sig : Signature
  /-- Control flow graph (none for extern functions) -/
  body : Option CFG := none
  /-- Attributes -/
  attrs : FuncAttrs := {}
  /-- Next available local ID -/
  nextLocalId : Nat := 0
  /-- Local variable types (for SSA verification) -/
  localTypes : Std.HashMap Nat Ty := {}
  deriving Inhabited

namespace Func

/-- Create an external function declaration -/
def extern (id : FuncId) (name : String) (params : Array Param) (retTy : Ty)
    (externName : String) : Func :=
  { id
  , sig := { name, params, retTy }
  , body := none
  , attrs := { extern := some externName }
  , nextLocalId := params.size
  }

/-- Create a function with a body -/
def withBody (id : FuncId) (sig : Signature) (cfg : CFG) : Func :=
  { id
  , sig
  , body := some cfg
  , nextLocalId := sig.params.size
  }

/-- Check if function is external -/
def isExtern (f : Func) : Bool := f.attrs.extern.isSome

/-- Allocate a fresh local ID -/
def freshLocal (f : Func) : LocalId × Func :=
  (⟨f.nextLocalId⟩, { f with nextLocalId := f.nextLocalId + 1 })

/-- Allocate a fresh local with a known type -/
def freshLocalTyped (f : Func) (ty : Ty) : LocalId × Func :=
  let id := ⟨f.nextLocalId⟩
  (id, { f with
    nextLocalId := f.nextLocalId + 1
    localTypes := f.localTypes.insert id.id ty
  })

/-- Get the type of a local -/
def getLocalType (f : Func) (id : LocalId) : Option Ty :=
  f.localTypes.get? id.id

/-- Set the type of a local -/
def setLocalType (f : Func) (id : LocalId) (ty : Ty) : Func :=
  { f with localTypes := f.localTypes.insert id.id ty }

/-- Update the CFG -/
def updateBody (f : Func) (update : CFG → CFG) : Func :=
  match f.body with
  | some cfg => { f with body := some (update cfg) }
  | none => f

/-- Get all blocks -/
def blocks (f : Func) : Array Block :=
  match f.body with
  | some cfg => cfg.allBlocks
  | none => #[]

instance : ToString Func where
  toString f :=
    let attrsStr := if f.attrs == FuncAttrs.default then ""
      else s!"{f.attrs} "
    let header := s!"{attrsStr}{f.sig}"
    match f.body with
    | none => header
    | some cfg =>
      let bodyStr := String.intercalate "\n\n" (cfg.allBlocks.toList.map ToString.toString)
      s!"{header} \{\n{bodyStr}\n}"

end Func

/-! ## Globals -/

/-- A global constant or variable -/
structure Global where
  /-- Global ID -/
  id : GlobalId
  /-- Name -/
  name : String
  /-- Type -/
  ty : Ty
  /-- Initial value (none for uninitialized) -/
  init : Option Const := none
  /-- Is this mutable? -/
  mutable : Bool := false
  deriving Repr, Inhabited

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
  /-- The type -/
  ty : Ty
  deriving Repr, Inhabited

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

/-! ## Module -/

/-- An Alloy module -/
structure Module where
  /-- Module name -/
  name : String
  /-- Functions -/
  funcs : Array Func := #[]
  /-- Global variables and constants -/
  globals : Array Global := #[]
  /-- Named type definitions -/
  types : Array TypeDef := #[]
  /-- String table -/
  strings : StringTable := {}
  /-- Function name to ID mapping -/
  funcIndex : Std.HashMap String FuncId := {}
  /-- Main function ID (if any) -/
  mainFunc : Option FuncId := none
  deriving Inhabited

namespace Module

/-- Create an empty module -/
def empty (name : String) : Module := { name }

/-- Add a function -/
def addFunc (m : Module) (f : Func) : Module :=
  let id := FuncId.mk m.funcs.size
  let f' := { f with id }
  { m with
    funcs := m.funcs.push f'
    funcIndex := m.funcIndex.insert f.sig.name id
  }

/-- Add a global -/
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
def getFunc (m : Module) (id : FuncId) : Option Func :=
  m.funcs[id.id]?

/-- Get function by name -/
def getFuncByName (m : Module) (name : String) : Option Func :=
  m.funcIndex.get? name |>.bind m.getFunc

/-- Get global by ID -/
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

end Soma.Alloy
