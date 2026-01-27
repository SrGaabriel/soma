import Somac.Alloy.Func
import Kenosis

namespace Somac.Alloy.Serialize

open Kenosis

/-- Serializable version of StringTable (converts HashMap to Array) -/
structure SerializableStringTable where
  strings : Array String
  deriving Serialize, Deserialize

/-- Serializable Ty -/
inductive SerializableTy where
  | prim (p : PrimTy)
  | ptr (t : SerializableTy)
  | rawPtr
  | funcPtr (args : Array SerializableTy) (ret : SerializableTy)
  | struct_ (fields : Array (String × SerializableTy))
  | array_ (elem : SerializableTy) (size : Nat)
  | tagged (tag : SerializableTy) (variants : Array (Nat × Array SerializableTy))
  | closure (args : Array SerializableTy) (ret : SerializableTy)
  deriving Serialize, Deserialize

/-- Convert ClosedTy to SerializableTy -/
partial def tyToSerializable : ClosedTy → SerializableTy
  | .prim p => .prim p
  | .ptr t => .ptr (tyToSerializable t)
  | .rawPtr => .rawPtr
  | .funcPtr args ret => .funcPtr (args.map tyToSerializable) (tyToSerializable ret)
  | .struct fields => .struct_ (fields.map fun (n, t) => (n, tyToSerializable t))
  | .array elem size => .array_ (tyToSerializable elem) size
  | .tagged tag variants => .tagged (tyToSerializable tag)
      (variants.map fun (i, ts) => (i, ts.map tyToSerializable))
  | .closure args ret => .closure (args.map tyToSerializable) (tyToSerializable ret)
  | .var i => nomatch i

/-- Convert SerializableTy back to ClosedTy -/
partial def tyFromSerializable : SerializableTy → ClosedTy
  | .prim p => .prim p
  | .ptr t => .ptr (tyFromSerializable t)
  | .rawPtr => .rawPtr
  | .funcPtr args ret => .funcPtr (args.map tyFromSerializable) (tyFromSerializable ret)
  | .struct_ fields => .struct (fields.map fun (n, t) => (n, tyFromSerializable t))
  | .array_ elem size => .array (tyFromSerializable elem) size
  | .tagged tag variants => .tagged (tyFromSerializable tag)
      (variants.map fun (i, ts) => (i, ts.map tyFromSerializable))
  | .closure args ret => .closure (args.map tyFromSerializable) (tyFromSerializable ret)

/-- Serializable Const using simple tagged format -/
inductive SerializableConst where
  | int (v : Int) (t : PrimTy)
  | float (v : Float) (t : PrimTy)
  | bool (b : Bool)
  | unit
  | null (t : SerializableTy)
  | string (idx : Nat) (len : Nat)
  | undef (t : SerializableTy)
  deriving Serialize, Deserialize

def constToSerializable : Const → SerializableConst
  | .int v t => .int v t
  | .float v t => .float v t
  | .bool b => .bool b
  | .unit => .unit
  | .null t => .null (tyToSerializable t)
  | .string idx len => .string idx len
  | .undef t => .undef (tyToSerializable t)

def constFromSerializable : SerializableConst → Const
  | .int v t => .int v t
  | .float v t => .float v t
  | .bool b => .bool b
  | .unit => .unit
  | .null t => .null (tyFromSerializable t)
  | .string idx len => .string idx len
  | .undef t => .undef (tyFromSerializable t)

/-- Serializable Param -/
structure SerializableParam where
  id : Nat
  name : String
  ty : SerializableTy
  deriving Serialize, Deserialize

def paramToSerializable (p : ClosedParam) : SerializableParam :=
  { id := p.id.id, name := p.name, ty := tyToSerializable p.ty }

def paramFromSerializable (sp : SerializableParam) : ClosedParam :=
  { id := ⟨sp.id⟩, name := sp.name, ty := tyFromSerializable sp.ty }

/-- Serializable Signature -/
structure SerializableSignature where
  name : String
  params : Array SerializableParam
  retTy : SerializableTy
  isClosure : Bool
  deriving Serialize, Deserialize

def sigToSerializable (sig : ClosedSignature) : SerializableSignature :=
  { name := sig.name
  , params := sig.params.map paramToSerializable
  , retTy := tyToSerializable sig.retTy
  , isClosure := sig.isClosure
  }

def sigFromSerializable (ss : SerializableSignature) : ClosedSignature :=
  { name := ss.name
  , params := ss.params.map paramFromSerializable
  , retTy := tyFromSerializable ss.retTy
  , isClosure := ss.isClosure
  }

/-- Serializable Func (without body for simplicity) -/
structure SerializableFunc where
  id : Nat
  sig : SerializableSignature
  hasBody : Bool
  attrs : FuncAttrs
  nextLocalId : Nat
  localTypes : Array (Nat × SerializableTy)
  deriving Serialize, Deserialize

def funcToSerializable (f : ClosedFunc) : SerializableFunc :=
  { id := f.id.id
  , sig := sigToSerializable f.sig
  , hasBody := f.body.isSome
  , attrs := f.attrs
  , nextLocalId := f.nextLocalId
  , localTypes := f.localTypes.toArray.map fun (k, v) => (k, tyToSerializable v)
  }

def funcFromSerializable (sf : SerializableFunc) : ClosedFunc :=
  { id := ⟨sf.id⟩
  , sig := sigFromSerializable sf.sig
  , body := none  -- Body serialization is complex, skip for now
  , attrs := sf.attrs
  , nextLocalId := sf.nextLocalId
  , localTypes := Std.HashMap.ofList (sf.localTypes.toList.map fun (k, v) => (k, tyFromSerializable v))
  }

/-- Serializable Global -/
structure SerializableGlobal where
  id : Nat
  name : String
  ty : SerializableTy
  init : Option SerializableConst
  mutable_ : Bool
  deriving Serialize, Deserialize

def globalToSerializable (g : Global) : SerializableGlobal :=
  { id := g.id.id
  , name := g.name
  , ty := tyToSerializable g.ty
  , init := g.init.map constToSerializable
  , mutable_ := g.mutable
  }

def globalFromSerializable (sg : SerializableGlobal) : Global :=
  { id := ⟨sg.id⟩
  , name := sg.name
  , ty := tyFromSerializable sg.ty
  , init := sg.init.map constFromSerializable
  , mutable := sg.mutable_
  }

/-- Serializable TypeDef -/
structure SerializableTypeDef where
  name : String
  ty : SerializableTy
  deriving Serialize, Deserialize

def typeDefToSerializable (td : TypeDef) : SerializableTypeDef :=
  { name := td.name, ty := tyToSerializable td.ty }

def typeDefFromSerializable (std : SerializableTypeDef) : TypeDef :=
  { name := std.name, ty := tyFromSerializable std.ty }

/-- Serializable version of Module -/
structure SerializableModule where
  name : String
  funcs : Array SerializableFunc
  globals : Array SerializableGlobal
  types : Array SerializableTypeDef
  strings : SerializableStringTable
  funcIndex : Array (String × Nat)
  mainFunc : Option Nat
  deriving Serialize, Deserialize

namespace StringTable

def toSerializable (st : StringTable) : SerializableStringTable :=
  { strings := st.strings }

def fromSerializable (sst : SerializableStringTable) : StringTable := Id.run do
  let mut st : StringTable := {}
  for s in sst.strings do
    let (_, st') := st.intern s
    st := st'
  return st

end StringTable

namespace Module

def toSerializable (m : Module) : SerializableModule :=
  -- Only serialize monomorphic functions
  let closedFuncs := m.monoFuncs
  { name := m.name
  , funcs := closedFuncs.map funcToSerializable
  , globals := m.globals.map globalToSerializable
  , types := m.types.map typeDefToSerializable
  , strings := StringTable.toSerializable m.strings
  , funcIndex := m.funcIndex.toArray.map fun (k, v) => (k, v.id)
  , mainFunc := m.mainFunc.map (·.id)
  }

def fromSerializable (sm : SerializableModule) : Module :=
  let closedFuncs := sm.funcs.map funcFromSerializable
  { name := sm.name
  , funcs := closedFuncs.map fun f => ⟨0, f⟩
  , globals := sm.globals.map globalFromSerializable
  , types := sm.types.map typeDefFromSerializable
  , strings := StringTable.fromSerializable sm.strings
  , funcIndex := Std.HashMap.ofList (sm.funcIndex.toList.map fun (k, v) => (k, ⟨v⟩))
  , mainFunc := sm.mainFunc.map (⟨·⟩)
  }

end Module

/-- Magic bytes for .alloybin files -/
def magicBytes : ByteArray := ByteArray.mk #[0x41, 0x4C, 0x4F, 0x59]

/-- Version of the serialization format -/
def formatVersion : UInt8 := 1

/-- Serialize an Alloy module to binary format -/
def serializeModule (m : Module) : ByteArray :=
  let sm := Module.toSerializable m
  let payload := Binary.encode sm
  -- Prepend magic bytes and version
  magicBytes ++ ByteArray.mk #[formatVersion] ++ payload

/-- Deserialize an Alloy module from binary format -/
def deserializeModule (bytes : ByteArray) : Except String Module := do
  -- Check minimum size
  if bytes.size < 5 then
    throw "Invalid .alloybin file: too small"

  -- Check magic bytes
  let magic := ByteArray.mk (bytes.toList.take 4).toArray
  if magic != magicBytes then
    throw "Invalid .alloybin file: bad magic bytes"

  -- Check version
  let version := bytes.get! 4
  if version != formatVersion then
    throw s!"Unsupported .alloybin version: {version} (expected {formatVersion})"

  -- Deserialize payload
  let payload := ByteArray.mk (bytes.toList.drop 5).toArray
  match Binary.decode payload with
  | .ok sm => .ok (Module.fromSerializable sm)
  | .error e => throw s!"Deserialization error: {e}"

/-- Write an Alloy module to a .alloybin file -/
def writeAlloyBin (path : System.FilePath) (m : Module) : IO Unit := do
  let bytes := serializeModule m
  IO.FS.writeBinFile path bytes

/-- Read an Alloy module from a .alloybin file -/
def readAlloyBin (path : System.FilePath) : IO (Except String Module) := do
  let bytes ← IO.FS.readBinFile path
  pure (deserializeModule bytes)

end Somac.Alloy.Serialize
