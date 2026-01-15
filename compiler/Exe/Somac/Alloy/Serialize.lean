import Somac.Alloy.Func
import Kenosis

namespace Somac.Alloy.Serialize

open Kenosis

/-- Serializable version of StringTable (converts HashMap to Array) -/
structure SerializableStringTable where
  strings : Array String
  deriving Serialize, Deserialize

/-- Serializable version of CFG -/
structure SerializableCFG where
  blocks : Array (Nat × Block)
  entry : BlockId
  nextBlockId : Nat
  deriving Serialize, Deserialize

/-- Serializable version of Func -/
structure SerializableFunc where
  id : FuncId
  sig : Signature
  body : Option SerializableCFG
  attrs : FuncAttrs
  nextLocalId : Nat
  localTypes : Array (Nat × Ty)
  specializedFrom : Option FuncId
  typeArgs : Array Ty
  deriving Serialize, Deserialize

/-- Serializable version of Module -/
structure SerializableModule where
  name : String
  funcs : Array SerializableFunc
  globals : Array Global
  types : Array TypeDef
  strings : SerializableStringTable
  funcIndex : Array (String × FuncId)
  mainFunc : Option FuncId
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

namespace CFG

def toSerializable (cfg : CFG) : SerializableCFG :=
  { blocks := cfg.blocks.toArray
  , entry := cfg.entry
  , nextBlockId := cfg.nextBlockId
  }

def fromSerializable (scfg : SerializableCFG) : CFG :=
  { blocks := Std.HashMap.ofList scfg.blocks.toList
  , entry := scfg.entry
  , nextBlockId := scfg.nextBlockId
  }

end CFG

namespace Func

def toSerializable (f : Func) : SerializableFunc :=
  { id := f.id
  , sig := f.sig
  , body := f.body.map CFG.toSerializable
  , attrs := f.attrs
  , nextLocalId := f.nextLocalId
  , localTypes := f.localTypes.toArray
  , specializedFrom := f.specializedFrom
  , typeArgs := f.typeArgs
  }

def fromSerializable (sf : SerializableFunc) : Func :=
  { id := sf.id
  , sig := sf.sig
  , body := sf.body.map CFG.fromSerializable
  , attrs := sf.attrs
  , nextLocalId := sf.nextLocalId
  , localTypes := Std.HashMap.ofList sf.localTypes.toList
  , specializedFrom := sf.specializedFrom
  , typeArgs := sf.typeArgs
  }

end Func

namespace Module

def toSerializable (m : Module) : SerializableModule :=
  { name := m.name
  , funcs := m.funcs.map Func.toSerializable
  , globals := m.globals
  , types := m.types
  , strings := StringTable.toSerializable m.strings
  , funcIndex := m.funcIndex.toArray
  , mainFunc := m.mainFunc
  }

def fromSerializable (sm : SerializableModule) : Module :=
  { name := sm.name
  , funcs := sm.funcs.map Func.fromSerializable
  , globals := sm.globals
  , types := sm.types
  , strings := StringTable.fromSerializable sm.strings
  , funcIndex := Std.HashMap.ofList sm.funcIndex.toList
  , mainFunc := sm.mainFunc
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
