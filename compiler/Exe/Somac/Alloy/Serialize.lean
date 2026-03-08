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
  | tyvar (idx : Nat)
  deriving Serialize, Deserialize

/-- Convert Ty n to SerializableTy -/
partial def tyToSerializable : Ty n → SerializableTy
  | .prim p => .prim p
  | .ptr t => .ptr (tyToSerializable t)
  | .rawPtr => .rawPtr
  | .funcPtr args ret => .funcPtr (args.map tyToSerializable) (tyToSerializable ret)
  | .struct fields => .struct_ (fields.map fun (n, t) => (n, tyToSerializable t))
  | .array elem size => .array_ (tyToSerializable elem) size
  | .tagged tag variants => .tagged (tyToSerializable tag)
      (variants.map fun (i, ts) => (i, ts.map tyToSerializable))
  | .closure args ret => .closure (args.map tyToSerializable) (tyToSerializable ret)
  | .var i => .tyvar i.val

/-- Convert SerializableTy back to Ty n -/
partial def tyFromSerializableN (n : Nat) : SerializableTy → Ty n
  | .prim p => .prim p
  | .ptr t => .ptr (tyFromSerializableN n t)
  | .rawPtr => .rawPtr
  | .funcPtr args ret => .funcPtr (args.map (tyFromSerializableN n)) (tyFromSerializableN n ret)
  | .struct_ fields => .struct (fields.map fun (name, t) => (name, tyFromSerializableN n t))
  | .array_ elem size => .array (tyFromSerializableN n elem) size
  | .tagged tag variants => .tagged (tyFromSerializableN n tag)
      (variants.map fun (i, ts) => (i, ts.map (tyFromSerializableN n)))
  | .closure args ret => .closure (args.map (tyFromSerializableN n)) (tyFromSerializableN n ret)
  | .tyvar idx =>
      if h : idx < n then .var ⟨idx, h⟩
      else .rawPtr

/-- Convert SerializableTy to ClosedTy -/
def tyFromSerializable : SerializableTy → ClosedTy := tyFromSerializableN 0

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

/-- Serializable Operand -/
inductive SerializableOperand where
  | local_ (id : Nat)
  | const_ (c : SerializableConst)
  | global_ (id : Nat)
  | func_ (id : Nat)
  deriving Serialize, Deserialize

def operandToSerializable : Operand → SerializableOperand
  | .local id => .local_ id.id
  | .const c => .const_ (constToSerializable c)
  | .global id => .global_ id.id
  | .func id => .func_ id.id

def operandFromSerializable : SerializableOperand → Operand
  | .local_ id => .local ⟨id⟩
  | .const_ c => .const (constFromSerializable c)
  | .global_ id => .global ⟨id⟩
  | .func_ id => .func ⟨id⟩

/-- Serializable BinOp -/
-- BinOp already derives Serialize, so we use it directly via a Nat tag
def binOpToNat : BinOp → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .rem => 4
  | .and => 5 | .or => 6 | .xor => 7 | .shl => 8 | .shr => 9
  | .eq => 10 | .ne => 11 | .lt => 12 | .le => 13 | .gt => 14 | .ge => 15

def natToBinOp : Nat → BinOp
  | 0 => .add | 1 => .sub | 2 => .mul | 3 => .div | 4 => .rem
  | 5 => .and | 6 => .or | 7 => .xor | 8 => .shl | 9 => .shr
  | 10 => .eq | 11 => .ne | 12 => .lt | 13 => .le | 14 => .gt | 15 => .ge
  | _ => .add

/-- Serializable UnOp -/
inductive SerializableUnOp where
  | neg | not
  | trunc (to : PrimTy) | zext (to : PrimTy) | sext (to : PrimTy)
  | itof (to : PrimTy) | ftoi (to : PrimTy)
  | bitcast (to : SerializableTy)
  | ptrtoint (to : PrimTy) | inttoptr
  deriving Serialize, Deserialize

def unOpToSerializable : UnOp n → SerializableUnOp
  | .neg => .neg | .not => .not
  | .trunc t => .trunc t | .zext t => .zext t | .sext t => .sext t
  | .itof t => .itof t | .ftoi t => .ftoi t
  | .bitcast t => .bitcast (tyToSerializable t)
  | .ptrtoint t => .ptrtoint t | .inttoptr => .inttoptr

def unOpFromSerializableN (n : Nat) : SerializableUnOp → UnOp n
  | .neg => .neg | .not => .not
  | .trunc t => .trunc t | .zext t => .zext t | .sext t => .sext t
  | .itof t => .itof t | .ftoi t => .ftoi t
  | .bitcast t => .bitcast (tyFromSerializableN n t)
  | .ptrtoint t => .ptrtoint t | .inttoptr => .inttoptr

/-- Serializable FuncRef -/
inductive SerializableFuncRef where
  | local_ (id : Nat)
  | external (name : String)
  | intrinsic (op : IntrinsicOp)
  | primOp (op : PrimOp)
  | externC (name : String)
  deriving Serialize, Deserialize

def funcRefToSerializable : FuncRef → SerializableFuncRef
  | .local id => .local_ id.id
  | .external name => .external name
  | .intrinsic op => .intrinsic op
  | .primOp op => .primOp op
  | .externC name => .externC name

def funcRefFromSerializable : SerializableFuncRef → FuncRef
  | .local_ id => .local ⟨id⟩
  | .external name => .external name
  | .intrinsic op => .intrinsic op
  | .primOp op => .primOp op
  | .externC name => .externC name

/-! ## Instruction Serialization -/

/-- Serializable instruction — mirrors every constructor of `Inst n`.
    Each constructor is assigned a numeric tag for stable binary encoding. -/
inductive SerializableInst where
  | binOp (op : Nat) (lhs rhs : SerializableOperand) (ty : SerializableTy)
  | unOp (op : SerializableUnOp) (operand : SerializableOperand)
  | copy (src : SerializableOperand)
  | alloca (ty : SerializableTy)
  | malloc (size : SerializableOperand)
  | free (ptr : SerializableOperand)
  | load (ptr : SerializableOperand) (ty : SerializableTy)
  | store (ptr val : SerializableOperand)
  | getFieldPtr (base : SerializableOperand) (idx : Nat) (ty : SerializableTy)
  | getElemPtr (base idx : SerializableOperand) (ty : SerializableTy)
  | extractField (val : SerializableOperand) (idx : Nat)
  | insertField (val : SerializableOperand) (idx : Nat) (newVal : SerializableOperand)
  | extractElem (val idx : SerializableOperand)
  | insertElem (val idx newVal : SerializableOperand)
  | structLit (fields : Array SerializableOperand) (ty : SerializableTy)
  | arrayLit (elems : Array SerializableOperand) (ty : SerializableTy)
  | getTag (val : SerializableOperand)
  | getPayload (val : SerializableOperand) (variant field : Nat) (ty : SerializableTy)
  | taggedLit (tag : Nat) (payload : Array SerializableOperand) (ty : SerializableTy)
  | call (funcId : Nat) (args : Array SerializableOperand) (retTy : SerializableTy)
  | callPoly (funcId : Nat) (tyArgs : Array SerializableTy) (args : Array SerializableOperand)
      (retTy : SerializableTy)
  | callIndirect (ptr : SerializableOperand) (args : Array SerializableOperand) (retTy : SerializableTy)
  | callClosure (closure : SerializableOperand) (args : Array SerializableOperand)
      (retTy : SerializableTy)
  | makeClosurePoly (funcRef : SerializableFuncRef) (tyArgs : Array SerializableTy)
      (env : SerializableOperand)
  | makeClosure (funcRef : SerializableFuncRef) (env : SerializableOperand)
  | makeClosureDyn (fnClosure env : SerializableOperand) (ty : SerializableTy)
  | closureFunc (closure : SerializableOperand)
  | closureEnv (closure : SerializableOperand)
  | phi (incoming : Array (SerializableOperand × Nat)) (ty : SerializableTy)
  | select (cond thenVal elseVal : SerializableOperand)
  | memcpy (dst src size : SerializableOperand)
  | memset (dst val size : SerializableOperand)
  | lazySup (label : Nat) (src : SerializableOperand) (ty : SerializableTy)
  | supProj0 (src : SerializableOperand) (ty : SerializableTy)
  | supProj1 (src : SerializableOperand) (ty : SerializableTy)
  | erase (val : SerializableOperand) (ty : SerializableTy)
  | panic (msgIdx line : Nat)
  | callIntrinsic (op : IntrinsicOp) (args : Array SerializableOperand) (retTy : SerializableTy)
  | callExtern (name : String) (args : Array SerializableOperand) (retTy : SerializableTy)
  deriving Serialize, Deserialize

private abbrev SOp := SerializableOperand
private abbrev STy := SerializableTy
private def sop := operandToSerializable
private def sty : Ty n → STy := tyToSerializable
private def sops (ops : Array Operand) : Array SOp := ops.map sop
private def stys (tys : Array (Ty n)) : Array STy := tys.map tyToSerializable

def instToSerializable : Inst n → SerializableInst
  | .binOp op l r ty => .binOp (binOpToNat op) (sop l) (sop r) (sty ty)
  | .unOp op o => .unOp (unOpToSerializable op) (sop o)
  | .copy s => .copy (sop s)
  | .alloca ty => .alloca (sty ty)
  | .malloc s => .malloc (sop s)
  | .free p => .free (sop p)
  | .load p ty => .load (sop p) (sty ty)
  | .store p v => .store (sop p) (sop v)
  | .getFieldPtr b i ty => .getFieldPtr (sop b) i (sty ty)
  | .getElemPtr b i ty => .getElemPtr (sop b) (sop i) (sty ty)
  | .extractField v i => .extractField (sop v) i
  | .insertField v i nv => .insertField (sop v) i (sop nv)
  | .extractElem v i => .extractElem (sop v) (sop i)
  | .insertElem v i nv => .insertElem (sop v) (sop i) (sop nv)
  | .structLit fs ty => .structLit (sops fs) (sty ty)
  | .arrayLit es ty => .arrayLit (sops es) (sty ty)
  | .getTag v => .getTag (sop v)
  | .getPayload v var fld ty => .getPayload (sop v) var fld (sty ty)
  | .taggedLit t p ty => .taggedLit t (sops p) (sty ty)
  | .call f as ty => .call f.id (sops as) (sty ty)
  | .callPoly f ta as ty => .callPoly f.id (stys ta) (sops as) (sty ty)
  | .callIndirect p as ty => .callIndirect (sop p) (sops as) (sty ty)
  | .callClosure c as ty => .callClosure (sop c) (sops as) (sty ty)
  | .makeClosurePoly fr ta e => .makeClosurePoly (funcRefToSerializable fr) (stys ta) (sop e)
  | .makeClosure fr e => .makeClosure (funcRefToSerializable fr) (sop e)
  | .makeClosureDyn fn e ty => .makeClosureDyn (sop fn) (sop e) (sty ty)
  | .closureFunc c => .closureFunc (sop c)
  | .closureEnv c => .closureEnv (sop c)
  | .phi inc ty => .phi (inc.map fun (o, b) => (sop o, b.id)) (sty ty)
  | .select c t e => .select (sop c) (sop t) (sop e)
  | .memcpy d s sz => .memcpy (sop d) (sop s) (sop sz)
  | .memset d v sz => .memset (sop d) (sop v) (sop sz)
  | .lazySup l s ty => .lazySup l.toNat (sop s) (sty ty)
  | .supProj0 s ty => .supProj0 (sop s) (sty ty)
  | .supProj1 s ty => .supProj1 (sop s) (sty ty)
  | .erase v ty => .erase (sop v) (sty ty)
  | .panic m l => .panic m l
  | .callIntrinsic op as ty => .callIntrinsic op (sops as) (sty ty)
  | .callExtern name as ty => .callExtern name (sops as) (sty ty)

private abbrev dop := operandFromSerializable
private def dty (n : Nat) := tyFromSerializableN n
private def dops (ops : Array SOp) : Array Operand := ops.map dop
private def dtys (n : Nat) (tys : Array STy) : Array (Ty n) := tys.map (tyFromSerializableN n)

def instFromSerializableN (n : Nat) : SerializableInst → Inst n
  | .binOp op l r ty => .binOp (natToBinOp op) (dop l) (dop r) (dty n ty)
  | .unOp op o => .unOp (unOpFromSerializableN n op) (dop o)
  | .copy s => .copy (dop s)
  | .alloca ty => .alloca (dty n ty)
  | .malloc s => .malloc (dop s)
  | .free p => .free (dop p)
  | .load p ty => .load (dop p) (dty n ty)
  | .store p v => .store (dop p) (dop v)
  | .getFieldPtr b i ty => .getFieldPtr (dop b) i (dty n ty)
  | .getElemPtr b i ty => .getElemPtr (dop b) (dop i) (dty n ty)
  | .extractField v i => .extractField (dop v) i
  | .insertField v i nv => .insertField (dop v) i (dop nv)
  | .extractElem v i => .extractElem (dop v) (dop i)
  | .insertElem v i nv => .insertElem (dop v) (dop i) (dop nv)
  | .structLit fs ty => .structLit (dops fs) (dty n ty)
  | .arrayLit es ty => .arrayLit (dops es) (dty n ty)
  | .getTag v => .getTag (dop v)
  | .getPayload v var fld ty => .getPayload (dop v) var fld (dty n ty)
  | .taggedLit t p ty => .taggedLit t (dops p) (dty n ty)
  | .call f as ty => .call ⟨f⟩ (dops as) (dty n ty)
  | .callPoly f ta as ty => .callPoly ⟨f⟩ (dtys n ta) (dops as) (dty n ty)
  | .callIndirect p as ty => .callIndirect (dop p) (dops as) (dty n ty)
  | .callClosure c as ty => .callClosure (dop c) (dops as) (dty n ty)
  | .makeClosurePoly fr ta e => .makeClosurePoly (funcRefFromSerializable fr) (dtys n ta) (dop e)
  | .makeClosure fr e => .makeClosure (funcRefFromSerializable fr) (dop e)
  | .makeClosureDyn fn e ty => .makeClosureDyn (dop fn) (dop e) (dty n ty)
  | .closureFunc c => .closureFunc (dop c)
  | .closureEnv c => .closureEnv (dop c)
  | .phi inc ty => .phi (inc.map fun (o, b) => (dop o, ⟨b⟩)) (dty n ty)
  | .select c t e => .select (dop c) (dop t) (dop e)
  | .memcpy d s sz => .memcpy (dop d) (dop s) (dop sz)
  | .memset d v sz => .memset (dop d) (dop v) (dop sz)
  | .lazySup l s ty => .lazySup (UInt32.ofNat l) (dop s) (dty n ty)
  | .supProj0 s ty => .supProj0 (dop s) (dty n ty)
  | .supProj1 s ty => .supProj1 (dop s) (dty n ty)
  | .erase v ty => .erase (dop v) (dty n ty)
  | .panic m l => .panic m l
  | .callIntrinsic op as ty => .callIntrinsic op (dops as) (dty n ty)
  | .callExtern name as ty => .callExtern name (dops as) (dty n ty)

/-! ## Terminator Serialization -/

/-- Serializable Terminator -/
inductive SerializableTerminator where
  | jump (target : Nat)
  | branch (cond : SerializableOperand) (thenBlock elseBlock : Nat)
  | switch (val : SerializableOperand) (cases : Array (Int × Nat)) (default : Nat)
  | ret (val : SerializableOperand)
  | retUnit
  | unreachable
  deriving Serialize, Deserialize

def terminatorToSerializable : Terminator → SerializableTerminator
  | .jump t => .jump t.id
  | .branch c t e => .branch (sop c) t.id e.id
  | .switch v cs d => .switch (sop v) (cs.map fun (i, b) => (i, b.id)) d.id
  | .ret v => .ret (sop v)
  | .retUnit => .retUnit
  | .unreachable => .unreachable

def terminatorFromSerializable : SerializableTerminator → Terminator
  | .jump t => .jump ⟨t⟩
  | .branch c t e => .branch (dop c) ⟨t⟩ ⟨e⟩
  | .switch v cs d => .switch (dop v) (cs.map fun (i, b) => (i, ⟨b⟩)) ⟨d⟩
  | .ret v => .ret (dop v)
  | .retUnit => .retUnit
  | .unreachable => .unreachable

/-! ## Statement Serialization -/

structure SerializableStmt where
  result : Option Nat
  inst : SerializableInst
  deriving Serialize, Deserialize

def stmtToSerializable (s : Stmt n) : SerializableStmt :=
  { result := s.result.map (·.id), inst := instToSerializable s.inst }

def stmtFromSerializableN (n : Nat) (ss : SerializableStmt) : Stmt n :=
  { result := ss.result.map (⟨·⟩), inst := instFromSerializableN n ss.inst }

/-! ## Block Serialization -/

structure SerializableBlock where
  id : Nat
  label : Option String
  params : Array (Nat × SerializableTy)
  stmts : Array SerializableStmt
  terminator : SerializableTerminator
  deriving Serialize, Deserialize

def blockToSerializable (b : Block n) : SerializableBlock :=
  { id := b.id.id
  , label := b.label
  , params := b.params.map fun (lid, ty) => (lid.id, tyToSerializable ty)
  , stmts := b.stmts.map stmtToSerializable
  , terminator := terminatorToSerializable b.terminator
  }

def blockFromSerializableN (n : Nat) (sb : SerializableBlock) : Block n :=
  { id := ⟨sb.id⟩
  , label := sb.label
  , params := sb.params.map fun (lid, ty) => (⟨lid⟩, tyFromSerializableN n ty)
  , stmts := sb.stmts.map (stmtFromSerializableN n)
  , terminator := terminatorFromSerializable sb.terminator
  }

/-! ## CFG Serialization -/

structure SerializableCFG where
  /-- Blocks stored as array of (blockId, block) pairs (HashMap is not directly serializable) -/
  blocks : Array SerializableBlock
  entry : Nat
  nextBlockId : Nat
  deriving Serialize, Deserialize

def cfgToSerializable (cfg : CFG n) : SerializableCFG :=
  { blocks := cfg.allBlocks.map blockToSerializable
  , entry := cfg.entry.id
  , nextBlockId := cfg.nextBlockId
  }

def cfgFromSerializableN (n : Nat) (sc : SerializableCFG) : CFG n :=
  let blocks := sc.blocks.foldl (init := ({} : Std.HashMap Nat (Block n))) fun acc sb =>
    let block := blockFromSerializableN n sb
    acc.insert block.id.id block
  { blocks, entry := ⟨sc.entry⟩, nextBlockId := sc.nextBlockId }

/-! ## Param, Signature, Func Serialization -/

/-- Serializable Param -/
structure SerializableParam where
  id : Nat
  name : String
  ty : SerializableTy
  deriving Serialize, Deserialize

def paramToSerializable (p : Param n) : SerializableParam :=
  { id := p.id.id, name := p.name, ty := tyToSerializable p.ty }

def paramFromSerializableN (n : Nat) (sp : SerializableParam) : Param n :=
  { id := ⟨sp.id⟩, name := sp.name, ty := tyFromSerializableN n sp.ty }

/-- Serializable Signature -/
structure SerializableSignature where
  name : String
  typeParamNames : Array String := #[]
  params : Array SerializableParam
  retTy : SerializableTy
  isClosure : Bool
  deriving Serialize, Deserialize

def sigToSerializable (sig : Signature n) : SerializableSignature :=
  { name := sig.name
  , typeParamNames := sig.typeParamNames
  , params := sig.params.map paramToSerializable
  , retTy := tyToSerializable sig.retTy
  , isClosure := sig.isClosure
  }

def sigFromSerializableN (n : Nat) (ss : SerializableSignature) : Signature n :=
  { name := ss.name
  , typeParamNames := ss.typeParamNames
  , params := ss.params.map (paramFromSerializableN n)
  , retTy := tyFromSerializableN n ss.retTy
  , isClosure := ss.isClosure
  }

/-- Serializable Func with full body support -/
structure SerializableFunc where
  id : Nat
  typeArity : Nat
  sig : SerializableSignature
  body : Option SerializableCFG
  attrs : FuncAttrs
  nextLocalId : Nat
  localTypes : Array (Nat × SerializableTy)
  deriving Serialize, Deserialize

/-- Serialize a function of any type arity -/
def someFuncToSerializable (sf : SomeFunc) : SerializableFunc :=
  let ⟨n, f⟩ := sf
  { id := f.id.id
  , typeArity := n
  , sig := sigToSerializable f.sig
  , body := f.body.map cfgToSerializable
  , attrs := f.attrs
  , nextLocalId := f.nextLocalId
  , localTypes := f.localTypes.toArray.map fun (k, v) => (k, tyToSerializable v)
  }

/-- Deserialize a function, reconstructing the correct type arity -/
def someFuncFromSerializable (sf : SerializableFunc) : SomeFunc :=
  let n := sf.typeArity
  let func : Func n :=
    { id := ⟨sf.id⟩
    , sig := sigFromSerializableN n sf.sig
    , body := sf.body.map (cfgFromSerializableN n)
    , attrs := sf.attrs
    , nextLocalId := sf.nextLocalId
    , localTypes := Std.HashMap.ofList (sf.localTypes.toList.map fun (k, v) =>
        (k, tyFromSerializableN n v))
    }
  ⟨n, func⟩

/-! ## Global, TypeDef, Module Serialization -/

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
  { name := m.name
  , funcs := m.funcs.map someFuncToSerializable
  , globals := m.globals.map globalToSerializable
  , types := m.types.map typeDefToSerializable
  , strings := StringTable.toSerializable m.strings
  , funcIndex := m.funcIndex.toArray.map fun (k, v) => (k, v.id)
  , mainFunc := m.mainFunc.map (·.id)
  }

def fromSerializable (sm : SerializableModule) : Module :=
  { name := sm.name
  , funcs := sm.funcs.map someFuncFromSerializable
  , globals := sm.globals.map globalFromSerializable
  , types := sm.types.map typeDefFromSerializable
  , strings := StringTable.fromSerializable sm.strings
  , funcIndex := Std.HashMap.ofList (sm.funcIndex.toList.map fun (k, v) => (k, ⟨v⟩))
  , mainFunc := sm.mainFunc.map (⟨·⟩)
  }

end Module

/-- Magic bytes for .alloybin files -/
def magicBytes : ByteArray := ByteArray.mk #[0x41, 0x4C, 0x4F, 0x59]

/-- Version of the serialization format — bumped to 3 for polymorphic function support -/
def formatVersion : UInt8 := 3

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
