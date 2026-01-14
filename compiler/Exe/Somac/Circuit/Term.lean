namespace Somac.Circuit.Term

/-- Number of bits for the substitution flag -/
def subBits : Nat := 1

/-- Number of bits for the tag field -/
def tagBits : Nat := 7

/-- Number of bits for the extended metadata field -/
def extBits : Nat := 24

/-- Number of bits for the value field -/
def valBits : Nat := 32

/-- Bit offset for the SUB field (most significant) -/
def subShift : Nat := 63

/-- Bit offset for the TAG field -/
def tagShift : Nat := 56

/-- Bit offset for the EXT field -/
def extShift : Nat := 32

/-- Bit offset for the VAL field (least significant) -/
def valShift : Nat := 0

/-- Mask for the SUB field (1 bit) -/
def subMask : UInt64 := 0x8000000000000000

/-- Mask for the TAG field (7 bits) -/
def tagMask : UInt64 := 0x7F00000000000000

/-- Mask for the EXT field (24 bits) -/
def extMask : UInt64 := 0x00FFFFFF00000000

/-- Mask for the VAL field (32 bits) -/
def valMask : UInt64 := 0x00000000FFFFFFFF

/-- Node type tag (7 bits, values 0-127) -/
inductive Tag where
  /-- Variable reference (linked or quoted) -/
  | var
  /-- Lambda abstraction -/
  | lam
  /-- Function application -/
  | app
  /-- Duplicator node (for cloning values) -/
  | dup
  /-- Superposition node (lazy duplication wrapper) -/
  | sup
  /-- Eraser node (for discarding values) -/
  | era
  /-- Constructor application -/
  | ctor
  /-- Pattern match (binary: hit/miss) -/
  | mat
  /-- Record value -/
  | record
  /-- Field projection -/
  | proj
  /-- Numeric literal -/
  | num
  /-- Unary primitive operation -/
  | op1
  /-- Binary primitive operation -/
  | op2
  /-- Global reference (book entry, static) -/
  | ref
  /-- Strict evaluation point (USE node) -/
  | use
  /-- Allocation node (lazy instantiation of REF) -/
  | alo
  /-- Heap-allocated array -/
  | array
  /-- Runtime array/string indexing -/
  | index
  /-- Heap-allocated string -/
  | string
  /-- Array/string slice (view without copying) -/
  | slice
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace Tag

/-- Convert tag to its numeric encoding (7 bits) -/
def toUInt8 : Tag → UInt8
  | .var    => 0
  | .lam    => 1
  | .app    => 2
  | .dup    => 3
  | .sup    => 4
  | .era    => 5
  | .ctor   => 6
  | .mat    => 7
  | .record => 8
  | .proj   => 9
  | .num    => 10
  | .op1    => 11
  | .op2    => 12
  | .ref    => 13
  | .use    => 14
  | .alo    => 15
  | .array  => 16
  | .index  => 17
  | .string => 18
  | .slice  => 19

/-- Convert numeric encoding back to tag -/
def fromUInt8 : UInt8 → Option Tag
  | 0  => some .var
  | 1  => some .lam
  | 2  => some .app
  | 3  => some .dup
  | 4  => some .sup
  | 5  => some .era
  | 6  => some .ctor
  | 7  => some .mat
  | 8  => some .record
  | 9  => some .proj
  | 10 => some .num
  | 11 => some .op1
  | 12 => some .op2
  | 13 => some .ref
  | 14 => some .use
  | 15 => some .alo
  | 16 => some .array
  | 17 => some .index
  | 18 => some .string
  | 19 => some .slice
  | _  => none

instance : ToString Tag where
  toString
    | .var    => "VAR"
    | .lam    => "LAM"
    | .app    => "APP"
    | .dup    => "DUP"
    | .sup    => "SUP"
    | .era    => "ERA"
    | .ctor   => "CTOR"
    | .mat    => "MAT"
    | .record => "REC"
    | .proj   => "PROJ"
    | .num    => "NUM"
    | .op1    => "OP1"
    | .op2    => "OP2"
    | .ref    => "REF"
    | .use    => "USE"
    | .alo    => "ALO"
    | .array  => "ARRAY"
    | .index  => "INDEX"
    | .string => "STRING"
    | .slice  => "SLICE"

end Tag

/-- A location in the heap (32-bit index) -/
structure Loc where
  val : UInt32
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace Loc

/-- The null/invalid location -/
def null : Loc := ⟨0⟩

/-- Check if a location is null -/
def isNull (l : Loc) : Bool := l.val == 0

/-- Create a location from a natural number -/
def ofNat (n : Nat) : Loc := ⟨n.toUInt32⟩

/-- Convert location to natural number -/
def toNat (l : Loc) : Nat := l.val.toNat

/-- Increment location by offset -/
def add (l : Loc) (offset : UInt32) : Loc := ⟨l.val + offset⟩

instance : ToString Loc where
  toString l := s!"@{l.val}"

end Loc

/-- Extended metadata (24 bits) -/
structure Ext where
  val : UInt32  -- Only lower 24 bits used
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace Ext

/-- Empty/zero extended metadata -/
def zero : Ext := ⟨0⟩

/-- Create from a natural number -/
def ofNat (n : Nat) : Ext := ⟨(n.toUInt32 &&& 0x00FFFFFF)⟩

/-- Convert to natural number -/
def toNat (e : Ext) : Nat := e.val.toNat

/-- Check if the erasure flag is set (bit 0) -/
def isErased (e : Ext) : Bool := (e.val &&& 1) == 1

/-- Set the erasure flag -/
def setErased (e : Ext) : Ext := ⟨e.val ||| 1⟩

/-- Clear the erasure flag -/
def clearErased (e : Ext) : Ext := ⟨e.val &&& 0x00FFFFFE⟩

/-- Get the label portion (for DUP/SUP, bits 1-23) -/
def label (e : Ext) : UInt32 := e.val >>> 1

/-- Create from a label value -/
def fromLabel (label : UInt32) : Ext := ⟨label <<< 1⟩

/-- Create from label and erasure flag -/
def make (label : UInt32) (erased : Bool) : Ext :=
  ⟨(label <<< 1) ||| (if erased then 1 else 0)⟩

instance : ToString Ext where
  toString e := s!"#{e.val}"

end Ext

/-- Unary operation codes for OP1 nodes -/
inductive Op1Code where
  /-- Logical negation (for booleans) -/
  | not
  /-- Arithmetic negation (for integers) -/
  | neg
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace Op1Code

def toUInt8 : Op1Code → UInt8
  | .not => 0
  | .neg => 1

def fromUInt8 : UInt8 → Option Op1Code
  | 0 => some .not
  | 1 => some .neg
  | _ => none

instance : ToString Op1Code where
  toString
    | .not => "!"
    | .neg => "-"

end Op1Code

/-- Binary operation codes for OP2 nodes -/
inductive Op2Code where
  /-- Integer addition -/
  | add
  /-- Integer subtraction -/
  | sub
  /-- Integer multiplication -/
  | mul
  /-- Integer division -/
  | div
  /-- Integer modulo -/
  | mod
  /-- Bitwise AND -/
  | and
  /-- Bitwise OR -/
  | or
  /-- Bitwise XOR -/
  | xor
  /-- Left shift -/
  | shl
  /-- Right shift -/
  | shr
  /-- Equality comparison -/
  | eq
  /-- Not equal comparison -/
  | ne
  /-- Less than comparison -/
  | lt
  /-- Less than or equal comparison -/
  | le
  /-- Greater than comparison -/
  | gt
  /-- Greater than or equal comparison -/
  | ge
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace Op2Code

def toUInt8 : Op2Code → UInt8
  | .add => 0
  | .sub => 1
  | .mul => 2
  | .div => 3
  | .mod => 4
  | .and => 5
  | .or  => 6
  | .xor => 7
  | .shl => 8
  | .shr => 9
  | .eq  => 10
  | .ne  => 11
  | .lt  => 12
  | .le  => 13
  | .gt  => 14
  | .ge  => 15

def fromUInt8 : UInt8 → Option Op2Code
  | 0  => some .add
  | 1  => some .sub
  | 2  => some .mul
  | 3  => some .div
  | 4  => some .mod
  | 5  => some .and
  | 6  => some .or
  | 7  => some .xor
  | 8  => some .shl
  | 9  => some .shr
  | 10 => some .eq
  | 11 => some .ne
  | 12 => some .lt
  | 13 => some .le
  | 14 => some .gt
  | 15 => some .ge
  | _  => none

instance : ToString Op2Code where
  toString
    | .add => "+"
    | .sub => "-"
    | .mul => "*"
    | .div => "/"
    | .mod => "%"
    | .and => "&"
    | .or  => "|"
    | .xor => "^"
    | .shl => "<<"
    | .shr => ">>"
    | .eq  => "=="
    | .ne  => "!="
    | .lt  => "<"
    | .le  => "<="
    | .gt  => ">"
    | .ge  => ">="

end Op2Code

/-- Primitive type codes for NUM nodes -/
inductive PrimType where
  | u8 | u16 | u32 | u64
  | i8 | i16 | i32 | i64
  | f32 | f64
  | bool
  | char
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace PrimType

def toUInt8 : PrimType → UInt8
  | .u8   => 0
  | .u16  => 1
  | .u32  => 2
  | .u64  => 3
  | .i8   => 4
  | .i16  => 5
  | .i32  => 6
  | .i64  => 7
  | .f32  => 8
  | .f64  => 9
  | .bool => 10
  | .char => 11

def fromUInt8 : UInt8 → Option PrimType
  | 0  => some .u8
  | 1  => some .u16
  | 2  => some .u32
  | 3  => some .u64
  | 4  => some .i8
  | 5  => some .i16
  | 6  => some .i32
  | 7  => some .i64
  | 8  => some .f32
  | 9  => some .f64
  | 10 => some .bool
  | 11 => some .char
  | _  => none

instance : ToString PrimType where
  toString
    | .u8   => "U8"
    | .u16  => "U16"
    | .u32  => "U32"
    | .u64  => "U64"
    | .i8   => "I8"
    | .i16  => "I16"
    | .i32  => "I32"
    | .i64  => "I64"
    | .f32  => "F32"
    | .f64  => "F64"
    | .bool => "Bool"
    | .char => "Char"

end PrimType

/-- A 64-bit term in the interaction net -/
structure Term where
  bits : UInt64
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace Term

/-- Check if the substitution bit is set -/
def isSubstituted (t : Term) : Bool :=
  (t.bits &&& subMask) != 0

/-- Get the tag field -/
def tag (t : Term) : Tag :=
  let tagVal := ((t.bits &&& tagMask) >>> tagShift.toUInt64).toUInt8
  Tag.fromUInt8 tagVal |>.getD .var

/-- Get the extended metadata field -/
def ext (t : Term) : Ext :=
  ⟨((t.bits &&& extMask) >>> extShift.toUInt64).toUInt32⟩

/-- Get the value field -/
def val (t : Term) : UInt32 :=
  (t.bits &&& valMask).toUInt32

/-- Get the value field as a heap location -/
def loc (t : Term) : Loc := ⟨t.val⟩

/-- Construct a term from its components -/
def make (sub : Bool) (tag : Tag) (ext : Ext) (val : UInt32) : Term :=
  let subBit : UInt64 := if sub then subMask else 0
  let tagBits : UInt64 := tag.toUInt8.toUInt64 <<< tagShift.toUInt64
  let extBits : UInt64 := ext.val.toUInt64 <<< extShift.toUInt64
  let valBits : UInt64 := val.toUInt64
  ⟨subBit ||| tagBits ||| extBits ||| valBits⟩

/-- Construct a term without substitution -/
def create (tag : Tag) (ext : Ext) (val : UInt32) : Term :=
  make false tag ext val

/-- Create a variable term -/
def mkVar (loc : Loc) : Term :=
  create Tag.var Ext.zero loc.val

/-- Create a lambda term -/
def mkLam (loc : Loc) (erased : Bool := false) : Term :=
  create Tag.lam (if erased then Ext.zero.setErased else Ext.zero) loc.val

/-- Create an application term -/
def mkApp (loc : Loc) : Term :=
  create Tag.app Ext.zero loc.val

/-- Create a duplicator term with label -/
def mkDup (label : UInt32) (loc : Loc) : Term :=
  create Tag.dup (Ext.fromLabel label) loc.val

/-- Create a superposition term with label -/
def mkSup (label : UInt32) (loc : Loc) : Term :=
  create Tag.sup (Ext.fromLabel label) loc.val

/-- Create an eraser term -/
def mkEra : Term :=
  create Tag.era Ext.zero 0

/-- Create a constructor term -/
def mkCtor (ctorTag : UInt32) (arity : UInt32) (loc : Loc) : Term :=
  -- EXT encodes: lower 16 bits = ctor tag, upper 8 bits = arity
  let ext := Ext.ofNat ((arity.toNat <<< 16) ||| ctorTag.toNat)
  create Tag.ctor ext loc.val

/-- Create a pattern match term -/
def mkMat (expectedTag : UInt32) (loc : Loc) : Term :=
  create Tag.mat (Ext.ofNat expectedTag.toNat) loc.val

/-- Create a record term -/
def mkRec (numFields : UInt32) (loc : Loc) : Term :=
  create Tag.record (Ext.ofNat numFields.toNat) loc.val

/-- Create a projection term -/
def mkProj (fieldIndex : UInt32) (loc : Loc) : Term :=
  create Tag.proj (Ext.ofNat fieldIndex.toNat) loc.val

/-- Create a numeric literal term -/
def mkNum (primType : PrimType) (value : UInt32) : Term :=
  create Tag.num (Ext.ofNat primType.toUInt8.toNat) value

/-- Create a unary operation term -/
def mkOp1 (op : Op1Code) (loc : Loc) : Term :=
  create Tag.op1 (Ext.ofNat op.toUInt8.toNat) loc.val

/-- Create a binary operation term -/
def mkOp2 (op : Op2Code) (loc : Loc) : Term :=
  create Tag.op2 (Ext.ofNat op.toUInt8.toNat) loc.val

/-- Create a global reference term -/
def mkRef (refId : UInt32) : Term :=
  create Tag.ref Ext.zero refId

/-- Create a USE (strict evaluation) term -/
def mkUse (loc : Loc) : Term :=
  create Tag.use Ext.zero loc.val

/-- Create an ALO (allocation/instantiation) term.
    refId: index into the book for the definition to instantiate
    loc: heap location for the instantiated subgraph -/
def mkAlo (refId : UInt32) (loc : Loc) : Term :=
  create Tag.alo (Ext.ofNat refId.toNat) loc.val

/-- Create an ARRAY term.
    elemType: primitive type of elements (encoded in EXT)
    loc: heap location pointing to array metadata (length + data pointer) -/
def mkArray (elemType : PrimType) (loc : Loc) : Term :=
  create Tag.array (Ext.ofNat elemType.toUInt8.toNat) loc.val

/-- Create an INDEX term for runtime array/string indexing.
    loc: heap location for aux ports (array/string and index) -/
def mkIndex (loc : Loc) : Term :=
  create Tag.index Ext.zero loc.val

/-- Create a STRING term.
    loc: heap location pointing to string metadata (length + data pointer) -/
def mkString (loc : Loc) : Term :=
  create Tag.string Ext.zero loc.val

/-- Create a SLICE term for array/string views.
    loc: heap location pointing to slice metadata (source + start + length) -/
def mkSlice (loc : Loc) : Term :=
  create Tag.slice Ext.zero loc.val

/-- Get the label from a DUP or SUP term -/
def getLabel (t : Term) : UInt32 :=
  t.ext.label

/-- Check if a LAM has its bound variable erased -/
def isLamErased (t : Term) : Bool :=
  t.ext.isErased

/-- Get the constructor tag from a CTOR term -/
def getCtorTag (t : Term) : UInt32 :=
  (t.ext.val &&& 0xFFFF)

/-- Get the arity from a CTOR term -/
def getCtorArity (t : Term) : UInt32 :=
  (t.ext.val >>> 16) &&& 0xFF

/-- Get the expected tag from a MAT term -/
def getMatExpectedTag (t : Term) : UInt32 :=
  t.ext.val

/-- Get the number of fields from a REC term -/
def getRecNumFields (t : Term) : UInt32 :=
  t.ext.val

/-- Get the field index from a PROJ term -/
def getProjIndex (t : Term) : UInt32 :=
  t.ext.val

/-- Get the primitive type from a NUM term -/
def getNumType (t : Term) : Option PrimType :=
  PrimType.fromUInt8 t.ext.val.toUInt8

/-- Get the operation code from an OP1 term -/
def getOp1Code (t : Term) : Option Op1Code :=
  Op1Code.fromUInt8 t.ext.val.toUInt8

/-- Get the operation code from an OP2 term -/
def getOp2Code (t : Term) : Option Op2Code :=
  Op2Code.fromUInt8 t.ext.val.toUInt8

/-- Get the reference ID from a REF term -/
def getRefId (t : Term) : UInt32 :=
  t.val

/-- Get the reference ID from an ALO term (stored in EXT) -/
def getAloRefId (t : Term) : UInt32 :=
  t.ext.val

/-- Get the element type from an ARRAY term -/
def getArrayElemType (t : Term) : Option PrimType :=
  PrimType.fromUInt8 t.ext.val.toUInt8

/-- Mark a term as substituted, pointing to a new location -/
def substitute (t : Term) (newLoc : Loc) : Term :=
  make true t.tag t.ext newLoc.val

/-- Get the substitution target if this term is substituted -/
def getSubstitution (t : Term) : Option Loc :=
  if t.isSubstituted then some t.loc else none

/-- Check if this is a compound node (has children in heap) -/
def isCompound (t : Term) : Bool :=
  match t.tag with
  | .lam | .app | .dup | .sup | .ctor | .mat | .record | .proj | .op1 | .op2 | .use | .alo => true
  | .array | .index | .string | .slice => true
  | .var | .era | .num | .ref => false

/-- Check if this is an immediate value (no heap allocation needed) -/
def isImmediate (t : Term) : Bool :=
  match t.tag with
  | .num | .era => true
  | _ => false

end Term

end Somac.Circuit.Term
