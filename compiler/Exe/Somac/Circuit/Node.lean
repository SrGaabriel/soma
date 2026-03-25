import Somac.Circuit.Term
import Soma.Core.Quantity

namespace Somac.Circuit.Node

open Somac.Circuit.Term (Term Tag Loc Ext Op1Code Op2Code PrimType)
open Soma.Core (Quantity)

/-- Unique identifier for a node in the graph -/
structure NodeId where
  id : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace NodeId

def zero : NodeId := ⟨0⟩

def succ (n : NodeId) : NodeId := ⟨n.id + 1⟩

instance : ToString NodeId where
  toString n := s!"n{n.id}"

end NodeId

/-- Port index within a node (0 = principal, 1+ = auxiliary) -/
structure PortIdx where
  idx : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace PortIdx

/-- The principal port (index 0) -/
def principal : PortIdx := ⟨0⟩

/-- First auxiliary port -/
def aux0 : PortIdx := ⟨1⟩

/-- Second auxiliary port -/
def aux1 : PortIdx := ⟨2⟩

/-- Third auxiliary port -/
def aux2 : PortIdx := ⟨3⟩

/-- Check if this is the principal port -/
def isPrincipal (p : PortIdx) : Bool := p.idx == 0

instance : ToString PortIdx where
  toString p := if p.isPrincipal then "●" else s!"p{p.idx}"

end PortIdx

/-- A fully qualified port: node + port index -/
structure PortId where
  node : NodeId
  port : PortIdx
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace PortId

/-- Create a principal port reference -/
def principal (n : NodeId) : PortId := ⟨n, .principal⟩

/-- Create an auxiliary port reference -/
def aux (n : NodeId) (idx : Nat) : PortId := ⟨n, ⟨idx + 1⟩⟩

instance : ToString PortId where
  toString p := s!"{p.node}:{p.port}"

end PortId

/-- A wire connects exactly two ports -/
structure Wire where
  /-- First endpoint -/
  src : PortId
  /-- Second endpoint -/
  dst : PortId
  deriving Repr, BEq, Hashable, Inhabited

namespace Wire

/-- Create a wire between two ports -/
def connect (a b : PortId) : Wire := ⟨a, b⟩

/-- Check if this wire involves a given port -/
def involvesPort (w : Wire) (p : PortId) : Bool :=
  w.src == p || w.dst == p

/-- Check if this wire connects two principal ports (active pair) -/
def isActivePair (w : Wire) : Bool :=
  w.src.port.isPrincipal && w.dst.port.isPrincipal

/-- Get the other endpoint of a wire given one endpoint -/
def otherEnd (w : Wire) (p : PortId) : Option PortId :=
  if w.src == p then some w.dst
  else if w.dst == p then some w.src
  else none

instance : ToString Wire where
  toString w := s!"{w.src} ~ {w.dst}"

end Wire

/-- A duplication label for DUP node matching -/
structure Label where
  id : UInt32
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace Label

def zero : Label := ⟨0⟩

def ofNat (n : Nat) : Label := ⟨n.toUInt32⟩

def toNat (l : Label) : Nat := l.id.toNat

def succ (l : Label) : Label := ⟨l.id + 1⟩

instance : ToString Label where
  toString l := s!"&{l.id}"

end Label

/-- High-level representation of an interaction net node -/
inductive Node where
  /-- Lambda abstraction
      - Principal: function value (ready for application)
      - Aux 0: bound variable slot
      - Aux 1: body result
      - erased: true if bound variable is unused (quantity 0) -/
  | lam (erased : Bool)

  /-- Function application
      - Principal: result of application
      - Aux 0: function to apply
      - Aux 1: argument -/
  | app

  /-- Duplicator node (explicit cloning)
      - Principal: value to duplicate
      - Aux 0: first copy (DP0)
      - Aux 1: second copy (DP1)
      - label: unique identifier for this duplication -/
  | dup (label : Label)

  /-- Superposition node (lazy duplication result)
      - Principal: the superposed value
      - Aux 0: first contained value (val0)
      - Aux 1: second contained value (val1)
      - label: matches DUP labels for annihilation

      SUP is the runtime counterpart to DUP for Tier 3 (recursive data).
      When a DUP is applied to a recursive value, instead of eagerly cloning,
      a SUP node is created. Consumers access the copies via projections.
      Same-label DUP-SUP annihilates in O(1); different-label commutes. -/
  | sup (label : Label)

  /-- Eraser node (discard value)
      - Principal: value to erase
      - No auxiliary ports -/
  | era

  /-- Constructor application
      - Principal: constructed value
      - Aux 0..N: constructor fields
      - tag: discriminant for pattern matching
      - arity: number of fields -/
  | ctor (tag : Nat) (arity : Nat)

  /-- Pattern match (binary hit/miss)
      - Principal: result of match
      - Aux 0: scrutinee
      - Aux 1: hit continuation (when tag matches)
      - Aux 2: miss continuation (when tag doesn't match)
      - expectedTag: constructor tag to match against -/
  | mat (expectedTag : Nat)

  /-- Record value
      - Principal: record value
      - Aux 0..N: field values
      - numFields: number of fields -/
  | record (numFields : Nat)

  /-- Field projection
      - Principal: extracted field value
      - Aux 0: record to project from
      - fieldIndex: which field to extract -/
  | proj (fieldIndex : Nat)

  /-- Numeric literal (immediate value)
      - Principal: numeric value
      - No auxiliary ports
      - primType: the primitive type
      - value: the immediate value -/
  | num (primType : PrimType) (value : UInt32)

  /-- Wide numeric literal (64-bit immediate)
      - Principal: numeric value
      - No auxiliary ports
      - primType: f64, i64, or u64
      - lo/hi: lower and upper 32-bit halves -/
  | num64 (primType : PrimType) (lo hi : UInt32)

  /-- Unary primitive operation
      - Principal: result
      - Aux 0: operand
      - op: the operation to perform (not, neg) -/
  | op1 (op : Op1Code)

  /-- Binary primitive operation
      - Principal: result
      - Aux 0: left operand
      - Aux 1: right operand
      - op: the operation to perform -/
  | op2 (op : Op2Code)

  /-- Global reference (book entry, static)
      - Principal: value
      - No auxiliary ports
      - refId: index into the global definition book
      - REF is a static pointer to a definition; it does NOT trigger instantiation.
        When reduction needs the definition's body, an ALO node is created. -/
  | ref (refId : Nat)

  /-- Strict evaluation point (USE node, for CBV semantics)
      - Principal: result
      - Aux 0: term to force to weak normal form
      - Aux 1: continuation that receives the forced value -/
  | use

  /-- Allocation node (lazy instantiation)
      - Principal: the instantiated value
      - No auxiliary ports (the instantiated subgraph is built on demand)
      - refId: index into the global definition book

      ALO is the dynamic counterpart to REF. When a recursive call is made:
      1. A REF node points to the static definition in the book
      2. When the REF interacts, an ALO is created
      3. The ALO lazily expands into a fresh copy of the definition's subgraph
      4. This enables infinite unfolding without infinite graphs upfront

      The key insight: REF is the "address" of a definition, ALO is the
      "instantiation" of that definition into a dynamic subgraph. -/
  | alo (refId : Nat)

  /-- Heap-allocated array
      - Principal: the array value
      - Aux 0: length (NUM node)
      - Aux 1: data pointer (heap location of contiguous elements)
      - elemType: primitive type of elements (for type-safe operations)

      Arrays support:
      - O(1) random access via INDEX node
      - DUP-ARRAY creates a shallow copy (shares backing memory, COW semantics)
      - ERA-ARRAY frees the backing memory when refcount hits zero -/
  | array (elemType : PrimType)

  /-- Runtime array/string indexing
      - Principal: extracted element
      - Aux 0: array or string to index
      - Aux 1: index value (NUM)

      Unlike PROJ which has compile-time constant index in EXT,
      INDEX takes a runtime value, enabling dynamic access patterns. -/
  | index

  /-- Heap-allocated string (UTF-8 encoded)
      - Principal: the string value
      - Aux 0: length in bytes (NUM node)
      - Aux 1: data pointer (heap location of UTF-8 bytes)

      Strings are immutable. Operations like concatenation create new strings.
      DUP-STRING shares the backing memory (strings are never mutated).
      ERA-STRING decrements refcount and frees when zero. -/
  | string

  /-- Array/string slice (view without copying)
      - Principal: the slice value
      - Aux 0: source array or string
      - Aux 1: start index (NUM)
      - Aux 2: length (NUM)

      Slices share the backing memory of their source.
      They enable efficient substring/subarray operations.
      DUP-SLICE just copies the slice metadata (start, length).
      ERA-SLICE decrements the source's refcount. -/
  | slice

  deriving Repr, BEq, Inhabited

namespace Node

/-- Get the number of auxiliary ports for a node -/
def numAuxPorts : Node → Nat
  | .lam _ => 2 -- var, body
  | .app => 2 -- fun, arg
  | .dup _ => 2 -- copy0, copy1
  | .sup _ => 2 -- val0, val1
  | .era => 0
  | .ctor _ n => n -- fields
  | .mat _ => 3 -- scrutinee, hit, miss
  | .record n => n -- fields
  | .proj _ => 1 -- record
  | .num _ _ => 0
  | .num64 _ _ _ => 0
  | .op1 _ => 1 -- operand
  | .op2 _ => 2 -- left, right
  | .ref _ => 0
  | .use => 2  -- term, continuation
  | .alo _ => 0 -- instantiation happens lazily, no static aux ports
  | .array _  => 2 -- length, data_ptr
  | .index => 2 -- array/string, index
  | .string  => 2 -- length, data_ptr
  | .slice => 3 -- source, start, length

/-- Get the total number of ports (principal + auxiliary) -/
def numPorts (n : Node) : Nat := 1 + n.numAuxPorts

/-- Check if a node is a combinator (pure interaction net node) -/
def isCombinator : Node → Bool
  | .lam _ | .app | .dup _ | .sup _ | .era => true
  | _ => false

/-- Check if a node carries an immediate value (no heap children) -/
def isImmediate : Node → Bool
  | .num _ _ | .num64 _ _ _ | .era | .ref _ | .alo _ => true
  | _ => false

/-- Get the tag for a node -/
def toTag : Node → Tag
  | .lam _    => .lam
  | .app      => .app
  | .dup _    => .dup
  | .sup _    => .sup
  | .era      => .era
  | .ctor _ _ => .ctor
  | .mat _    => .mat
  | .record _ => .record
  | .proj _   => .proj
  | .num _ _  => .num
  | .num64 _ _ _ => .num
  | .op1 _    => .op1
  | .op2 _    => .op2
  | .ref _    => .ref
  | .use      => .use
  | .alo _    => .alo
  | .array _  => .array
  | .index    => .index
  | .string   => .string
  | .slice    => .slice

/-- Convert to a packed Term representation -/
def toTerm (n : Node) (loc : Loc) : Term :=
  match n with
  | .lam erased   => Term.mkLam loc erased
  | .app          => Term.mkApp loc
  | .dup label    => Term.mkDup label.id loc
  | .sup label    => Term.mkSup label.id loc
  | .era          => Term.mkEra
  | .ctor tag ar  => Term.mkCtor tag.toUInt32 ar.toUInt32 loc
  | .mat expected => Term.mkMat expected.toUInt32 loc
  | .record nf    => Term.mkRec nf.toUInt32 loc
  | .proj idx     => Term.mkProj idx.toUInt32 loc
  | .num pt val   => Term.mkNum pt val
  | .num64 pt lo _ => Term.mkNum pt lo  -- TODO: extend Term to support 64-bit immediates
  | .op1 op       => Term.mkOp1 op loc
  | .op2 op       => Term.mkOp2 op loc
  | .ref rid      => Term.mkRef rid.toUInt32
  | .use          => Term.mkUse loc
  | .alo rid      => Term.mkAlo rid.toUInt32 loc
  | .array et     => Term.mkArray et loc
  | .index        => Term.mkIndex loc
  | .string       => Term.mkString loc
  | .slice        => Term.mkSlice loc

instance : ToString Node where
  toString
    | .lam true    => "LAM[era]"
    | .lam false   => "LAM"
    | .app         => "APP"
    | .dup label   => s!"DUP{label}"
    | .sup label   => s!"SUP{label}"
    | .era         => "ERA"
    | .ctor tag ar => s!"CTOR({tag}/{ar})"
    | .mat exp     => s!"MAT({exp})"
    | .record nf   => s!"REC({nf})"
    | .proj idx    => s!"PROJ({idx})"
    | .num pt val  => s!"{pt}({val})"
    | .num64 pt lo hi => s!"{pt}({hi.toNat * 0x100000000 + lo.toNat})"
    | .op1 op      => s!"OP1({op})"
    | .op2 op      => s!"OP2({op})"
    | .ref rid     => s!"REF({rid})"
    | .use         => "USE"
    | .alo rid     => s!"ALO({rid})"
    | .array et    => s!"ARRAY[{et}]"
    | .index       => "INDEX"
    | .string      => "STRING"
    | .slice       => "SLICE"

end Node

/-- The role of a port in a node -/
inductive PortRole where
  /-- Principal port: where interactions happen -/
  | principal
  /-- Lambda's bound variable slot -/
  | lamVar
  /-- Lambda's body result -/
  | lamBody
  /-- Application's function -/
  | appFun
  /-- Application's argument -/
  | appArg
  /-- DUP's first copy output -/
  | dupCopy0
  /-- DUP's second copy output -/
  | dupCopy1
  /-- SUP's first contained value -/
  | supVal0
  /-- SUP's second contained value -/
  | supVal1
  /-- Constructor field at index -/
  | ctorField (index : Nat)
  /-- MAT scrutinee -/
  | matScrutinee
  /-- MAT hit continuation -/
  | matHit
  /-- MAT miss continuation -/
  | matMiss
  /-- Record field at index -/
  | recField (index : Nat)
  /-- PROJ's record input -/
  | projRecord
  /-- OP1's operand -/
  | op1Operand
  /-- OP2's left operand -/
  | op2Left
  /-- OP2's right operand -/
  | op2Right
  /-- USE's term to force -/
  | useTerm
  /-- USE's continuation -/
  | useCont
  /-- ARRAY's length -/
  | arrayLength
  /-- ARRAY's data pointer -/
  | arrayData
  /-- INDEX's array/string source -/
  | indexSource
  /-- INDEX's index value -/
  | indexIdx
  /-- STRING's length -/
  | stringLength
  /-- STRING's data pointer -/
  | stringData
  /-- SLICE's source array/string -/
  | sliceSource
  /-- SLICE's start index -/
  | sliceStart
  /-- SLICE's length -/
  | sliceLength
  deriving Repr, BEq, Inhabited

namespace PortRole

instance : ToString PortRole where
  toString
    | .principal      => "●"
    | .lamVar         => "var"
    | .lamBody        => "body"
    | .appFun         => "fun"
    | .appArg         => "arg"
    | .dupCopy0       => "copy₀"
    | .dupCopy1       => "copy₁"
    | .supVal0        => "val₀"
    | .supVal1        => "val₁"
    | .ctorField i    => s!"field[{i}]"
    | .matScrutinee   => "scrutinee"
    | .matHit         => "hit"
    | .matMiss        => "miss"
    | .recField i     => s!"field[{i}]"
    | .projRecord     => "record"
    | .op1Operand     => "operand"
    | .op2Left        => "left"
    | .op2Right       => "right"
    | .useTerm        => "term"
    | .useCont        => "cont"
    | .arrayLength    => "length"
    | .arrayData      => "data"
    | .indexSource    => "source"
    | .indexIdx       => "index"
    | .stringLength   => "length"
    | .stringData     => "data"
    | .sliceSource    => "source"
    | .sliceStart     => "start"
    | .sliceLength    => "length"

end PortRole

/-- Get the role of a port given a node and port index -/
def Node.portRole (n : Node) (p : PortIdx) : Option PortRole :=
  if p.isPrincipal then some .principal
  else match n, p.idx with
    | .lam _, 1       => some .lamVar
    | .lam _, 2       => some .lamBody
    | .app, 1         => some .appFun
    | .app, 2         => some .appArg
    | .dup _, 1       => some .dupCopy0
    | .dup _, 2       => some .dupCopy1
    | .sup _, 1       => some .supVal0
    | .sup _, 2       => some .supVal1
    | .ctor _ ar, i   => if i <= ar then some (.ctorField (i - 1)) else none
    | .mat _, 1       => some .matScrutinee
    | .mat _, 2       => some .matHit
    | .mat _, 3       => some .matMiss
    | .record nf, i   => if i <= nf then some (.recField (i - 1)) else none
    | .proj _, 1      => some .projRecord
    | .op1 _, 1       => some .op1Operand
    | .op2 _, 1       => some .op2Left
    | .op2 _, 2       => some .op2Right
    | .use, 1         => some .useTerm
    | .use, 2         => some .useCont
    | .array _, 1     => some .arrayLength
    | .array _, 2     => some .arrayData
    | .index, 1       => some .indexSource
    | .index, 2       => some .indexIdx
    | .string, 1      => some .stringLength
    | .string, 2      => some .stringData
    | .slice, 1       => some .sliceSource
    | .slice, 2       => some .sliceStart
    | .slice, 3       => some .sliceLength
    | _, _            => none

/-! ## Active Pairs

  An active pair is two nodes connected principal-to-principal.
  These are the sites where interaction (reduction) can occur.
-/

/-- An active pair: two nodes whose principal ports are connected -/
structure ActivePair where
  /-- First node in the pair -/
  node1 : NodeId
  /-- Second node in the pair -/
  node2 : NodeId
  deriving Repr, BEq, Hashable, Inhabited

namespace ActivePair

/-- Create an active pair (order-normalized for consistent hashing) -/
def create (a b : NodeId) : ActivePair :=
  if a.id ≤ b.id then ⟨a, b⟩ else ⟨b, a⟩

/-- Check if a node is part of this active pair -/
def contains (ap : ActivePair) (n : NodeId) : Bool :=
  ap.node1 == n || ap.node2 == n

instance : ToString ActivePair where
  toString ap := s!"({ap.node1} ●─● {ap.node2})"

end ActivePair

end Somac.Circuit.Node
