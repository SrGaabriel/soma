import Soma.Unique
import Kenosis

namespace Soma.Core

open Soma
open Kenosis

/-- Prefix for local identifiers, distinguishing different kinds of locals -/
inductive LocalPrefix where
  | temp
  | block
  | param
  | reg
  | patternVar
  | closureSelf
  | dictParam
  | refParam
  | erasure
  | forkedTask
  deriving Repr, BEq, Hashable, DecidableEq, Serialize, Deserialize

namespace LocalPrefix

def toString : LocalPrefix → String
  | .temp => "t"
  | .block => "block"
  | .param => "p"
  | .reg => "r"
  | .patternVar => "pv"
  | .closureSelf => "closure_self"
  | .dictParam => "dict_param"
  | .refParam => "ref_param"
  | .erasure => "era"
  | .forkedTask => "fork"

instance : ToString LocalPrefix := ⟨LocalPrefix.toString⟩

end LocalPrefix

/-- A local identifier with prefix and index -/
structure LocalId where
  kind : LocalPrefix
  index : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Serialize, Deserialize

namespace LocalId

def toString (l : LocalId) : String := s!"{l.kind}{l.index}"

instance : ToString LocalId := ⟨LocalId.toString⟩

/-- Create a temp local -/
def temp (n : Nat) : LocalId := { kind := .temp, index := n }

/-- Create a block label -/
def block (n : Nat) : LocalId := { kind := .block, index := n }

/-- Create a parameter -/
def param (n : Nat) : LocalId := { kind := .param, index := n }

/-- Create an erasure -/
def erasure (n : Nat) : LocalId := { kind := .erasure, index := n }

/-- Create a forked task -/
def forkedTask (n : Nat) : LocalId := { kind := .forkedTask, index := n }

end LocalId

/-- Unique identifier for a local binding site.

    BindingIds identify binding sites (not uses) within expressions.
    They carry enough context for:
    - Scope tracking (the numeric id)
    - Debugging (original source name)
    - Cross-module safety (module name)
    - Semantic classification (prefix)
-/
structure BindingId where
  id : Nat
  module : String
  original : String
  kind : LocalPrefix := .patternVar
  deriving Repr

namespace BindingId

/-- Equality based on (id, module) - original name and prefix are metadata -/
instance : BEq BindingId where
  beq b1 b2 := b1.id == b2.id && b1.module == b2.module

instance : Hashable BindingId where
  hash b := mixHash (hash b.id) (hash b.module)

instance : Ord BindingId where
  compare b1 b2 :=
    match compare b1.module b2.module with
    | .eq => compare b1.id b2.id
    | other => other

instance : DecidableEq BindingId := fun b1 b2 =>
  match decEq b1.id b2.id, decEq b1.module b2.module, decEq b1.original b2.original, decEq b1.kind b2.kind with
  | isTrue h1, isTrue h2, isTrue h3, isTrue h4 =>
    isTrue (by cases b1; cases b2; simp_all)
  | isFalse h, _, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
  | _, isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
  | _, _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
  | _, _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)

instance : Inhabited BindingId := ⟨{ id := 0, module := "", original := "_" }⟩

/-- Display for debugging -/
def display (b : BindingId) : String := b.original

/-- Full display with ID -/
def debugDisplay (b : BindingId) : String := s!"{b.original}#{b.id}"

instance : ToString BindingId := ⟨BindingId.display⟩

/-- Generate the next binding ID (for sequential generation) -/
def next (b : BindingId) (newOriginal : String) : BindingId :=
  { b with id := b.id + 1, original := newOriginal }

end BindingId


/-- Runtime functions provided by the Soma runtime -/
inductive RuntimeFn where
  | printInt
  | printStr
  | panic
  | trace
  | alloc
  | free
  deriving Repr, BEq, Hashable, DecidableEq, Serialize, Deserialize

namespace RuntimeFn

def name : RuntimeFn → String
  | .printInt => "soma_print_int"
  | .printStr => "soma_print_str"
  | .panic => "soma_panic"
  | .trace => "soma_trace"
  | .alloc => "soma_alloc"
  | .free => "soma_free"

instance : ToString RuntimeFn := ⟨RuntimeFn.name⟩

end RuntimeFn

/-- Primitive operations (implemented as LLVM instructions) -/
inductive PrimOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  | and | or | not | neg
  deriving Repr, BEq, Hashable, DecidableEq, Serialize, Deserialize

namespace PrimOp

def symbol : PrimOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||" | .not => "!" | .neg => "neg"

def name : PrimOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod"
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .and => "and" | .or => "or" | .not => "not" | .neg => "neg"

instance : ToString PrimOp := ⟨PrimOp.symbol⟩

def llvmName (op : PrimOp) : String := s!"primop_{op.name}"

/-- Parse a string (symbol or name) into a PrimOp -/
def fromString? : String → Option PrimOp
  | "+" | "add" => some .add
  | "-" | "sub" => some .sub
  | "*" | "mul" => some .mul
  | "/" | "div" => some .div
  | "%" | "mod" => some .mod
  | "==" | "eq" => some .eq
  | "!=" | "ne" => some .ne
  | "<" | "lt" => some .lt
  | "<=" | "le" => some .le
  | ">" | "gt" => some .gt
  | ">=" | "ge" => some .ge
  | "&&" | "and" => some .and
  | "||" | "or" => some .or
  | "!" | "not" => some .not
  | "neg" => some .neg
  | _ => none

end PrimOp

/-- Compiler intrinsics (LLVM, runtime, or primitive ops) -/
inductive Intrinsic where
  | llvm (name : String)
  | runtime (fn : RuntimeFn)
  | primOp (op : PrimOp)
  deriving Repr, BEq, Hashable, DecidableEq, Serialize, Deserialize

namespace Intrinsic

def display : Intrinsic → String
  | .llvm s => s
  | .runtime r => r.name
  | .primOp p => p.symbol

def llvmName : Intrinsic → String
  | .llvm s => s
  | .runtime r => r.name
  | .primOp p => p.llvmName

instance : ToString Intrinsic := ⟨Intrinsic.display⟩

end Intrinsic

/-- Kind of dictionary name -/
inductive DictKind where
  /-- Global dictionary instance -/
  | global
  /-- Dictionary struct type -/
  | struct
  deriving Repr, BEq, Hashable, DecidableEq, Serialize, Deserialize

/-- A type class dictionary identifier.
    Uses a string representation of the instance type for naming purposes. -/
structure DictId where
  /-- Module where the instance is defined -/
  module : String
  /-- Type class name -/
  className : String
  /-- String representation of the instance type (for naming) -/
  instanceTypeStr : String
  /-- Kind of dictionary -/
  kind : DictKind
  deriving Repr, BEq, Hashable, DecidableEq, Serialize, Deserialize

namespace DictId

def display (d : DictId) : String :=
  match d.kind with
  | .global => s!"Dict${d.className}${d.instanceTypeStr}"
  | .struct => s!"DictStruct${d.className}"

instance : ToString DictId := ⟨DictId.display⟩

end DictId


/-- Kinds of synthetic (compiler-generated) names.
    Each synthetic name is derived from a base Unique and carries
    semantic information about why it was generated.

    Note: Type arguments are stored as strings for simplicity. -/
inductive SyntheticKind where
  | liftedLambda
  | closureEnv
  | monomorphized (typeStrs : Array String)
  | instanceMethod (forTypeStr : String)
  | dictParam (className : String) (forTypeStr : String)
  | dictGlobal (className : String) (forTypeStr : String)
  | dictStruct (className : String)
  | refParam (blockName : String)
  | erasure
  | temp
  deriving Repr, BEq, Hashable, DecidableEq, Serialize, Deserialize

namespace SyntheticKind

def suffix : SyntheticKind → String
  | .liftedLambda => "lambda"
  | .closureEnv => "env"
  | .monomorphized ts => s!"mono${ts.toList |> String.intercalate "_"}"
  | .instanceMethod ty => s!"inst${ty}"
  | .dictParam cls ty => s!"dict${cls}${ty}"
  | .dictGlobal cls ty => s!"Dict${cls}${ty}"
  | .dictStruct cls => s!"DictStruct${cls}"
  | .refParam blk => s!"refparam${blk}"
  | .erasure => "era"
  | .temp => "tmp"

instance : ToString SyntheticKind := ⟨SyntheticKind.suffix⟩

end SyntheticKind

/-- A fully resolved name in the compiler -/
inductive Name where
  | user (unique : Unique)
  | synthetic (base : Unique) (kind : SyntheticKind) (discriminator : Nat := 0)
  | intrinsic (i : Intrinsic)
  | local_ (id : LocalId)
  | projection (base : Name) (index : Nat)
  | dict (id : DictId)
  | ctor (typeUnique : Unique) (ctorName : String) (tag : Nat)
  deriving Serialize, Deserialize

namespace Name

/-- Equality for names -/
partial def beq : Name → Name → Bool
  | .user u1, .user u2 => u1 == u2
  | .synthetic b1 k1 d1, .synthetic b2 k2 d2 => b1 == b2 && k1 == k2 && d1 == d2
  | .intrinsic i1, .intrinsic i2 => i1 == i2
  | .local_ l1, .local_ l2 => l1 == l2
  | .projection b1 i1, .projection b2 i2 => i1 == i2 && Name.beq b1 b2
  | .dict d1, .dict d2 => d1 == d2
  | .ctor u1 c1 t1, .ctor u2 c2 t2 => u1 == u2 && c1 == c2 && t1 == t2
  | _, _ => false

instance : BEq Name := ⟨Name.beq⟩

/-- Hash for names -/
partial def hash : Name → UInt64
  | .user u => mixHash 0 (Hashable.hash u)
  | .synthetic b k d => mixHash 1 (mixHash (Hashable.hash b) (mixHash (Hashable.hash k) (Hashable.hash d)))
  | .intrinsic i => mixHash 2 (Hashable.hash i)
  | .local_ l => mixHash 3 (Hashable.hash l)
  | .projection b i => mixHash 4 (mixHash (Name.hash b) (Hashable.hash i))
  | .dict d => mixHash 5 (Hashable.hash d)
  | .ctor u _ t => mixHash 6 (mixHash (Hashable.hash u) (Hashable.hash t))

instance : Hashable Name := ⟨Name.hash⟩

/-- Display name for error messages and debugging -/
partial def display : Name → String
  | .user u => u.display
  | .synthetic base kind disc =>
      let suffix := kind.suffix
      let discStr := if disc > 0 then s!"${disc}" else ""
      s!"{base.original}${suffix}{discStr}"
  | .intrinsic i => i.display
  | .local_ l => l.toString
  | .projection base idx => s!"{display base}.{idx}"
  | .dict d => d.display
  | .ctor u c _ => s!"{u.display}.{c}"

instance : ToString Name := ⟨Name.display⟩

/-- Mangled name for LLVM codegen -/
partial def mangle : Name → String
  | .user u => u.mangle
  | .synthetic base kind disc =>
      let baseMangle := base.mangle
      let suffix := kind.suffix.map fun c => if c.isAlphanum || c == '_' then c else '_'
      s!"{baseMangle}_{suffix}_{disc}"
  | .intrinsic i => i.llvmName
  | .local_ l => l.toString
  | .projection base idx => s!"{mangle base}_proj{idx}"
  | .dict d => s!"{d.module}_{d.display}".map fun c => if c.isAlphanum || c == '_' then c else '_'
  | .ctor u c t => s!"{u.mangle}_{c}_{t}"

/-- Get the original source name if available -/
def original : Name → String
  | .user u => u.original
  | .synthetic base _ _ => base.original
  | .intrinsic i => i.display
  | .local_ l => l.toString
  | .projection base _ => original base
  | .dict d => d.display
  | .ctor u c _ => s!"{u.original}.{c}"

/-- Get the module name if available -/
def module? : Name → Option String
  | .user u => some u.module
  | .synthetic base _ _ => some base.module
  | .intrinsic _ => none
  | .local_ _ => none
  | .projection base _ => module? base
  | .dict d => some d.module
  | .ctor u _ _ => some u.module

/-- Get the base unique if this name has one -/
def baseUnique? : Name → Option Unique
  | .user u => some u
  | .synthetic base _ _ => some base
  | .ctor u _ _ => some u
  | _ => none

def isUser : Name → Bool
  | .user _ => true
  | _ => false

def isSynthetic : Name → Bool
  | .synthetic _ _ _ => true
  | _ => false

def isIntrinsic : Name → Bool
  | .intrinsic _ => true
  | _ => false

def isLocal : Name → Bool
  | .local_ _ => true
  | _ => false

def isProjection : Name → Bool
  | .projection _ _ => true
  | _ => false

def isDict : Name → Bool
  | .dict _ => true
  | _ => false

def isCtor : Name → Bool
  | .ctor _ _ _ => true
  | _ => false

def isErasure : Name → Bool
  | .local_ ⟨.erasure, _⟩ => true
  | .synthetic _ .erasure _ => true
  | _ => false

def isForkedTask : Name → Bool
  | .local_ ⟨.forkedTask, _⟩ => true
  | _ => false

def isInstanceMethod : Name → Bool
  | .synthetic _ (.instanceMethod _) _ => true
  | _ => false

/-- Create a projection -/
def mkProj (base : Name) (index : Nat) : Name :=
  .projection base index

/-- Create first projection (index 0) -/
def mkProj0 (base : Name) : Name := mkProj base 0

/-- Create second projection (index 1) -/
def mkProj1 (base : Name) : Name := mkProj base 1

/-- Get projection base if this is a projection -/
def projBase? : Name → Option Name
  | .projection base _ => some base
  | _ => none

/-- Check if this is projection 0 -/
def isProj0 : Name → Bool
  | .projection _ 0 => true
  | _ => false

/-- Check if this is projection 1 -/
def isProj1 : Name → Bool
  | .projection _ 1 => true
  | _ => false

/-- Get constructor tag if this is a constructor -/
def ctorTag? : Name → Option Nat
  | .ctor _ _ t => some t
  | _ => none

/-- Get the simple constructor name (without type prefix) if this is a constructor -/
def ctorSimpleName? : Name → Option String
  | .ctor _ c _ => some c
  | _ => none

/-- Get instance method type string if this is an instance method -/
def instanceMethodTypeStr? : Name → Option String
  | .synthetic _ (.instanceMethod ty) _ => some ty
  | _ => none

/-- Get instance method base unique if this is an instance method -/
def instanceMethodBase? : Name → Option Unique
  | .synthetic base (.instanceMethod _) _ => some base
  | _ => none

/-- Decompose an instance method name -/
def decomposeInstanceMethod? : Name → Option (Unique × String)
  | .synthetic base (.instanceMethod ty) _ => some (base, ty)
  | _ => none

/-- Check if this is an instance method for a specific base -/
def isInstanceMethodFor (baseUnique : Unique) : Name → Bool
  | .synthetic base (.instanceMethod _) _ => base == baseUnique
  | _ => false

/-- Create a synthetic name from a base -/
def makeSynthetic (base : Name) (kind : SyntheticKind) : Option Name :=
  base.baseUnique?.map fun u => .synthetic u kind 0

/-- Create a monomorphized name -/
def makeMonomorphized (base : Name) (typeStrs : Array String) : Option Name :=
  makeSynthetic base (.monomorphized typeStrs)

/-- Create an instance method name -/
def makeInstanceMethod (base : Name) (forTypeStr : String) : Option Name :=
  makeSynthetic base (.instanceMethod forTypeStr)

/-- Create a dictionary parameter name -/
def makeDictParam (base : Name) (className : String) (forTypeStr : String) : Option Name :=
  makeSynthetic base (.dictParam className forTypeStr)

/-- Create a dictionary global name -/
def makeDictGlobal (base : Name) (className : String) (forTypeStr : String) : Option Name :=
  makeSynthetic base (.dictGlobal className forTypeStr)

/-- Create a ref parameter name -/
def makeRefParam (base : Name) (blockName : String) : Option Name :=
  makeSynthetic base (.refParam blockName)

/-- Create a global dictionary name directly -/
def mkDictGlobal (moduleName : String) (className : String) (instanceTypeStr : String) : Name :=
  .dict { module := moduleName, className, instanceTypeStr, kind := .global }

/-- Create a dictionary struct name directly -/
def mkDictStruct (moduleName : String) (className : String) (instanceTypeStr : String) : Name :=
  .dict { module := moduleName, className, instanceTypeStr, kind := .struct }

/-- Convert a forked task name -/
def mkForkedTask : Name → Option Name
  | .local_ ⟨_, n⟩ => some (.local_ ⟨.forkedTask, n⟩)
  | _ => none

end Name

/-- Create a Name.user from a BindingId (for local → global promotion) -/
def BindingId.toUserName (b : BindingId) : Name :=
  .user { id := b.id, module := b.module, original := b.original }

end Soma.Core
