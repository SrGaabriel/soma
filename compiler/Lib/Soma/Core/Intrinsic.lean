import Kenosis

namespace Soma.Core

open Kenosis

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

/-- FFI intrinsic operations (pointer/memory operations implemented as LLVM instructions) -/
inductive FFIOp where
  /-- Null pointer constant -/
  | null
  /-- Pointer arithmetic: ptr + offset -/
  | ptrAdd
  /-- Pointer difference: ptr - ptr -/
  | ptrDiff
  /-- Read from memory (load) -/
  | ptrRead
  /-- Write to memory (store) -/
  | ptrWrite
  /-- Reinterpret pointer type (bitcast) -/
  | ptrCast
  /-- Convert Soma String to C string -/
  | toCString
  /-- Convert C string to Soma String -/
  | fromCString
  /-- Get length of C string -/
  | cstringLen
  /-- String concatenation -/
  | strcat
  /-- Convert integer to string -/
  | intToString
  /-- Lift pure value into IO -/
  | pureIO
  deriving Repr, BEq, Hashable, DecidableEq, Serialize, Deserialize

namespace FFIOp

def name : FFIOp → String
  | .null => "null"
  | .ptrAdd => "ptr_add"
  | .ptrDiff => "ptr_diff"
  | .ptrRead => "ptr_read"
  | .ptrWrite => "ptr_write"
  | .ptrCast => "ptr_cast"
  | .toCString => "to_cstring"
  | .fromCString => "from_cstring"
  | .cstringLen => "cstring_len"
  | .strcat => "strcat"
  | .intToString => "int_to_string"
  | .pureIO => "pure_io"

instance : ToString FFIOp := ⟨FFIOp.name⟩

def llvmName (op : FFIOp) : String := s!"soma_ffi_{op.name}"

/-- Parse a string into an FFIOp -/
def fromString? : String → Option FFIOp
  | "null" => some .null
  | "ptr_add" => some .ptrAdd
  | "ptr_diff" => some .ptrDiff
  | "ptr_read" => some .ptrRead
  | "ptr_write" => some .ptrWrite
  | "ptr_cast" => some .ptrCast
  | "to_cstring" => some .toCString
  | "from_cstring" => some .fromCString
  | "cstring_len" => some .cstringLen
  | "strcat" => some .strcat
  | "int_to_string" => some .intToString
  | "pure_io" => some .pureIO
  | _ => none

end FFIOp

/-- Compiler intrinsics (LLVM, runtime, primitive ops, FFI ops, or externs) -/
inductive Intrinsic where
  | llvm (name : String)
  | runtime (fn : RuntimeFn)
  | primOp (op : PrimOp)
  | ffiOp (op : FFIOp)
  /-- External C function (linked at runtime) -/
  | extern (name : String)
  deriving Repr, BEq, Hashable, DecidableEq, Serialize, Deserialize

namespace Intrinsic

def display : Intrinsic → String
  | .llvm s => s
  | .runtime r => r.name
  | .primOp p => p.symbol
  | .ffiOp f => f.name
  | .extern s => s

def llvmName : Intrinsic → String
  | .llvm s => s
  | .runtime r => r.name
  | .primOp p => p.llvmName
  | .ffiOp f => f.llvmName
  | .extern s => s

instance : ToString Intrinsic := ⟨Intrinsic.display⟩

/-- Check if this is an FFI operation -/
def isFfiOp : Intrinsic → Bool
  | .ffiOp _ => true
  | _ => false

/-- Check if this is an extern function -/
def isExtern : Intrinsic → Bool
  | .extern _ => true
  | _ => false

/-- Get FFI operation if this is one -/
def ffiOp? : Intrinsic → Option FFIOp
  | .ffiOp op => some op
  | _ => none

/-- Get extern name if this is one -/
def externName? : Intrinsic → Option String
  | .extern name => some name
  | _ => none

end Intrinsic

end Soma.Core
