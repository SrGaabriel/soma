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
  /-- Sequence IO actions: io_bind m f = f m -/
  | bindIO
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
  | .bindIO => "io_bind"

instance : ToString FFIOp := ⟨FFIOp.name⟩

def llvmName (op : FFIOp) : String := s!"soma_ffi_{op.name}"

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

/-- Resolve an explicit @[intrinsic "tag"] value to an Intrinsic -/
def fromTag? : String → Option Intrinsic
  | "primop.add" => some (.primOp .add)
  | "primop.sub" => some (.primOp .sub)
  | "primop.mul" => some (.primOp .mul)
  | "primop.div" => some (.primOp .div)
  | "primop.mod" => some (.primOp .mod)
  | "primop.eq" => some (.primOp .eq)
  | "primop.ne" => some (.primOp .ne)
  | "primop.lt" => some (.primOp .lt)
  | "primop.le" => some (.primOp .le)
  | "primop.gt" => some (.primOp .gt)
  | "primop.ge" => some (.primOp .ge)
  | "primop.and" => some (.primOp .and)
  | "primop.or" => some (.primOp .or)
  | "primop.not" => some (.primOp .not)
  | "primop.neg" => some (.primOp .neg)
  | "ffi.null" => some (.ffiOp .null)
  | "ffi.ptr_add" => some (.ffiOp .ptrAdd)
  | "ffi.ptr_diff" => some (.ffiOp .ptrDiff)
  | "ffi.ptr_read" => some (.ffiOp .ptrRead)
  | "ffi.ptr_write" => some (.ffiOp .ptrWrite)
  | "ffi.ptr_cast" => some (.ffiOp .ptrCast)
  | "ffi.to_cstring" => some (.ffiOp .toCString)
  | "ffi.from_cstring" => some (.ffiOp .fromCString)
  | "ffi.cstring_len" => some (.ffiOp .cstringLen)
  | "ffi.strcat" => some (.ffiOp .strcat)
  | "ffi.int_to_string" => some (.ffiOp .intToString)
  | "ffi.pure_io" => some (.ffiOp .pureIO)
  | "ffi.io_bind" => some (.ffiOp .bindIO)
  | _ => none

end Intrinsic

end Soma.Core
