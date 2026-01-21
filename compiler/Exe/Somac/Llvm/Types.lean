namespace Somac.Llvm

/-- LLVM calling conventions -/
inductive CallConv where
  | c -- Default C calling convention
  | fast -- Fast calling convention
  | cold -- Cold calling convention
  | tailcc -- Tail call optimized
  deriving Repr, BEq, Inhabited

instance : ToString CallConv where
  toString
    | .c => "ccc"
    | .fast => "fastcc"
    | .cold => "coldcc"
    | .tailcc => "tailcc"

/-- LLVM linkage types -/
inductive Linkage where
  | private_ -- Not visible outside the module
  | internal -- Like private, but may appear in symbol table
  | external -- Default linkage, visible everywhere
  | weak -- Weak linkage
  | linkonce -- Merged with other linkonce of same name
  deriving Repr, BEq, Inhabited

instance : ToString Linkage where
  toString
    | .private_ => "private"
    | .internal => "internal"
    | .external => ""
    | .weak => "weak"
    | .linkonce => "linkonce"

/-- LLVM types -/
inductive LLVMType where
  -- Primitive types
  | void
  | i1
  | i8 | i16 | i32 | i64 | i128
  | half | float | double | fp128
  -- Pointer type
  | ptr
  -- Aggregate types
  | array (size : Nat) (elem : LLVMType)
  | struct (packed : Bool) (fields : Array LLVMType)
  | namedStruct (name : String)
  -- Function type
  | func (ret : LLVMType) (params : Array LLVMType) (vararg : Bool := false)
  -- Vector type
  | vector (size : Nat) (elem : LLVMType)
  deriving Repr, BEq, Inhabited

namespace LLVMType

/-- Get the size in bits for integer types -/
def intBits : LLVMType → Option Nat
  | .i1 => some 1
  | .i8 => some 8
  | .i16 => some 16
  | .i32 => some 32
  | .i64 => some 64
  | .i128 => some 128
  | _ => none

/-- Check if this is an integer type -/
def isInt : LLVMType → Bool
  | .i1 | .i8 | .i16 | .i32 | .i64 | .i128 => true
  | _ => false

/-- Check if this is a floating point type -/
def isFloat : LLVMType → Bool
  | .half | .float | .double | .fp128 => true
  | _ => false

/-- Check if this is a pointer type -/
def isPtr : LLVMType → Bool
  | .ptr => true
  | _ => false

/-- Convert to LLVM IR syntax -/
partial def toLLVM : LLVMType → String
  | .void => "void"
  | .i1 => "i1"
  | .i8 => "i8"
  | .i16 => "i16"
  | .i32 => "i32"
  | .i64 => "i64"
  | .i128 => "i128"
  | .half => "half"
  | .float => "float"
  | .double => "double"
  | .fp128 => "fp128"
  | .ptr => "ptr"
  | .array size elem => s!"[{size} x {elem.toLLVM}]"
  | .struct packed fields =>
    let fieldsStr := String.intercalate ", " (fields.toList.map toLLVM)
    if packed then s!"<\{ {fieldsStr} }>" else s!"\{ {fieldsStr} }"
  | .namedStruct name => s!"%{name}"
  | .func ret params vararg =>
    let paramsStr := String.intercalate ", " (params.toList.map toLLVM)
    let varargStr := if vararg then (if params.isEmpty then "..." else ", ...") else ""
    s!"{ret.toLLVM} ({paramsStr}{varargStr})"
  | .vector size elem => s!"<{size} x {elem.toLLVM}>"

instance : ToString LLVMType where
  toString := toLLVM

end LLVMType

/-- A local SSA value reference -/
structure LocalRef where
  id : Nat
  deriving Repr, BEq, Hashable, Inhabited

namespace LocalRef

def toLLVM (r : LocalRef) : String := s!"%{r.id}"

instance : ToString LocalRef where
  toString := toLLVM

end LocalRef

/-- A named local value (for function parameters) -/
structure NamedRef where
  name : String
  deriving Repr, BEq, Hashable, Inhabited

namespace NamedRef

def toLLVM (r : NamedRef) : String := s!"%{r.name}"

instance : ToString NamedRef where
  toString := toLLVM

end NamedRef

/-- Check if an LLVM identifier character is valid (doesn't need quoting).
    Valid characters are: letters, digits, underscore, dot, and dollar sign -/
def isValidLLVMIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '.' || c == '$' || c == '-'

/-- Check if a name needs quoting for LLVM IR.
    Names containing invalid characters (like `/`) must be quoted. -/
def needsQuoting (name : String) : Bool :=
  name.isEmpty || name.any fun c => !isValidLLVMIdentChar c

/-- Quote an LLVM name if it contains invalid characters.
    Invalid chars in quoted names are escaped. -/
def quoteIfNeeded (name : String) : String :=
  if needsQuoting name then
    -- Quote the name and escape special characters
    let escaped := name.foldl (fun acc c =>
      if c == '"' then acc ++ "\\\""
      else if c == '\\' then acc ++ "\\\\"
      else acc.push c) ""
    s!"\"{escaped}\""
  else
    name

structure GlobalRef where
  name : String
  deriving Repr, BEq, Hashable, Inhabited

namespace GlobalRef

def toLLVM (r : GlobalRef) : String := s!"@{quoteIfNeeded r.name}"

instance : ToString GlobalRef where
  toString := toLLVM

end GlobalRef

/-- A basic block label -/
structure Label where
  name : String
  deriving Repr, BEq, Hashable, Inhabited

namespace Label

def toLLVM (l : Label) : String := s!"%{l.name}"

instance : ToString Label where
  toString := toLLVM

end Label

/-- LLVM constant values -/
inductive LLVMConst where
  | int (val : Int) (bits : Nat)
  | float32 (val : Float)
  | float64 (val : Float)
  | null
  | undef (ty : LLVMType)
  | zeroinit (ty : LLVMType)
  | bool (val : Bool)
  | string (val : String)
  | array (elemTy : LLVMType) (elems : Array LLVMConst)
  | struct (packed : Bool) (elems : Array (LLVMType × LLVMConst))
  | globalRef (name : String)
  deriving Repr, Inhabited

namespace LLVMConst

partial def toLLVM : LLVMConst → String
  | .int val _bits => s!"{val}"
  | .float32 val => s!"{val}"
  | .float64 val => s!"{val}"
  | .null => "null"
  | .undef _ => "undef"
  | .zeroinit _ => "zeroinitializer"
  | .bool true => "true"
  | .bool false => "false"
  | .string s =>
    let toHex (n : Nat) : String :=
      let hexDigits := "0123456789ABCDEF".toList
      let hi := hexDigits.getD (n / 16) '0'
      let lo := hexDigits.getD (n % 16) '0'
      s!"{hi}{lo}"
    let escaped := s.foldl (fun acc c =>
      if c.toNat < 32 || c.toNat > 126 || c == '"' || c == '\\'
      then acc ++ s!"\\{toHex c.toNat}"
      else acc.push c) ""
    s!"c\"{escaped}\\00\""
  | .array elemTy elems =>
    let elemsStr := String.intercalate ", " (elems.toList.map fun e =>
      s!"{elemTy.toLLVM} {e.toLLVM}")
    s!"[{elemsStr}]"
  | .struct packed elems =>
    let elemsStr := String.intercalate ", " (elems.toList.map fun (ty, c) =>
      s!"{ty.toLLVM} {c.toLLVM}")
    if packed then s!"<\{ {elemsStr} }>" else s!"\{ {elemsStr} }"
  | .globalRef name => s!"@{name}"

instance : ToString LLVMConst where
  toString := toLLVM

end LLVMConst

/-- An LLVM value (either a reference or a constant) -/
inductive LLVMValue where
  | local (ref : LocalRef)
  | named (ref : NamedRef)
  | global (ref : GlobalRef)
  | const (c : LLVMConst)
  | label (l : Label)
  deriving Repr, Inhabited

namespace LLVMValue

def toLLVM : LLVMValue → String
  | .local ref => ref.toLLVM
  | .named ref => ref.toLLVM
  | .global ref => ref.toLLVM
  | .const c => c.toLLVM
  | .label l => l.toLLVM

instance : ToString LLVMValue where
  toString := toLLVM

/-- Create an integer constant -/
def intConst (val : Int) (bits : Nat := 64) : LLVMValue :=
  .const (.int val bits)

/-- Create a boolean constant -/
def boolConst (val : Bool) : LLVMValue :=
  .const (.bool val)

/-- Create a null pointer -/
def nullPtr : LLVMValue := .const .null

/-- Create an undef value -/
def undef (ty : LLVMType) : LLVMValue := .const (.undef ty)

end LLVMValue

/-- Integer comparison predicates -/
inductive ICmpPred where
  | eq | ne | ugt | uge | ult | ule | sgt | sge | slt | sle
  deriving Repr, BEq, Inhabited

instance : ToString ICmpPred where
  toString
    | .eq => "eq" | .ne => "ne"
    | .ugt => "ugt" | .uge => "uge" | .ult => "ult" | .ule => "ule"
    | .sgt => "sgt" | .sge => "sge" | .slt => "slt" | .sle => "sle"

/-- Float comparison predicates -/
inductive FCmpPred where
  | oeq | ogt | oge | olt | ole | one | ord
  | ueq | ugt | uge | ult | ule | une | uno
  deriving Repr, BEq, Inhabited

instance : ToString FCmpPred where
  toString
    | .oeq => "oeq" | .ogt => "ogt" | .oge => "oge" | .olt => "olt"
    | .ole => "ole" | .one => "one" | .ord => "ord"
    | .ueq => "ueq" | .ugt => "ugt" | .uge => "uge" | .ult => "ult"
    | .ule => "ule" | .une => "une" | .uno => "uno"

/-- Atomic ordering for memory operations -/
inductive AtomicOrdering where
  | unordered | monotonic | acquire | release | acqrel | seqcst
  deriving Repr, BEq, Inhabited

instance : ToString AtomicOrdering where
  toString
    | .unordered => "unordered" | .monotonic => "monotonic"
    | .acquire => "acquire" | .release => "release"
    | .acqrel => "acq_rel" | .seqcst => "seq_cst"

/-- LLVM instructions -/
inductive LLVMInst where
  -- Arithmetic operations
  | add (nuw nsw : Bool) (ty : LLVMType) (lhs rhs : LLVMValue)
  | sub (nuw nsw : Bool) (ty : LLVMType) (lhs rhs : LLVMValue)
  | mul (nuw nsw : Bool) (ty : LLVMType) (lhs rhs : LLVMValue)
  | udiv (exact : Bool) (ty : LLVMType) (lhs rhs : LLVMValue)
  | sdiv (exact : Bool) (ty : LLVMType) (lhs rhs : LLVMValue)
  | urem (ty : LLVMType) (lhs rhs : LLVMValue)
  | srem (ty : LLVMType) (lhs rhs : LLVMValue)
  -- Floating point operations
  | fadd (ty : LLVMType) (lhs rhs : LLVMValue)
  | fsub (ty : LLVMType) (lhs rhs : LLVMValue)
  | fmul (ty : LLVMType) (lhs rhs : LLVMValue)
  | fdiv (ty : LLVMType) (lhs rhs : LLVMValue)
  | frem (ty : LLVMType) (lhs rhs : LLVMValue)
  | fneg (ty : LLVMType) (val : LLVMValue)
  -- Bitwise operations
  | shl (nuw nsw : Bool) (ty : LLVMType) (lhs rhs : LLVMValue)
  | lshr (exact : Bool) (ty : LLVMType) (lhs rhs : LLVMValue)
  | ashr (exact : Bool) (ty : LLVMType) (lhs rhs : LLVMValue)
  | and_ (ty : LLVMType) (lhs rhs : LLVMValue)
  | or_ (ty : LLVMType) (lhs rhs : LLVMValue)
  | xor_ (ty : LLVMType) (lhs rhs : LLVMValue)
  -- Comparisons
  | icmp (pred : ICmpPred) (ty : LLVMType) (lhs rhs : LLVMValue)
  | fcmp (pred : FCmpPred) (ty : LLVMType) (lhs rhs : LLVMValue)
  -- Conversions
  | trunc (fromTy toTy : LLVMType) (val : LLVMValue)
  | zext (fromTy toTy : LLVMType) (val : LLVMValue)
  | sext (fromTy toTy : LLVMType) (val : LLVMValue)
  | fptrunc (fromTy toTy : LLVMType) (val : LLVMValue)
  | fpext (fromTy toTy : LLVMType) (val : LLVMValue)
  | fptoui (fromTy toTy : LLVMType) (val : LLVMValue)
  | fptosi (fromTy toTy : LLVMType) (val : LLVMValue)
  | uitofp (fromTy toTy : LLVMType) (val : LLVMValue)
  | sitofp (fromTy toTy : LLVMType) (val : LLVMValue)
  | ptrtoint (fromTy toTy : LLVMType) (val : LLVMValue)
  | inttoptr (fromTy toTy : LLVMType) (val : LLVMValue)
  | bitcast (fromTy toTy : LLVMType) (val : LLVMValue)
  -- Memory operations
  | alloca (ty : LLVMType) (numElems : Option LLVMValue) (align : Option Nat)
  | load (ty : LLVMType) (ptr : LLVMValue) (align : Option Nat)
  | store (ty : LLVMType) (val ptr : LLVMValue) (align : Option Nat)
  | getelementptr (inbounds : Bool) (baseTy : LLVMType) (ptr : LLVMValue)
                  (indices : Array (LLVMType × LLVMValue))
  -- Aggregate operations
  | extractvalue (aggTy : LLVMType) (agg : LLVMValue) (indices : Array Nat)
  | insertvalue (aggTy : LLVMType) (agg val : LLVMValue) (indices : Array Nat)
  -- Function calls
  | call (tailcall : Bool) (callconv : Option CallConv) (retTy : LLVMType)
         (func : LLVMValue) (args : Array (LLVMType × LLVMValue))
  -- Select and phi
  | select (condTy resTy : LLVMType) (cond thenVal elseVal : LLVMValue)
  | phi (ty : LLVMType) (incoming : Array (LLVMValue × Label))
  -- Memory intrinsics
  | memcpy (dst src len : LLVMValue) (align : Nat) (isVolatile : Bool)
  | memset (dst val len : LLVMValue) (align : Nat) (isVolatile : Bool)
  | memmove (dst src len : LLVMValue) (align : Nat) (isVolatile : Bool)

  deriving Repr, Inhabited

namespace LLVMInst

/-- Convert instruction to LLVM IR syntax -/
partial def toLLVM : LLVMInst → String
  | .add nuw nsw ty lhs rhs =>
    let flags := (if nuw then "nuw " else "") ++ (if nsw then "nsw " else "")
    s!"add {flags}{ty} {lhs}, {rhs}"
  | .sub nuw nsw ty lhs rhs =>
    let flags := (if nuw then "nuw " else "") ++ (if nsw then "nsw " else "")
    s!"sub {flags}{ty} {lhs}, {rhs}"
  | .mul nuw nsw ty lhs rhs =>
    let flags := (if nuw then "nuw " else "") ++ (if nsw then "nsw " else "")
    s!"mul {flags}{ty} {lhs}, {rhs}"
  | .udiv exact ty lhs rhs =>
    let flag := if exact then "exact " else ""
    s!"udiv {flag}{ty} {lhs}, {rhs}"
  | .sdiv exact ty lhs rhs =>
    let flag := if exact then "exact " else ""
    s!"sdiv {flag}{ty} {lhs}, {rhs}"
  | .urem ty lhs rhs => s!"urem {ty} {lhs}, {rhs}"
  | .srem ty lhs rhs => s!"srem {ty} {lhs}, {rhs}"

  | .fadd ty lhs rhs => s!"fadd {ty} {lhs}, {rhs}"
  | .fsub ty lhs rhs => s!"fsub {ty} {lhs}, {rhs}"
  | .fmul ty lhs rhs => s!"fmul {ty} {lhs}, {rhs}"
  | .fdiv ty lhs rhs => s!"fdiv {ty} {lhs}, {rhs}"
  | .frem ty lhs rhs => s!"frem {ty} {lhs}, {rhs}"
  | .fneg ty val => s!"fneg {ty} {val}"

  | .shl nuw nsw ty lhs rhs =>
    let flags := (if nuw then "nuw " else "") ++ (if nsw then "nsw " else "")
    s!"shl {flags}{ty} {lhs}, {rhs}"
  | .lshr exact ty lhs rhs =>
    let flag := if exact then "exact " else ""
    s!"lshr {flag}{ty} {lhs}, {rhs}"
  | .ashr exact ty lhs rhs =>
    let flag := if exact then "exact " else ""
    s!"ashr {flag}{ty} {lhs}, {rhs}"
  | .and_ ty lhs rhs => s!"and {ty} {lhs}, {rhs}"
  | .or_ ty lhs rhs => s!"or {ty} {lhs}, {rhs}"
  | .xor_ ty lhs rhs => s!"xor {ty} {lhs}, {rhs}"

  | .icmp pred ty lhs rhs => s!"icmp {pred} {ty} {lhs}, {rhs}"
  | .fcmp pred ty lhs rhs => s!"fcmp {pred} {ty} {lhs}, {rhs}"

  | .trunc fromTy toTy val => s!"trunc {fromTy} {val} to {toTy}"
  | .zext fromTy toTy val => s!"zext {fromTy} {val} to {toTy}"
  | .sext fromTy toTy val => s!"sext {fromTy} {val} to {toTy}"
  | .fptrunc fromTy toTy val => s!"fptrunc {fromTy} {val} to {toTy}"
  | .fpext fromTy toTy val => s!"fpext {fromTy} {val} to {toTy}"
  | .fptoui fromTy toTy val => s!"fptoui {fromTy} {val} to {toTy}"
  | .fptosi fromTy toTy val => s!"fptosi {fromTy} {val} to {toTy}"
  | .uitofp fromTy toTy val => s!"uitofp {fromTy} {val} to {toTy}"
  | .sitofp fromTy toTy val => s!"sitofp {fromTy} {val} to {toTy}"
  | .ptrtoint fromTy toTy val => s!"ptrtoint {fromTy} {val} to {toTy}"
  | .inttoptr fromTy toTy val => s!"inttoptr {fromTy} {val} to {toTy}"
  | .bitcast fromTy toTy val => s!"bitcast {fromTy} {val} to {toTy}"

  | .alloca ty numElems align =>
    let numStr := match numElems with
      | some n => s!", i64 {n}"
      | none => ""
    let alignStr := match align with
      | some a => s!", align {a}"
      | none => ""
    s!"alloca {ty}{numStr}{alignStr}"
  | .load ty ptr align =>
    let alignStr := match align with
      | some a => s!", align {a}"
      | none => ""
    s!"load {ty}, ptr {ptr}{alignStr}"
  | .store ty val ptr align =>
    let alignStr := match align with
      | some a => s!", align {a}"
      | none => ""
    s!"store {ty} {val}, ptr {ptr}{alignStr}"
  | .getelementptr inbounds baseTy ptr indices =>
    let ibStr := if inbounds then "inbounds " else ""
    let indicesStr := String.intercalate ", " (indices.toList.map fun (ty, idx) =>
      s!"{ty} {idx}")
    s!"getelementptr {ibStr}{baseTy}, ptr {ptr}, {indicesStr}"

  | .extractvalue aggTy agg indices =>
    let indicesStr := String.intercalate ", " (indices.toList.map ToString.toString)
    s!"extractvalue {aggTy} {agg}, {indicesStr}"
  | .insertvalue aggTy agg val indices =>
    let indicesStr := String.intercalate ", " (indices.toList.map ToString.toString)
    s!"insertvalue {aggTy} {agg}, {val}, {indicesStr}"

  | .call tailcall callconv retTy func args =>
    let tailStr := if tailcall then "tail " else ""
    let convStr := match callconv with
      | some cc => s!"{cc} "
      | none => ""
    let argsStr := String.intercalate ", " (args.toList.map fun (ty, v) =>
      s!"{ty} {v}")
    s!"{tailStr}call {convStr}{retTy} {func}({argsStr})"

  | .select condTy resTy cond thenVal elseVal =>
    s!"select {condTy} {cond}, {resTy} {thenVal}, {resTy} {elseVal}"
  | .phi ty incoming =>
    let pairsStr := String.intercalate ", " (incoming.toList.map fun (v, l) =>
      s!"[ {v}, {l} ]")
    s!"phi {ty} {pairsStr}"

  | .memcpy dst src len _align isVolatile =>
    let volStr := if isVolatile then "true" else "false"
    s!"call void @llvm.memcpy.p0.p0.i64(ptr {dst}, ptr {src}, i64 {len}, i1 {volStr})"
  | .memset dst val len _align isVolatile =>
    let volStr := if isVolatile then "true" else "false"
    s!"call void @llvm.memset.p0.i64(ptr {dst}, i8 {val}, i64 {len}, i1 {volStr})"
  | .memmove dst src len _align isVolatile =>
    let volStr := if isVolatile then "true" else "false"
    s!"call void @llvm.memmove.p0.p0.i64(ptr {dst}, ptr {src}, i64 {len}, i1 {volStr})"

instance : ToString LLVMInst where
  toString := toLLVM

end LLVMInst

/-- LLVM terminator instructions -/
inductive LLVMTerminator where
  | ret (ty : LLVMType) (val : Option LLVMValue)
  | br (target : Label)
  | condBr (cond : LLVMValue) (thenLabel elseLabel : Label)
  | switch (ty : LLVMType) (val : LLVMValue) (default : Label)
           (cases : Array (LLVMConst × Label))
  | unreachable
  deriving Repr, Inhabited

namespace LLVMTerminator

def toLLVM : LLVMTerminator → String
  | .ret ty val =>
    match val with
    | some v => s!"ret {ty} {v}"
    | none => "ret void"
  | .br target => s!"br label {target}"
  | .condBr cond thenL elseL =>
    s!"br i1 {cond}, label {thenL}, label {elseL}"
  | .switch ty val default cases =>
    let casesStr := String.intercalate "\n    " (cases.toList.map fun (c, l) =>
      s!"{ty} {c}, label {l}")
    s!"switch {ty} {val}, label {default} [\n    {casesStr}\n  ]"
  | .unreachable => "unreachable"

instance : ToString LLVMTerminator where
  toString := toLLVM

end LLVMTerminator

/-- A statement is an instruction with an optional result assignment -/
structure LLVMStmt where
  result : Option LocalRef
  inst : LLVMInst
  deriving Repr, Inhabited

namespace LLVMStmt

def toLLVM (s : LLVMStmt) : String :=
  match s.result with
  | some r => s!"{r} = {s.inst}"
  | none => s!"{s.inst}"

/-- Check if this statement is a phi instruction -/
def isPhi (s : LLVMStmt) : Bool :=
  match s.inst with
  | .phi _ _ => true
  | _ => false

instance : ToString LLVMStmt where
  toString := toLLVM

end LLVMStmt

/-- An LLVM basic block -/
structure LLVMBlock where
  label : Label
  stmts : Array LLVMStmt := #[]
  terminator : LLVMTerminator
  deriving Repr, Inhabited

namespace LLVMBlock

def toLLVM (b : LLVMBlock) : String :=
  -- LLVM requires phi nodes to be at the beginning of a basic block
  let (phis, nonPhis) := b.stmts.partition LLVMStmt.isPhi
  let sortedStmts := phis ++ nonPhis
  let stmtsStr := if sortedStmts.isEmpty then ""
    else "\n  " ++ String.intercalate "\n  " (sortedStmts.toList.map LLVMStmt.toLLVM)
  s!"{b.label.name}:{stmtsStr}\n  {b.terminator}"

instance : ToString LLVMBlock where
  toString := toLLVM

end LLVMBlock

/-- An LLVM function parameter -/
structure LLVMParam where
  name : String
  ty : LLVMType
  attrs : Array String := #[]
  deriving Repr, Inhabited

namespace LLVMParam

def toLLVM (p : LLVMParam) : String :=
  let attrsStr := if p.attrs.isEmpty then ""
    else " " ++ String.intercalate " " p.attrs.toList
  s!"{p.ty}{attrsStr} %{p.name}"

instance : ToString LLVMParam where
  toString := toLLVM

end LLVMParam

/-- Function attributes -/
structure LLVMFuncAttrs where
  linkage : Linkage := .external
  callconv : Option CallConv := none
  nounwind : Bool := false
  noreturn : Bool := false
  readonly : Bool := false
  alwaysInline : Bool := false
  noInline : Bool := false
  deriving Repr, Inhabited

namespace LLVMFuncAttrs

def toLLVM (a : LLVMFuncAttrs) : String :=
  let parts : List String := []
  let parts := if a.nounwind then parts ++ ["nounwind"] else parts
  let parts := if a.noreturn then parts ++ ["noreturn"] else parts
  let parts := if a.readonly then parts ++ ["readonly"] else parts
  let parts := if a.alwaysInline then parts ++ ["alwaysinline"] else parts
  let parts := if a.noInline then parts ++ ["noinline"] else parts
  if parts.isEmpty then "" else " " ++ String.intercalate " " parts

instance : ToString LLVMFuncAttrs where
  toString := toLLVM

end LLVMFuncAttrs

/-- An LLVM function -/
structure LLVMFunc where
  name : String
  retTy : LLVMType
  params : Array LLVMParam
  attrs : LLVMFuncAttrs := {}
  blocks : Array LLVMBlock := #[]
  isDeclaration : Bool := false
  deriving Repr, Inhabited

namespace LLVMFunc

def toLLVM (f : LLVMFunc) : String :=
  let linkageStr := match f.attrs.linkage with
    | .external => ""
    | l => s!"{l} "
  let defOrDecl := if f.isDeclaration then "declare" else "define"
  let paramsStr := String.intercalate ", " (f.params.toList.map LLVMParam.toLLVM)
  let quotedName := quoteIfNeeded f.name

  if f.isDeclaration then
    s!"{defOrDecl} {linkageStr}{f.retTy} @{quotedName}({paramsStr}){f.attrs}"
  else
    let blocksStr := String.intercalate "\n" (f.blocks.toList.map LLVMBlock.toLLVM)
    s!"{defOrDecl} {linkageStr}{f.retTy} @{quotedName}({paramsStr}){f.attrs} \{\n{blocksStr}\n}"

instance : ToString LLVMFunc where
  toString := toLLVM

end LLVMFunc

/-- An LLVM global variable -/
structure LLVMGlobal where
  name : String
  ty : LLVMType
  init : Option LLVMConst := none
  linkage : Linkage := .external
  isConstant : Bool := false
  align : Option Nat := none
  deriving Repr, Inhabited

namespace LLVMGlobal

def toLLVM (g : LLVMGlobal) : String :=
  let linkageStr := match g.linkage with
    | .external => ""
    | l => s!"{l} "
  let constStr := if g.isConstant then "constant" else "global"
  let initStr := match g.init with
    | some c => s!" {c}"
    | none => " zeroinitializer"
  let alignStr := match g.align with
    | some a => s!", align {a}"
    | none => ""
  let quotedName := quoteIfNeeded g.name
  s!"@{quotedName} = {linkageStr}{constStr} {g.ty}{initStr}{alignStr}"

instance : ToString LLVMGlobal where
  toString := toLLVM

end LLVMGlobal

/-- A named struct type definition -/
structure LLVMTypeDef where
  name : String
  fields : Array LLVMType
  packed : Bool := false
  deriving Repr, Inhabited

namespace LLVMTypeDef

def toLLVM (td : LLVMTypeDef) : String :=
  let fieldsStr := String.intercalate ", " (td.fields.toList.map LLVMType.toLLVM)
  let bodyStr := if td.packed then s!"<\{ {fieldsStr} }>" else s!"\{ {fieldsStr} }"
  s!"%{td.name} = type {bodyStr}"

instance : ToString LLVMTypeDef where
  toString := toLLVM

end LLVMTypeDef

/-- An LLVM module -/
structure LLVMModule where
  name : String
  targetTriple : Option String := none
  dataLayout : Option String := none
  types : Array LLVMTypeDef := #[]
  globals : Array LLVMGlobal := #[]
  funcs : Array LLVMFunc := #[]
  deriving Repr, Inhabited

namespace LLVMModule

def toLLVM (m : LLVMModule) : String :=
  let headerParts : List String := []
  let headerParts := match m.targetTriple with
    | some t => headerParts ++ [s!"target triple = \"{t}\""]
    | none => headerParts
  let headerParts := match m.dataLayout with
    | some d => headerParts ++ [s!"target datalayout = \"{d}\""]
    | none => headerParts
  let headerStr := if headerParts.isEmpty then ""
    else String.intercalate "\n" headerParts ++ "\n\n"

  let typesStr := if m.types.isEmpty then ""
    else String.intercalate "\n" (m.types.toList.map LLVMTypeDef.toLLVM) ++ "\n\n"

  let globalsStr := if m.globals.isEmpty then ""
    else String.intercalate "\n" (m.globals.toList.map LLVMGlobal.toLLVM) ++ "\n\n"

  let funcsStr := String.intercalate "\n\n" (m.funcs.toList.map LLVMFunc.toLLVM)

  s!"; ModuleID = '{m.name}'\n{headerStr}{typesStr}{globalsStr}{funcsStr}"

instance : ToString LLVMModule where
  toString := toLLVM

end LLVMModule

end Somac.Llvm
