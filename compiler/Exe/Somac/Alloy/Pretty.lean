import Somac.Alloy.Func

namespace Somac.Alloy.Pretty

open Somac.Alloy

/-! ## Configuration -/

/-- Pretty printing configuration -/
structure Config where
  /-- Indentation width -/
  indent : Nat := 2
  /-- Show types on all values -/
  showTypes : Bool := true
  /-- Maximum line width -/
  maxWidth : Nat := 100
  /-- Use colors (ANSI escape codes) -/
  useColors : Bool := false
  deriving Repr, Inhabited

def Config.default : Config := {}

/-! ## Color Helpers -/

def colorKeyword (cfg : Config) (s : String) : String :=
  if cfg.useColors then s!"\x1b[1;34m{s}\x1b[0m" else s

def colorType (cfg : Config) (s : String) : String :=
  if cfg.useColors then s!"\x1b[33m{s}\x1b[0m" else s

def colorLocal (cfg : Config) (s : String) : String :=
  if cfg.useColors then s!"\x1b[36m{s}\x1b[0m" else s

def colorConst (cfg : Config) (s : String) : String :=
  if cfg.useColors then s!"\x1b[32m{s}\x1b[0m" else s

def colorLabel (cfg : Config) (s : String) : String :=
  if cfg.useColors then s!"\x1b[35m{s}\x1b[0m" else s

def colorComment (cfg : Config) (s : String) : String :=
  if cfg.useColors then s!"\x1b[90m{s}\x1b[0m" else s

/-! ## Type Formatting -/

partial def ppTy (cfg : Config) : Ty n → String
  | .prim p => colorType cfg (ToString.toString p)
  | .ptr t => s!"*{ppTy cfg t}"
  | .rawPtr => colorType cfg "ptr"
  | .funcPtr args ret =>
    let argsStr := String.intercalate ", " (args.toList.map (ppTy cfg))
    s!"{colorKeyword cfg "fn"}({argsStr}) -> {ppTy cfg ret}"
  | .struct fields =>
    let fieldsStr := String.intercalate ", " (fields.toList.map fun (n, t) =>
      s!"{n}: {ppTy cfg t}")
    s!"\{{fieldsStr}}"
  | .array elem size => s!"[{ppTy cfg elem}; {size}]"
  | .tagged tag variants =>
    let varStr := String.intercalate " | " (variants.toList.map fun (i, ts) =>
      let tsStr := String.intercalate ", " (ts.toList.map (ppTy cfg))
      s!"{i}({tsStr})")
    s!"{colorKeyword cfg "tagged"}<{ppTy cfg tag}>[{varStr}]"
  | .closure args ret =>
    let argsStr := String.intercalate ", " (args.toList.map (ppTy cfg))
    s!"{colorKeyword cfg "closure"}({argsStr}) -> {ppTy cfg ret}"
  | .var i => colorType cfg s!"α{i.val}"

/-! ## Value Formatting -/

def ppLocalId (cfg : Config) (id : LocalId) : String :=
  colorLocal cfg s!"%{id.id}"

def ppBlockId (cfg : Config) (id : BlockId) : String :=
  colorLabel cfg s!"bb{id.id}"

def ppFuncId (cfg : Config) (id : FuncId) : String :=
  colorLabel cfg s!"@fn{id.id}"

def ppFuncRef (cfg : Config) (ref : FuncRef) : String :=
  match ref with
  | .local id => ppFuncId cfg id
  | .external name => colorLabel cfg s!"@extern\"{name}\""
  | .intrinsic op => colorLabel cfg s!"@intrinsic.{op}"
  | .primOp op => colorLabel cfg s!"@primop.{op}"
  | .externC name => colorLabel cfg s!"@externc\"{name}\""

def ppGlobalId (cfg : Config) (id : GlobalId) : String :=
  colorLabel cfg s!"@g{id.id}"

def ppConst (cfg : Config) : Const → String
  | .int v t => colorConst cfg s!"{v}_{t}"
  | .float v t => colorConst cfg s!"{v}_{t}"
  | .bool b => colorConst cfg (if b then "true" else "false")
  | .unit => colorConst cfg "()"
  | .null _ => colorConst cfg "null"
  | .string idx len => colorConst cfg s!"str#{idx}[{len}]"
  | .undef t => s!"{colorKeyword cfg "undef"}:{ppTy cfg t}"

def ppOperand (cfg : Config) : Operand → String
  | .local id => ppLocalId cfg id
  | .const c => ppConst cfg c
  | .global id => ppGlobalId cfg id
  | .func id => ppFuncId cfg id

/-! ## Instruction Formatting -/

def ppBinOp (cfg : Config) : BinOp → String
  | .add => colorKeyword cfg "add"
  | .sub => colorKeyword cfg "sub"
  | .mul => colorKeyword cfg "mul"
  | .div => colorKeyword cfg "div"
  | .rem => colorKeyword cfg "rem"
  | .and => colorKeyword cfg "and"
  | .or => colorKeyword cfg "or"
  | .xor => colorKeyword cfg "xor"
  | .shl => colorKeyword cfg "shl"
  | .shr => colorKeyword cfg "shr"
  | .eq => colorKeyword cfg "eq"
  | .ne => colorKeyword cfg "ne"
  | .lt => colorKeyword cfg "lt"
  | .le => colorKeyword cfg "le"
  | .gt => colorKeyword cfg "gt"
  | .ge => colorKeyword cfg "ge"

def ppUnOp (cfg : Config) : UnOp n → String
  | .neg => colorKeyword cfg "neg"
  | .not => colorKeyword cfg "not"
  | .trunc t => s!"{colorKeyword cfg "trunc"}.{t}"
  | .zext t => s!"{colorKeyword cfg "zext"}.{t}"
  | .sext t => s!"{colorKeyword cfg "sext"}.{t}"
  | .itof t => s!"{colorKeyword cfg "itof"}.{t}"
  | .ftoi t => s!"{colorKeyword cfg "ftoi"}.{t}"
  | .bitcast t => s!"{colorKeyword cfg "bitcast"}.{ppTy cfg t}"
  | .ptrtoint t => s!"{colorKeyword cfg "ptrtoint"}.{t}"
  | .inttoptr => colorKeyword cfg "inttoptr"

def ppInst (cfg : Config) : Inst n → String
  | .binOp op lhs rhs ty =>
    s!"{ppBinOp cfg op} {ppTy cfg ty} {ppOperand cfg lhs}, {ppOperand cfg rhs}"
  | .unOp op operand =>
    s!"{ppUnOp cfg op} {ppOperand cfg operand}"
  | .copy src =>
    s!"{colorKeyword cfg "copy"} {ppOperand cfg src}"
  | .alloca ty =>
    s!"{colorKeyword cfg "alloca"} {ppTy cfg ty}"
  | .malloc size =>
    s!"{colorKeyword cfg "malloc"} {ppOperand cfg size}"
  | .free ptr =>
    s!"{colorKeyword cfg "free"} {ppOperand cfg ptr}"
  | .load ptr ty =>
    s!"{colorKeyword cfg "load"} {ppTy cfg ty}, {ppOperand cfg ptr}"
  | .store ptr val =>
    s!"{colorKeyword cfg "store"} {ppOperand cfg ptr}, {ppOperand cfg val}"
  | .getFieldPtr base idx _ =>
    s!"{colorKeyword cfg "getfieldptr"} {ppOperand cfg base}, {idx}"
  | .getElemPtr base idx _ =>
    s!"{colorKeyword cfg "getelemptr"} {ppOperand cfg base}, {ppOperand cfg idx}"
  | .extractField val idx =>
    s!"{colorKeyword cfg "extractfield"} {ppOperand cfg val}, {idx}"
  | .insertField val idx newVal =>
    s!"{colorKeyword cfg "insertfield"} {ppOperand cfg val}, {idx}, {ppOperand cfg newVal}"
  | .extractElem val idx =>
    s!"{colorKeyword cfg "extractelem"} {ppOperand cfg val}, {ppOperand cfg idx}"
  | .insertElem val idx newVal =>
    s!"{colorKeyword cfg "insertelem"} {ppOperand cfg val}, {ppOperand cfg idx}, {ppOperand cfg newVal}"
  | .structLit fields ty =>
    let fs := String.intercalate ", " (fields.toList.map (ppOperand cfg))
    s!"{colorKeyword cfg "struct"} {ppTy cfg ty} \{{fs}}"
  | .arrayLit elems elemTy =>
    let es := String.intercalate ", " (elems.toList.map (ppOperand cfg))
    s!"{colorKeyword cfg "array"} [{ppTy cfg elemTy}] [{es}]"
  | .getTag val =>
    s!"{colorKeyword cfg "gettag"} {ppOperand cfg val}"
  | .getPayload val variant field ty =>
    s!"{colorKeyword cfg "getpayload"} {ppOperand cfg val}, {variant}, {field} : {ppTy cfg ty}"
  | .taggedLit tag payload ty =>
    let ps := String.intercalate ", " (payload.toList.map (ppOperand cfg))
    s!"{colorKeyword cfg "tagged"} {ppTy cfg ty} {tag}({ps})"
  | .call func args retTy =>
    let as := String.intercalate ", " (args.toList.map (ppOperand cfg))
    s!"{colorKeyword cfg "call"} {ppTy cfg retTy} {ppFuncId cfg func}({as})"
  | .callIndirect ptr args retTy =>
    let as := String.intercalate ", " (args.toList.map (ppOperand cfg))
    s!"{colorKeyword cfg "call.indirect"} {ppTy cfg retTy} {ppOperand cfg ptr}({as})"
  | .callClosure closure args retTy =>
    let as := String.intercalate ", " (args.toList.map (ppOperand cfg))
    s!"{colorKeyword cfg "call.closure"} {ppTy cfg retTy} {ppOperand cfg closure}({as})"
  | .makeClosure func env =>
    s!"{colorKeyword cfg "makeclosure"} {ppFuncRef cfg func}, {ppOperand cfg env}"
  | .makeClosurePoly func typeArgs env =>
    let tyArgsStr := String.intercalate ", " (typeArgs.toList.map (ppTy cfg))
    s!"{colorKeyword cfg "makeclosure.poly"} {ppFuncRef cfg func}<{tyArgsStr}>, {ppOperand cfg env}"
  | .callPoly func typeArgs args retTy =>
    let tyArgsStr := String.intercalate ", " (typeArgs.toList.map (ppTy cfg))
    let argsStr := String.intercalate ", " (args.toList.map (ppOperand cfg))
    s!"{colorKeyword cfg "call.poly"} {ppTy cfg retTy} {ppFuncId cfg func}<{tyArgsStr}>({argsStr})"
  | .closureFunc closure =>
    s!"{colorKeyword cfg "closure.func"} {ppOperand cfg closure}"
  | .closureEnv closure =>
    s!"{colorKeyword cfg "closure.env"} {ppOperand cfg closure}"
  | .phi incoming ty =>
    let is := String.intercalate ", " (incoming.toList.map fun (v, b) =>
      s!"[{ppOperand cfg v}, {ppBlockId cfg b}]")
    s!"{colorKeyword cfg "phi"} {ppTy cfg ty} {is}"
  | .select cond t e =>
    s!"{colorKeyword cfg "select"} {ppOperand cfg cond}, {ppOperand cfg t}, {ppOperand cfg e}"
  | .memcpy dst src size =>
    s!"{colorKeyword cfg "memcpy"} {ppOperand cfg dst}, {ppOperand cfg src}, {ppOperand cfg size}"
  | .memset dst val size =>
    s!"{colorKeyword cfg "memset"} {ppOperand cfg dst}, {ppOperand cfg val}, {ppOperand cfg size}"
  | .clone src ty =>
    s!"{colorKeyword cfg "clone"} {ppTy cfg ty} {ppOperand cfg src}"
  | .erase val ty =>
    s!"{colorKeyword cfg "erase"} {ppTy cfg ty} {ppOperand cfg val}"
  | .panic msgIdx line =>
    s!"{colorKeyword cfg "panic"} #{msgIdx} @ line {line}"
  | .callIntrinsic op args retTy =>
    let as := String.intercalate ", " (args.toList.map (ppOperand cfg))
    s!"{colorKeyword cfg "call.intrinsic"} {ppTy cfg retTy} {op}({as})"
  | .callExtern name args retTy =>
    let as := String.intercalate ", " (args.toList.map (ppOperand cfg))
    s!"{colorKeyword cfg "call.extern"} {ppTy cfg retTy} \"{name}\"({as})"

/-! ## Terminator Formatting -/

def ppTerminator (cfg : Config) : Terminator → String
  | .jump target =>
    s!"{colorKeyword cfg "jump"} {ppBlockId cfg target}"
  | .branch cond thenB elseB =>
    s!"{colorKeyword cfg "br"} {ppOperand cfg cond}, {ppBlockId cfg thenB}, {ppBlockId cfg elseB}"
  | .switch val cases default =>
    let cs := String.intercalate ", " (cases.toList.map fun (v, b) =>
      s!"{v} => {ppBlockId cfg b}")
    s!"{colorKeyword cfg "switch"} {ppOperand cfg val} [{cs}] {colorKeyword cfg "default"} {ppBlockId cfg default}"
  | .ret val =>
    s!"{colorKeyword cfg "ret"} {ppOperand cfg val}"
  | .retUnit =>
    colorKeyword cfg "ret"
  | .unreachable =>
    colorKeyword cfg "unreachable"

/-! ## Statement Formatting -/

def ppStmt (cfg : Config) : Stmt n → String
  | ⟨some result, inst⟩ => s!"{ppLocalId cfg result} = {ppInst cfg inst}"
  | ⟨none, inst⟩ => ppInst cfg inst

/-! ## Block Formatting -/

def ppBlock (cfg : Config) (b : Block n) : String :=
  let labelStr := match b.label with
    | some l => colorComment cfg s!" ; {l}"
    | none => ""

  let paramsStr := if b.params.isEmpty then ""
    else
      let ps := String.intercalate ", " (b.params.toList.map fun (p, t) =>
        s!"{ppLocalId cfg p}: {ppTy cfg t}")
      s!"({ps})"

  let header := s!"{ppBlockId cfg b.id}{paramsStr}:{labelStr}"

  let stmtsStr := if b.stmts.isEmpty then ""
    else
      let indent := String.ofList (List.replicate cfg.indent ' ')
      let stmts := b.stmts.toList.map fun s => s!"{indent}{ppStmt cfg s}"
      "\n" ++ String.intercalate "\n" stmts

  let indent := String.ofList (List.replicate cfg.indent ' ')
  let termStr := s!"\n{indent}{ppTerminator cfg b.terminator}"

  s!"{header}{stmtsStr}{termStr}"

/-! ## Function Formatting -/

def ppSignature (cfg : Config) (sig : Signature n) : String :=
  let paramsStr := String.intercalate ", " (sig.params.toList.map fun p =>
    s!"{ppLocalId cfg p.id}: {ppTy cfg p.ty}")
  let closureStr := if sig.isClosure then s!" {colorComment cfg "[closure]"}" else ""
  s!"{colorKeyword cfg "fn"} @{sig.name}({paramsStr}) -> {ppTy cfg sig.retTy}{closureStr}"

def ppFuncAttrs (cfg : Config) (attrs : FuncAttrs) : String :=
  let attrList : List String := []
  let attrList := if attrs.inline then attrList ++ [colorKeyword cfg "inline"] else attrList
  let attrList := if attrs.noInline then attrList ++ [colorKeyword cfg "noinline"] else attrList
  let attrList := match attrs.extern with
    | some name => attrList ++ [s!"{colorKeyword cfg "extern"}(\"{name}\")"]
    | none => attrList
  let attrList := if attrs.pure then attrList ++ [colorKeyword cfg "pure"] else attrList
  let attrList := if attrs.tailCall then attrList ++ [colorKeyword cfg "tailcall"] else attrList
  if attrList.isEmpty then "" else s!"[{String.intercalate ", " attrList}] "

def ppFunc (cfg : Config) (f : Func n) : String :=
  let attrsStr := ppFuncAttrs cfg f.attrs
  let sigStr := ppSignature cfg f.sig
  match f.body with
  | none => s!"{attrsStr}{sigStr}"
  | some cfgBody =>
    let blocksStr := String.intercalate "\n\n" (cfgBody.allBlocks.toList.map (ppBlock cfg))
    s!"{attrsStr}{sigStr} \{\n{blocksStr}\n}"

/-! ## Global Formatting -/

def ppGlobal (cfg : Config) (g : Global) : String :=
  let mutStr := if g.mutable then colorKeyword cfg "var" else colorKeyword cfg "const"
  let initStr := match g.init with
    | some c => s!" = {ppConst cfg c}"
    | none => ""
  s!"{mutStr} {ppGlobalId cfg g.id} @{g.name}: {ppTy cfg g.ty}{initStr}"

/-! ## Type Definition Formatting -/

def ppTypeDef (cfg : Config) (td : TypeDef) : String :=
  s!"{colorKeyword cfg "type"} @{td.name} = {ppTy cfg td.ty}"

/-! ## Module Formatting -/

def ppSomeFunc (cfg : Config) (sf : SomeFunc) : String :=
  let ⟨_, f⟩ := sf
  ppFunc cfg f

def ppModule (cfg : Config := .default) (m : Module) : String :=
  let header := colorComment cfg s!"; Alloy IR Module: {m.name}\n"

  let typesStr := if m.types.isEmpty then ""
    else
      let ts := String.intercalate "\n" (m.types.toList.map (ppTypeDef cfg))
      s!"\n{colorComment cfg "; Types"}\n{ts}\n"

  let globalsStr := if m.globals.isEmpty then ""
    else
      let gs := String.intercalate "\n" (m.globals.toList.map (ppGlobal cfg))
      s!"\n{colorComment cfg "; Globals"}\n{gs}\n"

  let funcsStr := String.intercalate "\n\n" (m.funcs.toList.map (ppSomeFunc cfg))
  let funcsSection := s!"\n{colorComment cfg "; Functions"}\n{funcsStr}"

  let mainStr := match m.mainFunc with
    | some id => s!"\n\n{colorComment cfg s!"; main = {id}"}"
    | none => ""

  s!"{header}{typesStr}{globalsStr}{funcsSection}{mainStr}"

/-! ## Public API -/

/-- Pretty print a module with default config -/
def pp (m : Module) : String := ppModule .default m

/-- Pretty print a module with colors -/
def ppColored (m : Module) : String := ppModule { useColors := true } m

/-- Pretty print a function -/
def ppFn (f : Func n) : String := ppFunc .default f

/-- Pretty print a block -/
def ppBb (b : Block n) : String := ppBlock .default b

end Somac.Alloy.Pretty
