import Lean.Data.Json
import Soma.Project
import Soma.Project.Check
import Soma.Unique
import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Quantity
import Soma.Core.Primitive
import Soma.Core.TypeId
import Soma.Dependent.Monad

namespace Soma.Project.MetadataLoad

open Soma
open Soma.Project
open Soma.Syntax (Span)
open Soma.Core
open Soma.Check (ExternalDependency CheckError)
open Soma.Dependent (Globals GlobalInfo InstanceEnv InstanceInfo ClassInfo AbbrevEnv AbbrevInfo)

/-! # Metadata JSON Loading

Parse metadata JSON back into compiler types for dependency loading.
This module handles deserialization of Core.Value and related dependent type structures.
-/

-- Note: Level, Quantity, BinderInfo, TypeId, Unique have FromJson instances
-- defined in their respective modules. We use those directly.

/-- Parse a Level from JSON using derived instance -/
def levelFromJson (j : Lean.Json) : Except String Level :=
  Lean.FromJson.fromJson? j

/-- Parse a Quantity from JSON using derived instance -/
def quantityFromJson (j : Lean.Json) : Except String Quantity :=
  Lean.FromJson.fromJson? j

/-- Parse a BinderInfo from JSON using derived instance -/
def binderInfoFromJson (j : Lean.Json) : Except String Soma.Metal.BinderInfo :=
  Lean.FromJson.fromJson? j

/-- Parse a StarPrimitive from JSON -/
def starPrimitiveFromJson (j : Lean.Json) : Except String StarPrimitive := do
  match j with
  | .str name =>
    match StarPrimitive.fromName? name with
    | some p => pure p
    | none => .error s!"Unknown star primitive: {name}"
  | _ => .error s!"Invalid star primitive JSON: {j}"

/-- Parse a HigherPrimitive from JSON -/
def higherPrimitiveFromJson (j : Lean.Json) : Except String HigherPrimitive := do
  match j with
  | .str name =>
    match HigherPrimitive.fromName? name with
    | some p => pure p
    | none => .error s!"Unknown higher primitive: {name}"
  | _ => .error s!"Invalid higher primitive JSON: {j}"

/-- Parse a TypeId from JSON using derived instance -/
def typeIdFromJson (j : Lean.Json) : Except String TypeId :=
  Lean.FromJson.fromJson? j

/-- Parse a Unique from JSON using derived instance -/
def uniqueFromJson (j : Lean.Json) : Except String Unique :=
  Lean.FromJson.fromJson? j

/-- Parse a LocalPrefix from JSON -/
def localPrefixFromJson (j : Lean.Json) : Except String LocalPrefix := do
  match j with
  | .str "temp" => pure .temp
  | .str "block" => pure .block
  | .str "param" => pure .param
  | .str "reg" => pure .reg
  | .str "patternVar" => pure .patternVar
  | .str "closureSelf" => pure .closureSelf
  | .str "dictParam" => pure .dictParam
  | .str "refParam" => pure .refParam
  | .str "erasure" => pure .erasure
  | .str "forkedTask" => pure .forkedTask
  | other => .error s!"Unknown LocalPrefix: {other}"

/-- Parse a DictKind from string -/
def dictKindFromString (s : String) : Except String DictKind := do
  match s with
  | "global" => pure .global
  | "struct" => pure .struct
  | other => .error s!"Unknown DictKind: {other}"

/-- Parse a SyntheticKind from JSON -/
def syntheticKindFromJson (j : Lean.Json) : Except String SyntheticKind := do
  let tag ← j.getObjValAs? String "tag"
  match tag with
  | "liftedLambda" => pure .liftedLambda
  | "closureEnv" => pure .closureEnv
  | "monomorphized" =>
    let typeStrsJ ← j.getObjValAs? (Array Lean.Json) "typeStrs"
    let typeStrs ← typeStrsJ.toList.mapM fun js =>
      match js with
      | .str s => pure s
      | _ => .error "Expected string in typeStrs"
    pure (.monomorphized typeStrs.toArray)
  | "instanceMethod" =>
    let forTypeStr ← j.getObjValAs? String "forTypeStr"
    pure (.instanceMethod forTypeStr)
  | "dictParam" =>
    let className ← j.getObjValAs? String "className"
    let forTypeStr ← j.getObjValAs? String "forTypeStr"
    pure (.dictParam className forTypeStr)
  | "dictGlobal" =>
    let className ← j.getObjValAs? String "className"
    let forTypeStr ← j.getObjValAs? String "forTypeStr"
    pure (.dictGlobal className forTypeStr)
  | "dictStruct" =>
    let className ← j.getObjValAs? String "className"
    pure (.dictStruct className)
  | "refParam" =>
    let blockName ← j.getObjValAs? String "blockName"
    pure (.refParam blockName)
  | "erasure" => pure .erasure
  | "temp" => pure .temp
  | other => .error s!"Unknown SyntheticKind tag: {other}"

/-- Parse a RuntimeFn from JSON -/
def runtimeFnFromJson (j : Lean.Json) : Except String RuntimeFn := do
  match j with
  | .str "printInt" => pure .printInt
  | .str "printStr" => pure .printStr
  | .str "panic" => pure .panic
  | .str "trace" => pure .trace
  | .str "alloc" => pure .alloc
  | .str "free" => pure .free
  | other => .error s!"Unknown RuntimeFn: {other}"

/-- Parse a PrimOp from JSON -/
def primOpFromJson (j : Lean.Json) : Except String PrimOp := do
  match j with
  | .str "add" => pure .add | .str "sub" => pure .sub | .str "mul" => pure .mul
  | .str "div" => pure .div | .str "mod" => pure .mod | .str "eq" => pure .eq
  | .str "ne" => pure .ne | .str "lt" => pure .lt | .str "le" => pure .le
  | .str "gt" => pure .gt | .str "ge" => pure .ge | .str "and" => pure .and
  | .str "or" => pure .or | .str "not" => pure .not | .str "neg" => pure .neg
  | other => .error s!"Unknown PrimOp: {other}"

/-- Parse an Intrinsic from JSON -/
def intrinsicFromJson (j : Lean.Json) : Except String Intrinsic := do
  match j with
  | .obj obj =>
    if let some (.str name) := obj.get? "llvm" then
      pure (.llvm name)
    else if let some runtimeJ := obj.get? "runtime" then
      let fn ← runtimeFnFromJson runtimeJ
      pure (.runtime fn)
    else if let some primOpJ := obj.get? "primOp" then
      let op ← primOpFromJson primOpJ
      pure (.primOp op)
    else .error s!"Invalid Intrinsic JSON: {j}"
  | _ => .error s!"Invalid Intrinsic JSON: {j}"

/-- Parse a Core.Name from JSON -/
partial def coreNameFromJson (j : Lean.Json) : Except String Core.Name := do
  match j with
  | .obj obj =>
    if let some userJ := obj.get? "user" then
      let unique ← uniqueFromJson userJ
      pure (.user unique)
    else if let some syntheticJ := obj.get? "synthetic" then
      let baseJ ← syntheticJ.getObjVal? "base"
      let base ← uniqueFromJson baseJ
      let kindJ ← syntheticJ.getObjVal? "kind"
      let kind ← syntheticKindFromJson kindJ
      let disc ← syntheticJ.getObjValAs? Nat "disc"
      pure (.synthetic base kind disc)
    else if let some intrinsicJ := obj.get? "intrinsic" then
      let intrinsic ← intrinsicFromJson intrinsicJ
      pure (.intrinsic intrinsic)
    else if let some localJ := obj.get? "local" then
      let kindJ ← localJ.getObjVal? "kind"
      let kind ← localPrefixFromJson kindJ
      let index ← localJ.getObjValAs? Nat "index"
      pure (.local_ ⟨kind, index⟩)
    else if let some projJ := obj.get? "projection" then
      let baseJ ← projJ.getObjVal? "base"
      let base ← coreNameFromJson baseJ
      let index ← projJ.getObjValAs? Nat "index"
      pure (.projection base index)
    else if let some dictJ := obj.get? "dict" then
      let module ← dictJ.getObjValAs? String "module"
      let className ← dictJ.getObjValAs? String "className"
      let instanceTypeStr ← dictJ.getObjValAs? String "instanceTypeStr"
      let kindStr ← dictJ.getObjValAs? String "kind"
      let kind ← dictKindFromString kindStr
      pure (.dict ⟨module, className, instanceTypeStr, kind⟩)
    else if let some ctorJ := obj.get? "ctor" then
      let uniqueJ ← ctorJ.getObjVal? "unique"
      let unique ← uniqueFromJson uniqueJ
      let name ← ctorJ.getObjValAs? String "name"
      let tag ← ctorJ.getObjValAs? Nat "tag"
      pure (.ctor unique name tag)
    else .error s!"Invalid Core.Name JSON: {j}"
  | _ => .error s!"Invalid Core.Name JSON: {j}"

/-- Parse a BoundVar from JSON -/
def boundVarFromJson (j : Lean.Json) : Except String BoundVar := do
  let name ← j.getObjValAs? String "name"
  let level ← j.getObjValAs? Nat "level"
  pure ⟨name, ⟨level⟩⟩

/-- Parse a MetaId from JSON -/
def metaIdFromJson (j : Lean.Json) : Except String MetaId := do
  let id ← j.getObjValAs? Nat "id"
  pure ⟨id⟩

-- Forward declarations for mutual recursion
mutual

/-- Parse a Term from JSON -/
partial def termFromJson (j : Lean.Json) : Except String Term := do
  match j with
  | .obj obj =>
    if let some varJ := obj.get? "var" then
      let idx ← varJ.getObjValAs? Nat "idx"
      let name ← varJ.getObjValAs? String "name"
      pure (.var idx name)
    else if let some (.str litStr) := obj.get? "lit" then
      -- Simplified: just create a string literal
      pure (.stringLit litStr)
    else if let some appJ := obj.get? "app" then
      let fnJ ← appJ.getObjVal? "fn"
      let fn ← termFromJson fnJ
      let argsJ ← appJ.getObjValAs? (Array Lean.Json) "args"
      let args ← argsJ.toList.mapM termFromJson
      pure (.app fn args)
    else if let some lamJ := obj.get? "lam" then
      let namesJ ← lamJ.getObjValAs? (Array Lean.Json) "names"
      let names ← namesJ.toList.mapM (fun j => match j with
        | .str s => pure s
        | _ => .error "Expected string in names")
      let bodyJ ← lamJ.getObjVal? "body"
      let body ← termFromJson bodyJ
      pure (.lam names body)
    else if let some ifJ := obj.get? "if" then
      let condJ ← ifJ.getObjVal? "cond"
      let cond ← termFromJson condJ
      let thenJ ← ifJ.getObjVal? "then"
      let then_ ← termFromJson thenJ
      let elseJ ← ifJ.getObjVal? "else"
      let else_ ← termFromJson elseJ
      pure (.if_ cond then_ else_)
    else if let some (.arr arr) := obj.get? "pair" then
      if arr.size = 2 then
        let fst ← termFromJson arr[0]!
        let snd ← termFromJson arr[1]!
        pure (.pair fst snd)
      else .error "Invalid pair: expected 2 elements"
    else if let some fstJ := obj.get? "fst" then
      let e ← termFromJson fstJ
      pure (.fst e)
    else if let some sndJ := obj.get? "snd" then
      let e ← termFromJson sndJ
      pure (.snd e)
    else if let some piJ := obj.get? "pi" then
      let qtyJ ← piJ.getObjVal? "qty"
      let qty ← quantityFromJson qtyJ
      let binderJ ← piJ.getObjVal? "binder"
      let binder ← binderInfoFromJson binderJ
      let name ← piJ.getObjValAs? String "name"
      let domainJ ← piJ.getObjVal? "domain"
      let domain ← termFromJson domainJ
      let codomainJ ← piJ.getObjVal? "codomain"
      let codomain ← termFromJson codomainJ
      pure (.pi qty binder name domain codomain)
    else if let some sigmaJ := obj.get? "sigma" then
      let qtyJ ← sigmaJ.getObjVal? "qty"
      let qty ← quantityFromJson qtyJ
      let name ← sigmaJ.getObjValAs? String "name"
      let fstJ ← sigmaJ.getObjVal? "fst"
      let fst ← termFromJson fstJ
      let sndJ ← sigmaJ.getObjVal? "snd"
      let snd ← termFromJson sndJ
      pure (.sigma qty name fst snd)
    else if let some typeJ := obj.get? "type" then
      let level ← levelFromJson typeJ
      pure (.type level)
    else if let some primJ := obj.get? "primTy" then
      let p ← starPrimitiveFromJson primJ
      pure (.primTy p)
    else if let some hprimJ := obj.get? "higherPrimTy" then
      let p ← higherPrimitiveFromJson hprimJ
      pure (.higherPrimTy p)
    else if let some intLitJ := obj.get? "intLit" then
      match intLitJ.getInt? with
      | .ok n => pure (.intLit n)
      | .error e => .error s!"Invalid intLit: {e}"
    else if let some (.str s) := obj.get? "stringLit" then
      pure (.stringLit s)
    else if let some rowJ := obj.get? "recordTy" then
      let row ← termFromJson rowJ
      pure (.recordTy row)
    else if let some rowJ := obj.get? "variantTy" then
      let row ← termFromJson rowJ
      pure (.variantTy row)
    else if obj.contains "rowEmpty" then
      pure .rowEmpty
    else if let some extJ := obj.get? "rowExtend" then
      let labelJ ← extJ.getObjVal? "label"
      let label ← termFromJson labelJ
      let fieldTyJ ← extJ.getObjVal? "fieldTy"
      let fieldTy ← termFromJson fieldTyJ
      let tailJ ← extJ.getObjVal? "tail"
      let tail ← termFromJson tailJ
      pure (.rowExtend label fieldTy tail)
    else if let some (.str name) := obj.get? "labelLit" then
      pure (.labelLit name)
    else if let some (.arr fieldsJ) := obj.get? "record" then
      let fields ← fieldsJ.toList.mapM fun fieldJ => do
        let name ← fieldJ.getObjValAs? String "name"
        let valueJ ← fieldJ.getObjVal? "value"
        let value ← termFromJson valueJ
        pure (name, value)
      pure (.record fields)
    else if let some faJ := obj.get? "fieldAccess" then
      let exprJ ← faJ.getObjVal? "expr"
      let e ← termFromJson exprJ
      let field ← faJ.getObjValAs? String "field"
      pure (.fieldAccess e field)
    else if let some ctorJ := obj.get? "construct" then
      let nameJ ← ctorJ.getObjVal? "name"
      let name ← coreNameFromJson nameJ
      let tag ← ctorJ.getObjValAs? Nat "tag"
      let argsJ ← ctorJ.getObjValAs? (Array Lean.Json) "args"
      let args ← argsJ.toList.mapM termFromJson
      pure (.construct name tag args)
    else if let some caseJ := obj.get? "case" then
      let scrutineeJ ← caseJ.getObjVal? "scrutinee"
      let scrutinee ← termFromJson scrutineeJ
      let armsJ ← caseJ.getObjValAs? (Array Lean.Json) "arms"
      let arms ← armsJ.toList.mapM fun armJ => do
        let name ← armJ.getObjValAs? String "name"
        let tag ← armJ.getObjValAs? Nat "tag"
        let bodyJ ← armJ.getObjVal? "body"
        let body ← termFromJson bodyJ
        pure (name, tag, body)
      pure (.case scrutinee arms)
    else if let some globalJ := obj.get? "global" then
      let name ← coreNameFromJson globalJ
      pure (.global name)
    else if let some eqJ := obj.get? "eq" then
      let tyLevelJ ← eqJ.getObjVal? "tyLevel"
      let tyLevel ← levelFromJson tyLevelJ
      let tyJ ← eqJ.getObjVal? "ty"
      let ty ← termFromJson tyJ
      let lhsJ ← eqJ.getObjVal? "lhs"
      let lhs ← termFromJson lhsJ
      let rhsJ ← eqJ.getObjVal? "rhs"
      let rhs ← termFromJson rhsJ
      pure (.eq tyLevel ty lhs rhs)
    else if let some reflJ := obj.get? "refl" then
      let tyJ ← reflJ.getObjVal? "ty"
      let ty ← termFromJson tyJ
      let xJ ← reflJ.getObjVal? "x"
      let x ← termFromJson xJ
      pure (.refl ty x)
    else if let some transJ := obj.get? "transport" then
      let tyLevelJ ← transJ.getObjVal? "tyLevel"
      let tyLevel ← levelFromJson tyLevelJ
      let tyJ ← transJ.getObjVal? "ty"
      let ty ← termFromJson tyJ
      let motiveJ ← transJ.getObjVal? "motive"
      let motive ← termFromJson motiveJ
      let lhsJ ← transJ.getObjVal? "lhs"
      let lhs ← termFromJson lhsJ
      let rhsJ ← transJ.getObjVal? "rhs"
      let rhs ← termFromJson rhsJ
      let eqJ ← transJ.getObjVal? "eq"
      let eq ← termFromJson eqJ
      let bodyJ ← transJ.getObjVal? "body"
      let body ← termFromJson bodyJ
      pure (.transport tyLevel ty motive lhs rhs eq body)
    else if let some mvarJ := obj.get? "mvar" then
      match mvarJ.getNat? with
      | .ok id => pure (.mvar id)
      | .error e => .error s!"Invalid mvar id: {e}"
    else if let some (.str msg) := obj.get? "panic" then
      pure (.panic msg)
    else .error s!"Unknown term JSON: {j}"
  | _ => .error s!"Invalid term JSON: {j}"

/-- Parse an Env from JSON -/
partial def envFromJson (j : Lean.Json) : Except String Env := do
  let valuesJ ← j.getObjValAs? (Array Lean.Json) "values"
  let size ← j.getObjValAs? Nat "size"
  let values ← valuesJ.toList.mapM fun entryJ => do
    let name ← entryJ.getObjValAs? String "name"
    let valueJ ← entryJ.getObjVal? "value"
    let value ← valueFromJson valueJ
    pure (name, value)
  pure (.mk values size)

/-- Parse a Closure from JSON -/
partial def closureFromJson (j : Lean.Json) : Except String Closure := do
  match j with
  | .obj obj =>
    if let some termJ := obj.get? "term" then
      let name ← termJ.getObjValAs? String "name"
      let envJ ← termJ.getObjVal? "env"
      let env ← envFromJson envJ
      let bodyJ ← termJ.getObjVal? "body"
      let body ← termFromJson bodyJ
      pure (.term name env body)
    else if let some constJ := obj.get? "const" then
      let name ← constJ.getObjValAs? String "name"
      let valueJ ← constJ.getObjVal? "value"
      let value ← valueFromJson valueJ
      pure (.const name value)
    else .error s!"Invalid closure JSON: {j}"
  | _ => .error s!"Invalid closure JSON: {j}"

/-- Parse an ArmClosure from JSON -/
partial def armClosureFromJson (j : Lean.Json) : Except String ArmClosure := do
  let pattern ← j.getObjValAs? String "pattern"
  let closureJ ← j.getObjVal? "closure"
  let closure ← closureFromJson closureJ
  pure (.mk pattern closure)

/-- Parse a Neutral from JSON -/
partial def neutralFromJson (j : Lean.Json) : Except String Neutral := do
  match j with
  | .obj obj =>
    if let some nVarJ := obj.get? "nVar" then
      let v ← boundVarFromJson nVarJ
      pure (.nVar v)
    else if let some nMetaJ := obj.get? "nMeta" then
      let id ← metaIdFromJson nMetaJ
      pure (.nMeta id)
    else if let some nAppJ := obj.get? "nApp" then
      let fnJ ← nAppJ.getObjVal? "fn"
      let fn ← neutralFromJson fnJ
      let argJ ← nAppJ.getObjVal? "arg"
      let arg ← valueFromJson argJ
      pure (.nApp fn arg)
    else if let some nFstJ := obj.get? "nFst" then
      let pair ← neutralFromJson nFstJ
      pure (.nFst pair)
    else if let some nSndJ := obj.get? "nSnd" then
      let pair ← neutralFromJson nSndJ
      pure (.nSnd pair)
    else if let some nFaJ := obj.get? "nFieldAccess" then
      let recordJ ← nFaJ.getObjVal? "record"
      let record ← neutralFromJson recordJ
      let field ← nFaJ.getObjValAs? String "field"
      pure (.nFieldAccess record field)
    else if let some nCaseJ := obj.get? "nCase" then
      let scrutineeJ ← nCaseJ.getObjVal? "scrutinee"
      let scrutinee ← neutralFromJson scrutineeJ
      let armsJ ← nCaseJ.getObjValAs? (Array Lean.Json) "arms"
      let arms ← armsJ.toList.mapM armClosureFromJson
      pure (.nCase scrutinee arms)
    else .error s!"Invalid neutral JSON: {j}"
  | _ => .error s!"Invalid neutral JSON: {j}"

/-- Parse a Value from JSON -/
partial def valueFromJson (j : Lean.Json) : Except String Value := do
  match j with
  | .obj obj =>
    if let some vTypeJ := obj.get? "vType" then
      let level ← levelFromJson vTypeJ
      pure (.vType level)
    else if let some vPiJ := obj.get? "vPi" then
      let qtyJ ← vPiJ.getObjVal? "qty"
      let qty ← quantityFromJson qtyJ
      let binderJ ← vPiJ.getObjVal? "binder"
      let binder ← binderInfoFromJson binderJ
      let name ← vPiJ.getObjValAs? String "name"
      let domainJ ← vPiJ.getObjVal? "domain"
      let domain ← valueFromJson domainJ
      let codomainJ ← vPiJ.getObjVal? "codomain"
      let codomain ← closureFromJson codomainJ
      pure (.vPi qty binder name domain codomain)
    else if let some vLamJ := obj.get? "vLam" then
      let qtyJ ← vLamJ.getObjVal? "qty"
      let qty ← quantityFromJson qtyJ
      let binderJ ← vLamJ.getObjVal? "binder"
      let binder ← binderInfoFromJson binderJ
      let name ← vLamJ.getObjValAs? String "name"
      let domainJ ← vLamJ.getObjVal? "domain"
      let domain ← valueFromJson domainJ
      let bodyJ ← vLamJ.getObjVal? "body"
      let body ← closureFromJson bodyJ
      pure (.vLam qty binder name domain body)
    else if let some vSigmaJ := obj.get? "vSigma" then
      let qtyJ ← vSigmaJ.getObjVal? "qty"
      let qty ← quantityFromJson qtyJ
      let name ← vSigmaJ.getObjValAs? String "name"
      let fstJ ← vSigmaJ.getObjVal? "fst"
      let fst ← valueFromJson fstJ
      let sndJ ← vSigmaJ.getObjVal? "snd"
      let snd ← closureFromJson sndJ
      pure (.vSigma qty name fst snd)
    else if let some (.arr arr) := obj.get? "vPair" then
      if arr.size = 2 then
        let fst ← valueFromJson arr[0]!
        let snd ← valueFromJson arr[1]!
        pure (.vPair fst snd)
      else .error "Invalid vPair: expected 2 elements"
    else if let some vNeutralJ := obj.get? "vNeutral" then
      let tyJ ← vNeutralJ.getObjVal? "ty"
      let ty ← valueFromJson tyJ
      let neutralJ ← vNeutralJ.getObjVal? "neutral"
      let neutral ← neutralFromJson neutralJ
      pure (.vNeutral ty neutral)
    else if let some vPrimTyJ := obj.get? "vPrimTy" then
      let p ← starPrimitiveFromJson vPrimTyJ
      pure (.vPrimTy p)
    else if let some vHigherPrimJ := obj.get? "vHigherPrim" then
      let p ← higherPrimitiveFromJson vHigherPrimJ
      pure (.vHigherPrim p)
    else if let some intLitJ := obj.get? "vIntLit" then
      match intLitJ.getInt? with
      | .ok n => pure (.vIntLit n)
      | .error e => .error s!"Invalid vIntLit: {e}"
    else if let some (.str s) := obj.get? "vStringLit" then
      pure (.vStringLit s)
    else if obj.contains "vRowEmpty" then
      pure .vRowEmpty
    else if let some vRowExtendJ := obj.get? "vRowExtend" then
      let labelJ ← vRowExtendJ.getObjVal? "label"
      let label ← valueFromJson labelJ
      let fieldTyJ ← vRowExtendJ.getObjVal? "fieldTy"
      let fieldTy ← valueFromJson fieldTyJ
      let tailJ ← vRowExtendJ.getObjVal? "tail"
      let tail ← valueFromJson tailJ
      pure (.vRowExtend label fieldTy tail)
    else if let some vRecordJ := obj.get? "vRecord" then
      let row ← valueFromJson vRecordJ
      pure (.vRecord row)
    else if let some vVariantJ := obj.get? "vVariant" then
      let row ← valueFromJson vVariantJ
      pure (.vVariant row)
    else if let some (.str name) := obj.get? "vLabelLit" then
      pure (.vLabelLit name)
    else if let some (.arr fieldsJ) := obj.get? "vRecordVal" then
      let fields ← fieldsJ.toList.mapM fun fieldJ => do
        let name ← fieldJ.getObjValAs? String "name"
        let valueJ ← fieldJ.getObjVal? "value"
        let value ← valueFromJson valueJ
        pure (name, value)
      pure (.vRecordVal fields)
    else if let some vDataTypeJ := obj.get? "vDataType" then
      let idJ ← vDataTypeJ.getObjVal? "id"
      let id ← typeIdFromJson idJ
      let paramsJ ← vDataTypeJ.getObjValAs? (Array Lean.Json) "params"
      let params ← paramsJ.toList.mapM valueFromJson
      pure (.vDataType id params)
    else if let some vConstructorJ := obj.get? "vConstructor" then
      let nameJ ← vConstructorJ.getObjVal? "name"
      let name ← coreNameFromJson nameJ
      let tag ← vConstructorJ.getObjValAs? Nat "tag"
      let argsJ ← vConstructorJ.getObjValAs? (Array Lean.Json) "args"
      let args ← argsJ.toList.mapM valueFromJson
      pure (.vConstructor name tag args)
    else if let some vEqJ := obj.get? "vEq" then
      let tyLevelJ ← vEqJ.getObjVal? "tyLevel"
      let tyLevel ← levelFromJson tyLevelJ
      let tyJ ← vEqJ.getObjVal? "ty"
      let ty ← valueFromJson tyJ
      let lhsJ ← vEqJ.getObjVal? "lhs"
      let lhs ← valueFromJson lhsJ
      let rhsJ ← vEqJ.getObjVal? "rhs"
      let rhs ← valueFromJson rhsJ
      pure (.vEq tyLevel ty lhs rhs)
    else if let some vReflJ := obj.get? "vRefl" then
      let tyJ ← vReflJ.getObjVal? "ty"
      let ty ← valueFromJson tyJ
      let xJ ← vReflJ.getObjVal? "x"
      let x ← valueFromJson xJ
      pure (.vRefl ty x)
    else if let some vTransportJ := obj.get? "vTransport" then
      let tyLevelJ ← vTransportJ.getObjVal? "tyLevel"
      let tyLevel ← levelFromJson tyLevelJ
      let tyJ ← vTransportJ.getObjVal? "ty"
      let ty ← valueFromJson tyJ
      let motiveJ ← vTransportJ.getObjVal? "motive"
      let motive ← valueFromJson motiveJ
      let lhsJ ← vTransportJ.getObjVal? "lhs"
      let lhs ← valueFromJson lhsJ
      let rhsJ ← vTransportJ.getObjVal? "rhs"
      let rhs ← valueFromJson rhsJ
      let eqJ ← vTransportJ.getObjVal? "eq"
      let eq ← valueFromJson eqJ
      let bodyJ ← vTransportJ.getObjVal? "body"
      let body ← valueFromJson bodyJ
      pure (.vTransport tyLevel ty motive lhs rhs eq body)
    else .error s!"Unknown value JSON: {j}"
  | _ => .error s!"Invalid value JSON: {j}"

end

/-- Parse a Span from JSON -/
def spanFromJson (j : Lean.Json) : Except String Span := do
  let fileId ← j.getObjValAs? Nat "fileId"
  let startOffset ← j.getObjValAs? Nat "startOffset"
  let endOffset ← j.getObjValAs? Nat "endOffset"
  let startLine ← j.getObjValAs? Nat "startLine"
  let startColumn ← j.getObjValAs? Nat "startColumn"
  let endLine ← j.getObjValAs? Nat "endLine"
  let endColumn ← j.getObjValAs? Nat "endColumn"
  pure {
    start := { file := ⟨fileId⟩, byteOffset := startOffset, line := startLine, column := startColumn }
    stop := { file := ⟨fileId⟩, byteOffset := endOffset, line := endLine, column := endColumn }
  }

/-- Parse a SymbolKind from JSON -/
def symbolKindFromJson (j : Lean.Json) : Except String SymbolKind := do
  match j with
  | .str "binding" => pure .binding
  | .str "type" => pure .type
  | .str "typeClass" => pure .typeClass
  | .str "letBinding" => pure .letBinding
  | .str "lambdaParam" => pure .lambdaParam
  | .str "patternVar" => pure .patternVar
  | .str "patternAs" => pure .patternAs
  | .str "composeBinding" => pure .composeBinding
  | .str "intrinsicBinding" => pure .intrinsicBinding
  | .str "intrinsicType" => pure .intrinsicType
  | .obj obj =>
    if let some dataConJ := obj.get? "dataCon" then
      let parent ← dataConJ.getObjValAs? String "parent"
      let tag ← dataConJ.getObjValAs? Nat "tag"
      pure (.dataCon parent tag)
    else if let some (.str cls) := obj.get? "typeClassMethod" then
      pure (.typeClassMethod cls)
    else if let some instJ := obj.get? "instanceMethod" then
      let inst ← instJ.getObjValAs? String "instance"
      let cls ← instJ.getObjValAs? String "class"
      pure (.instanceMethod inst cls)
    else
      .error s!"Unknown symbol kind: {j}"
  | _ => .error s!"Invalid symbol kind JSON: {j}"

/-- Parse a Symbol from JSON -/
def symbolFromJson (j : Lean.Json) : Except String Symbol := do
  let name ← j.getObjValAs? String "name"
  let kindJ ← j.getObjVal? "kind"
  let kind ← symbolKindFromJson kindJ
  let module ← j.getObjValAs? String "module"
  let package ← j.getObjValAs? String "package"
  let spanJ ← j.getObjVal? "span"
  let span ← spanFromJson spanJ
  let uniqueJ ← j.getObjVal? "unique"
  let unique ← uniqueFromJson uniqueJ
  pure { unique, name, kind, module, package, span }

/-- Parse a symbol entry (symbol + type as Value) from JSON -/
def symbolEntryFromJson (j : Lean.Json) : Except String (Symbol × Value) := do
  let symJ ← j.getObjVal? "symbol"
  let sym ← symbolFromJson symJ
  let typeJ ← j.getObjVal? "type"
  let ty ← valueFromJson typeJ
  pure (sym, ty)

/-- Parse SymbolEnv from JSON array -/
def symbolEnvFromJson (j : Lean.Json) : Except String SymbolEnv := do
  match j with
  | .arr entries =>
    let pairs ← entries.toList.mapM symbolEntryFromJson
    pure (pairs.foldl (fun env (sym, val) => env.insert sym val) {})
  | _ => .error "Expected array for symbols"

/-- Parse an instance entry from JSON -/
def instanceEntryFromJson (j : Lean.Json) : Except String (Array Value × Symbol) := do
  let typeArgsJ ← j.getObjValAs? (Array Lean.Json) "typeArgs"
  let typeArgs ← typeArgsJ.toList.mapM valueFromJson
  let symJ ← j.getObjVal? "symbol"
  let sym ← symbolFromJson symJ
  pure (typeArgs.toArray, sym)

/-- Parse InstanceMetadata from JSON array -/
def instanceMetadataFromJson (j : Lean.Json) : Except String InstanceMetadata := do
  match j with
  | .arr entries =>
    let mut env : InstanceMetadata := {}
    for entry in entries do
      let className ← entry.getObjValAs? String "class"
      let instancesJ ← entry.getObjValAs? (Array Lean.Json) "instances"
      let instances ← instancesJ.toList.mapM instanceEntryFromJson
      env := env.insert className instances.toArray
    pure env
  | _ => .error "Expected array for instances"

/-- Parse constructor metadata from JSON array -/
def constructorMetadataFromJson (j : Lean.Json) : Except String (Std.HashMap String Nat) := do
  match j with
  | .arr entries =>
    let mut ctors : Std.HashMap String Nat := {}
    for entry in entries do
      let name ← entry.getObjValAs? String "name"
      let tag ← entry.getObjValAs? Nat "tag"
      ctors := ctors.insert name tag
    pure ctors
  | _ => .error "Expected array for constructors"

/-- Parse a GlobalInfo from JSON -/
def globalInfoFromJson (j : Lean.Json) : Except String GlobalInfo := do
  let nameJ ← j.getObjVal? "name"
  let name ← coreNameFromJson nameJ
  let typeJ ← j.getObjVal? "type"
  let type ← valueFromJson typeJ
  let valueJ := j.getObjVal? "value"
  let value ← match valueJ with
    | .ok v => if v == .null then pure none else (valueFromJson v).map some
    | .error _ => pure none
  let isConstructor ← j.getObjValAs? Bool "isConstructor"
  let ctorTag ← j.getObjValAs? Nat "ctorTag"
  pure { name, type, value, isConstructor, ctorTag }

/-- Parse Globals from JSON -/
def globalsFromJson (j : Lean.Json) : Except String Globals := do
  let defsJ ← j.getObjValAs? (Array Lean.Json) "defs"
  let typeIdsJ ← j.getObjValAs? (Array Lean.Json) "typeIds"
  let mut defs : Std.HashMap String GlobalInfo := {}
  for entry in defsJ do
    let name ← entry.getObjValAs? String "name"
    let infoJ ← entry.getObjVal? "info"
    let info ← globalInfoFromJson infoJ
    defs := defs.insert name info
  let mut typeIds : Std.HashMap String TypeId := {}
  for entry in typeIdsJ do
    let name ← entry.getObjValAs? String "name"
    let idJ ← entry.getObjVal? "id"
    let id ← typeIdFromJson idJ
    typeIds := typeIds.insert name id
  pure { defs, typeIds }

/-- Parse a ClassInfo from JSON -/
def classInfoFromJson (j : Lean.Json) : Except String ClassInfo := do
  let classIdJ ← j.getObjVal? "classId"
  let classId ← uniqueFromJson classIdJ
  let numParams ← j.getObjValAs? Nat "numParams"
  let paramQuantitiesJ ← j.getObjValAs? (Array Lean.Json) "paramQuantities"
  let paramQuantities ← paramQuantitiesJ.toList.mapM quantityFromJson
  let recordTypeJ ← j.getObjVal? "recordType"
  let recordType ← valueFromJson recordTypeJ
  let superclassesJ ← j.getObjValAs? (Array Lean.Json) "superclasses"
  let superclasses ← superclassesJ.toList.mapM fun scJ => do
    let classIdJ ← scJ.getObjVal? "classId"
    let classId ← uniqueFromJson classIdJ
    let paramIndicesJ ← scJ.getObjValAs? (Array Lean.Json) "paramIndices"
    let paramIndices ← paramIndicesJ.toList.mapM fun j =>
      match j.getNat? with
      | .ok n => pure n
      | .error e => .error s!"Expected number: {e}"
    pure (classId, paramIndices.toArray)
  let spanJ ← j.getObjVal? "span"
  let span ← spanFromJson spanJ
  pure { classId, numParams, paramQuantities := paramQuantities.toArray, recordType, superclasses := superclasses.toArray, span }

/-- Parse an InstanceInfo from JSON -/
def instanceInfoFromJson (j : Lean.Json) : Except String InstanceInfo := do
  let instanceIdJ ← j.getObjVal? "instanceId"
  let instanceId ← uniqueFromJson instanceIdJ
  let classIdJ ← j.getObjVal? "classId"
  let classId ← uniqueFromJson classIdJ
  let argsJ ← j.getObjValAs? (Array Lean.Json) "args"
  let args ← argsJ.toList.mapM valueFromJson
  let argQuantitiesJ ← j.getObjValAs? (Array Lean.Json) "argQuantities"
  let argQuantities ← argQuantitiesJ.toList.mapM quantityFromJson
  let constraintsJ ← j.getObjValAs? (Array Lean.Json) "constraints"
  let constraints ← constraintsJ.toList.mapM fun cJ => do
    let classIdJ ← cJ.getObjVal? "classId"
    let classId ← uniqueFromJson classIdJ
    let cArgsJ ← cJ.getObjValAs? (Array Lean.Json) "args"
    let cArgs ← cArgsJ.toList.mapM valueFromJson
    pure (classId, cArgs.toArray)
  let valueJ ← j.getObjVal? "value"
  let value ← valueFromJson valueJ
  let spanJ ← j.getObjVal? "span"
  let span ← spanFromJson spanJ
  pure { instanceId, classId, args := args.toArray, argQuantities := argQuantities.toArray, constraints := constraints.toArray, value, span }

/-- Parse InstanceEnv from JSON -/
def instanceEnvFromJson (j : Lean.Json) : Except String InstanceEnv := do
  let classesJ ← j.getObjValAs? (Array Lean.Json) "classes"
  let instancesJ ← j.getObjValAs? (Array Lean.Json) "instances"
  let nextInstanceId ← j.getObjValAs? Nat "nextInstanceId"
  let moduleName ← j.getObjValAs? String "moduleName"
  let mut classes : Std.HashMap Unique ClassInfo := {}
  for entry in classesJ do
    let classIdJ ← entry.getObjVal? "classId"
    let classId ← uniqueFromJson classIdJ
    let infoJ ← entry.getObjVal? "info"
    let info ← classInfoFromJson infoJ
    classes := classes.insert classId info
  let mut instances : Std.HashMap Unique (Array InstanceInfo) := {}
  for entry in instancesJ do
    let classIdJ ← entry.getObjVal? "classId"
    let classId ← uniqueFromJson classIdJ
    let instsJ ← entry.getObjValAs? (Array Lean.Json) "instances"
    let insts ← instsJ.toList.mapM instanceInfoFromJson
    instances := instances.insert classId insts.toArray
  pure { classes, instances, nextInstanceId, moduleName }

/-- Parse an AbbrevInfo from JSON -/
def abbrevInfoFromJson (j : Lean.Json) : Except String AbbrevInfo := do
  let abbrevIdJ ← j.getObjVal? "abbrevId"
  let abbrevId ← uniqueFromJson abbrevIdJ
  let arity ← j.getObjValAs? Nat "arity"
  let expansionJ ← j.getObjVal? "expansion"
  let expansion ← valueFromJson expansionJ
  let spanJ ← j.getObjVal? "span"
  let span ← spanFromJson spanJ
  pure { abbrevId, arity, expansion, span }

/-- Parse AbbrevEnv from JSON array -/
def abbrevEnvFromJson (j : Lean.Json) : Except String AbbrevEnv := do
  match j with
  | .arr entries =>
    let mut env := AbbrevEnv.empty
    for entry in entries do
      let info ← abbrevInfoFromJson entry
      env := env.insert info
    pure env
  | _ => .error "Expected array for abbrevEnv"

/-- Load metadata from a JSON file -/
def loadMetadataFromFile (path : System.FilePath) : IO (Except String ExternalDependency) := do
  let content ← IO.FS.readFile path
  match Lean.Json.parse content with
  | .error e => pure (.error s!"Failed to parse JSON: {e}")
  | .ok json => do
    let result := do
      let version ← json.getObjValAs? String "version"
      -- Accept version 2 (without abbrevEnv) and version 3 (with abbrevEnv)
      if version != "2" && version != "3" then
        .error s!"Unsupported metadata version: {version}. Expected version 2 or 3."
      else
        let moduleName ← json.getObjValAs? String "module"
        let symbolsJ ← json.getObjVal? "symbols"
        let symbols ← symbolEnvFromJson symbolsJ
        let instancesJ ← json.getObjVal? "instances"
        let instances ← instanceMetadataFromJson instancesJ
        let constructorsJ ← json.getObjVal? "constructors"
        let constructors ← constructorMetadataFromJson constructorsJ
        let globalsJ ← json.getObjVal? "globals"
        let globals ← globalsFromJson globalsJ
        let instanceEnvJ ← json.getObjVal? "instanceEnv"
        let instanceEnv ← instanceEnvFromJson instanceEnvJ
        -- Parse abbrevEnv if present (version 3), otherwise use empty
        let abbrevEnv ← match json.getObjVal? "abbrevEnv" with
          | .ok abbrevEnvJ => abbrevEnvFromJson abbrevEnvJ
          | .error _ => pure AbbrevEnv.empty
        pure {
          name := moduleName
          version := some version
          symbols := ({} : Std.HashMap String SymbolEnv).insert moduleName symbols
          instances := ({} : Std.HashMap String InstanceMetadata).insert moduleName instances
          constructors := constructors
          globals := globals
          instanceEnv := instanceEnv
          abbrevEnv := abbrevEnv
        }
    pure result

/-- Load multiple metadata files as external dependencies -/
def loadMetadataFiles (deps : Array (String × System.FilePath)) : IO (Except CheckError (Array ExternalDependency)) := do
  let mut results : Array ExternalDependency := #[]
  for (name, path) in deps do
    match ← loadMetadataFromFile path with
    | .ok dep => results := results.push dep
    | .error e => return .error (.dependencyLoadError name e)
  pure (.ok results)

end Soma.Project.MetadataLoad
