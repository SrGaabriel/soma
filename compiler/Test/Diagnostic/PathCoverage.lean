import Soma.Core.Value
import Soma.Core.Pp
import Soma.Core.Path
import Test.Fixtures

namespace Test.Diagnostic.PathCoverage

open Soma.Core
open Test.Fixtures

private def stubTy : Value := .vDataType ⟨9001, "test", "PCStub"⟩ []
private def stubVal : Value := .vDataType ⟨9002, "test", "PCStubVal"⟩ []
private def stubDataId : Soma.Unique := ⟨9003, "test", "PCData"⟩
private def stubCtorName : QualifiedName := ⟨⟨9004, "test", "PCCtor"⟩⟩
private def stubFieldName : String := "fld"
private def stubLabel : Value := .vLabelLit "lbl"

private def ppCtx : PpContext := {}

private structure Case where
  label : String
  value : Value
  expected : Path
  expectedToken : Option String := none

private def stubDomTy : Value := .vDataType ⟨9101, "test", "PCDom"⟩ []
private def stubCodTy : Value := .vDataType ⟨9102, "test", "PCCod"⟩ []
private def stubArg0  : Value := .vDataType ⟨9103, "test", "PCArg0"⟩ []
private def stubArg1  : Value := .vDataType ⟨9104, "test", "PCArg1"⟩ []
private def stubField : Value := .vDataType ⟨9105, "test", "PCField"⟩ []
private def stubLam   : Value := .vDataType ⟨9106, "test", "PCLamBody"⟩ []

private def vPiCase : Case :=
  let cod : Closure := .const "_" stubCodTy
  { label := "piDomain"
    value := .vPi .omega .explicit "x" stubDomTy cod
    expected := #[.piDomain]
    expectedToken := some "PCDom" }

private def vPiCodCase : Case :=
  let cod : Closure := .const "_" stubCodTy
  { label := "piCodomain"
    value := .vPi .omega .explicit "x" stubDomTy cod
    expected := #[.piCodomain]
    expectedToken := some "PCCod" }

private def vLamCase : Case :=
  let body : Closure := .const "_" stubLam
  { label := "lamBody"
    value := .vLam "x" stubDomTy body
    expected := #[.lamBody]
    expectedToken := some "PCLamBody" }

private def vDataTypeParam0Case : Case :=
  { label := "dataTypeParam 0"
    value := .vDataType stubDataId [stubArg0, stubArg1]
    expected := #[.dataTypeParam 0]
    expectedToken := some "PCArg0" }

private def vDataTypeParam1Case : Case :=
  { label := "dataTypeParam 1"
    value := .vDataType stubDataId [stubArg0, stubArg1]
    expected := #[.dataTypeParam 1]
    expectedToken := some "PCArg1" }

private def vConstructorArgCase (idx : Nat) : Case :=
  let token := if idx == 0 then "PCArg0" else "PCArg1"
  { label := s!"constructorArg {idx}"
    value := .vConstructor stubCtorName 0 [stubArg0, stubArg1] stubTy
    expected := #[.constructorArg idx]
    expectedToken := some token }

private def vRowExtendCases : List Case :=
  let row : Value := .vRowExtend stubLabel stubField .vRowEmpty
  [ { label := "rowLabel", value := row, expected := #[.rowLabel]
      expectedToken := some "'lbl" }
  , { label := "rowField", value := row, expected := #[.rowField]
      expectedToken := some "PCField" }
  , { label := "rowTail",  value := row, expected := #[.rowTail]
      expectedToken := some "{}" } ]

private def vRecordCase : Case :=
  let row : Value := .vRowExtend stubLabel stubField .vRowEmpty
  { label := "recordRow"
    value := .vRecord row
    expected := #[.recordRow]
    expectedToken := some "PCField" }

private def vVariantCase : Case :=
  let row : Value := .vRowExtend stubLabel stubField .vRowEmpty
  { label := "variantRow"
    value := .vVariant row
    expected := #[.variantRow]
    expectedToken := some "PCField" }

private def vReflCases : List Case := []

private def vNeutralAppCase : Case :=
  let neu : Neutral := Neutral.mk (.hVar ⟨"f", ⟨0⟩⟩) #[.eApp stubArg0]
  { label := "spineArg 0"
    value := .vNeutral stubTy neu
    expected := #[.spineArg 0]
    expectedToken := some "PCArg0" }

private def vNeutralFieldCase : Case :=
  let neu : Neutral := Neutral.mk (.hVar ⟨"r", ⟨0⟩⟩) #[.eField stubFieldName]
  { label := s!"spineField .{stubFieldName}"
    value := .vNeutral stubTy neu
    expected := #[.spineField stubFieldName]
    expectedToken := some s!".{stubFieldName}" }

private def vRecordValCase : Case :=
  { label := s!"recordField `{stubFieldName}`"
    value := .vRecordVal [(stubFieldName, stubField)]
    expected := #[.recordField stubFieldName]
    expectedToken := some "PCField" }

private def vTransportCases : List Case := []

private def allCases : List Case :=
  [vPiCase, vPiCodCase, vLamCase,
   vDataTypeParam0Case, vDataTypeParam1Case,
   vConstructorArgCase 0, vConstructorArgCase 1] ++
  vRowExtendCases ++
  [vRecordCase, vVariantCase] ++
  vReflCases ++
  [vNeutralAppCase, vNeutralFieldCase, vRecordValCase] ++
  vTransportCases

private def textOfSpan (text : String) (span : PpSubSpan) : String := Id.run do
  let lines := text.splitOn "\n"
  if span.startLine == 0 ∨ span.startLine > lines.length then return ""
  let mut parts : Array String := #[]
  for i in [span.startLine - 1 : Nat.min span.endLine lines.length] do
    let line := lines[i]!
    let lineChars := line.toList
    let startCol := if i + 1 == span.startLine then span.startCol else 0
    let endCol := if i + 1 == span.endLine then span.endCol else lineChars.length
    let lo := Nat.min startCol lineChars.length
    let hi := Nat.min endCol lineChars.length
    if hi > lo then
      parts := parts.push (lineChars.drop lo |>.take (hi - lo) |> String.ofList)
  return String.intercalate "\n" parts.toList

private def runOne (c : Case) : IO TestResult := do
  let rendered := Value.ppWithSpans ppCtx c.value
  match rendered.spans[c.expected]? with
  | none =>
    let keys := rendered.spans.toList.map (fun (p, _) => Path.describe p)
    return .failed s!"path `{Path.describe c.expected}` not in rendered spans for case `{c.label}`. \
      Rendered text: {rendered.text.trimAscii}; recorded paths: [{String.intercalate ", " keys}]."
  | some span =>
    let slice := textOfSpan rendered.text span
    if slice.trimAscii.isEmpty then
      return .failed s!"path `{Path.describe c.expected}` for case `{c.label}` has a recorded span \
        but the visible text inside it is empty. Rendered text: `{rendered.text.trimAscii}` \
        Span = ({span.startLine},{span.startCol})-({span.endLine},{span.endCol})"
    match c.expectedToken with
    | none => return .passed
    | some token =>
      if slice.toSlice.contains token then return .passed
      else return .failed s!"path `{Path.describe c.expected}` for case `{c.label}` rendered as \
        `{slice}` but expected to contain `{token}`. Full rendered text: `{rendered.text.trimAscii}`"

def run : IO TestRunner := do
  IO.println "=== Diagnostic PathStep Coverage ==="
  let mut runner := TestRunner.init
  for c in allCases do
    let result ← runOne c
    runner := runner.record c.label result
    match result with
    | .passed => IO.println s!"  [PASS] {c.label}"
    | .failed msg => IO.println s!"  [FAIL] {c.label}: {msg}"
    | .skipped reason => IO.println s!"  [SKIP] {c.label}: {reason}"
  IO.println ""
  runner.printSummary "PathStep Coverage"
  return runner

end Test.Diagnostic.PathCoverage
