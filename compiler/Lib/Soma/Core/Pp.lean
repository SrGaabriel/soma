import Soma.Core.Value
import Soma.Core.Quote
import Soma.Core.Path
import Soma.Core.Doc

namespace Soma.Core

structure PpContext where
  metas : MetaState := .empty
  maxWidth : Nat := 80
  eqInductiveId : Option Unique := none
  deriving Inhabited

namespace PpContext

def empty : PpContext := {}

def ofMetas (m : MetaState) : PpContext := { metas := m }

def withEqInductive (ctx : PpContext) (eqId? : Option Unique) : PpContext :=
  { ctx with eqInductiveId := eqId? }

end PpContext

private def binderPrefix : BinderInfo → String
  | .explicit => ""
  | .implicit => "implicit "
  | .instance_ => "instance "
  | .strictImplicit => "strict "

private def instantiateClosureForPp (name : String) (domain : Value)
    (clos : Closure) : Value :=
  let lvl := clos.level?.getD ⟨0⟩
  let x := Value.vNeutral domain (.nVar ⟨name, lvl⟩)
  Closure.applyPure clos x

mutual

partial def valuePp (ctx : PpContext) : Value → String
  | .vType level =>
    match level with
    | .lit 0 => "Type"
    | .lit _ => s!"Type{Level.toSubscript level}"
    | _ => s!"Type{level}"
  | .vPi _qty binder name domain codomain =>
    let binderStr := binderPrefix binder
    let domStr := valuePp ctx domain
    let codStr := valuePp ctx (instantiateClosureForPp name domain codomain)
    s!"({binderStr}{name} : {domStr}) -> {codStr}"
  | .vLam name body =>
    let bodyStr := valuePp ctx (instantiateClosureForPp name .type0 body)
    s!"fun({name}) => {bodyStr}"
  | .vNeutral _ neu => neutralPp ctx neu
  | .vRowSort => "Row"
  | .vLabelSort => "Label"
  | .vIntLit n => toString n
  | .vFloatLit f => toString f
  | .vStringLit s => s!"\"{s}\""
  | .vRowEmpty => "{}"
  | .vRowExtend label fieldTy tail =>
    let labelStr := valuePp ctx label
    let tyStr := valuePp ctx fieldTy
    let tailStr := valuePp ctx tail
    "{ " ++ labelStr ++ " : " ++ tyStr ++ " | " ++ tailStr ++ " }"
  | .vRecord row => "{ " ++ valuePp ctx row ++ " }"
  | .vVariant row => "< " ++ valuePp ctx row ++ " >"
  | .vLabelLit name => s!"'{name}"
  | .vRecordVal fields =>
    let fieldsStr := fields.map fun (n, v) => n ++ " = " ++ valuePp ctx v
    "{ " ++ ", ".intercalate fieldsStr ++ " }"
  | .vDataType id params =>
    if ctx.eqInductiveId == some id then
      match params with
      | [_ty, lhs, rhs] =>
        s!"{valuePp ctx lhs} = {valuePp ctx rhs}"
      | _ =>
        let paramsStr := params.map (valuePp ctx)
        s!"{id.original} {" ".intercalate paramsStr}"
    else if params.isEmpty then id.original
    else
      let paramsStr := params.map (valuePp ctx)
      s!"{id.original} {" ".intercalate paramsStr}"
  | .vConstructor name _ args _ =>
    if args.isEmpty then name.display
    else
      let argsStr := args.map (valuePp ctx)
      s!"{name.display} {" ".intercalate argsStr}"
partial def headPp (ctx : PpContext) : Head → String
  | .hVar v => v.name
  | .hMeta id =>
    match ctx.metas.lookup id with
    | some info =>
      match info.solution with
      | some sol => valuePp ctx sol
      | none =>
        match info.displayHint with
        | some hint => s!"?{hint}"
        | none => s!"?m{id.id}"
    | none => s!"?m{id.id}"
  | .hConst name _ => name.display
  | .hCase scrutinees _ _ =>
    let scrutsStr := scrutinees.toList.map (valuePp ctx) |> String.intercalate ", "
    s!"case {scrutsStr} of …"
  | .hErrored => "{errored}"

partial def elimPp (ctx : PpContext) (acc : String) : Elim → String
  | .eApp arg => s!"{acc} {valuePp ctx arg}"
  | .eField name => s!"{acc}.{name}"

partial def neutralPp (ctx : PpContext) (neu : Neutral) : String :=
  neu.spine.foldl (elimPp ctx) (headPp ctx neu.head)

end

def Value.pp (ctx : PpContext) (v : Value) : String := valuePp ctx v
def Neutral.pp (ctx : PpContext) (n : Neutral) : String := neutralPp ctx n

mutual

partial def valueDoc (ctx : PpContext) (path : Path) (v : Value) : Doc :=
  .tagPath path <|
  match v with
  | .vType level =>
    match level with
    | .lit 0 => .text "Type"
    | .lit _ => .text s!"Type{Level.toSubscript level}"
    | _ => .text s!"Type{level}"
  | .vPi _qty binder name domain codomain =>
    let binderStr := binderPrefix binder
    let codVal := instantiateClosureForPp name domain codomain
    .group <|
      .text s!"({binderStr}{name} : " ++
      .nest 2 (valueDoc ctx (path.push .piDomain) domain) ++
      .text ")" ++
      .nest 2 (.softline ++ .text "-> " ++
        valueDoc ctx (path.push .piCodomain) codVal)
  | .vLam name body =>
    let bodyVal := instantiateClosureForPp name .type0 body
    .group <|
      .text s!"fun({name}) => " ++
      .nest 2 (valueDoc ctx (path.push .lamBody) bodyVal)
  | .vNeutral _ neu => neutralDoc ctx path neu
  | .vRowSort => .text "Row"
  | .vLabelSort => .text "Label"
  | .vIntLit n => .text (toString n)
  | .vFloatLit f => .text (toString f)
  | .vStringLit s => .text s!"\"{s}\""
  | .vRowEmpty => .text "{}"
  | .vRowExtend label fieldTy tail =>
    .group <|
      .text "{ " ++
      .nest 2 (
        valueDoc ctx (path.push .rowLabel) label ++
        .text " : " ++
        valueDoc ctx (path.push .rowField) fieldTy ++
        .softline ++ .text "| " ++
        valueDoc ctx (path.push .rowTail) tail) ++
      .text " }"
  | .vRecord row =>
    .group <|
      .text "{ " ++ valueDoc ctx (path.push .recordRow) row ++ .text " }"
  | .vVariant row =>
    .group <|
      .text "< " ++ valueDoc ctx (path.push .variantRow) row ++ .text " >"
  | .vLabelLit name => .text s!"'{name}"
  | .vRecordVal fields =>
    let inner : Doc := Id.run do
      let mut acc : Doc := .empty
      let mut first := true
      for (n, fv) in fields do
        if !first then acc := acc ++ .text "," ++ .softline
        first := false
        acc := acc ++ .text s!"{n} = " ++
          valueDoc ctx (path.push (.recordField n)) fv
      return acc
    .group <| .text "{ " ++ .nest 2 inner ++ .text " }"
  | .vDataType id params =>
    if ctx.eqInductiveId == some id then
      match params with
      | [_ty, lhs, rhs] =>
        .group <|
          valueDoc ctx (path.push (.dataTypeParam 1)) lhs ++
          .nest 2 (.softline ++ .text "= " ++
            valueDoc ctx (path.push (.dataTypeParam 2)) rhs)
      | _ =>
        let inner : Doc := Id.run do
          let mut acc : Doc := .text id.original
          let mut idx := 0
          for p in params do
            acc := acc ++ .softline ++
              valueDoc ctx (path.push (.dataTypeParam idx)) p
            idx := idx + 1
          return acc
        .group <| .nest 2 inner
    else if params.isEmpty then .text id.original
    else
      let inner : Doc := Id.run do
        let mut acc : Doc := .text id.original
        let mut idx := 0
        for p in params do
          acc := acc ++ .softline ++
            valueDoc ctx (path.push (.dataTypeParam idx)) p
          idx := idx + 1
        return acc
      .group <| .nest 2 inner
  | .vConstructor name _ args _ =>
    if args.isEmpty then .text name.display
    else
      let inner : Doc := Id.run do
        let mut acc : Doc := .text name.display
        let mut idx := 0
        for a in args do
          acc := acc ++ .softline ++
            valueDoc ctx (path.push (.constructorArg idx)) a
          idx := idx + 1
        return acc
      .group <| .nest 2 inner

partial def neutralDoc (ctx : PpContext) (path : Path) (neu : Neutral) : Doc :=
  let acc : Doc := Id.run do
    let mut acc := headDoc ctx path neu.head
    let mut idx := 0
    for e in neu.spine do
      match e with
      | .eApp arg =>
        acc := acc ++ .softline ++ valueDoc ctx (path.push (.spineArg idx)) arg
      | .eField name =>
        acc := acc ++ .tagPath (path.push (.spineField name)) (.text s!".{name}")
      idx := idx + 1
    return acc
  .group <| .nest 2 acc

partial def headDoc (ctx : PpContext) (_path : Path) (h : Head) : Doc :=
  .text (headPp ctx h)

end

/-- Pretty-print a value with full path-to-span tracking -/
def Value.ppWithSpans (ctx : PpContext) (v : Value)
    (startCol : Nat := 0) : Rendered :=
  Doc.render (valueDoc ctx Path.empty v) ctx.maxWidth startCol

@[deprecated Rendered (since := "05-15-2026")]
abbrev PpOutput := Rendered

end Soma.Core
