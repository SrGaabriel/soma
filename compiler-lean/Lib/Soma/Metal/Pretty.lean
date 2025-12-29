/-
  Soma.Metal.Pretty
  Pretty printing for Metal IR (both typed and untyped).
-/
import Soma.Metal.Expr
import Soma.Metal.Function
import Soma.Metal.Module

namespace Soma.Metal.Pretty

open Soma.Metal
open Soma.Typing

/-- Configuration for pretty printing -/
structure Config where
  showTypes : Bool := false
  indent : Nat := 2

/-- Pretty print a type annotation if showTypes is enabled -/
def ppTypeAnnotation (cfg : Config) (ty : MonoTy) : String :=
  if cfg.showTypes then s!" : {ty}" else ""

/-- Pretty print a Unit annotation (for untyped) -/
def ppUnitAnnotation (_cfg : Config) (_u : Unit) : String := ""

/-- Class for pretty printing annotations -/
class PpAnnotation (α : Type) where
  ppAnnotation : Config → α → String

instance : PpAnnotation Unit where
  ppAnnotation := ppUnitAnnotation

instance : PpAnnotation MonoTy where
  ppAnnotation := ppTypeAnnotation

/-- Create indentation string -/
def mkIndent (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

/-- Pretty print a param list -/
def ppParamList [PpAnnotation α] (cfg : Config) : ParamList α → String
  | .nil => ""
  | .cons _ name info rest =>
    let paramStr := s!"{name}{PpAnnotation.ppAnnotation cfg info}"
    let restStr := ppParamList cfg rest
    if restStr.isEmpty then paramStr else s!"{paramStr}, {restStr}"

/-- Pretty print a pattern -/
partial def ppPattern [PpAnnotation α] (cfg : Config) : Pattern α → String
  | .var _ name info _ => name ++ PpAnnotation.ppAnnotation cfg info
  | .wildcard _ _ => "_"
  | .lit lit _ => toString lit
  | .ctor name args _ _ =>
    if args.isEmpty then
      name.display
    else
      s!"{name.display}({", ".intercalate (args.toList.map (ppPattern cfg))})"
  | .tuple elems _ _ =>
    s!"({", ".intercalate (elems.toList.map (ppPattern cfg))})"
  | .array elems _ _ =>
    s!"[{", ".intercalate (elems.toList.map (ppPattern cfg))}]"
  | .cons head tail _ _ =>
    s!"{ppPattern cfg head} :: {ppPattern cfg tail}"
  | .as _ name inner _ _ =>
    s!"{name}@{ppPattern cfg inner}"

/-- Pretty print a pattern list -/
def ppPatternList [PpAnnotation α] (cfg : Config) : PatternList α → List String
  | .nil => []
  | .cons p ps => ppPattern cfg p :: ppPatternList cfg ps

mutual

/-- Pretty print an expression -/
partial def ppExpr [PpAnnotation α] (cfg : Config) (indent : Nat) : Expr α scope → String
  | .var v info _ =>
    v.original ++ PpAnnotation.ppAnnotation cfg info
  | .lit lit _ =>
    toString lit
  | .call fn args info _ =>
    let fnStr := ppExpr cfg indent fn
    let argsStr := ppExprList cfg indent args
    let callStr := if argsStr.isEmpty then fnStr else s!"{fnStr}({", ".intercalate argsStr})"
    callStr ++ PpAnnotation.ppAnnotation cfg info
  | .let_ _ name value body info _ =>
    let ind := mkIndent indent
    let nextInd := indent + cfg.indent
    let valueStr := ppExpr cfg nextInd value
    let bodyStr := ppExpr cfg indent body
    s!"let {name}{PpAnnotation.ppAnnotation cfg info} = {valueStr}\n{ind}{bodyStr}"
  | .lam params body info _ =>
    let paramsStr := ppParamList cfg params
    let bodyStr := ppExpr cfg (indent + cfg.indent) body
    s!"(\\{paramsStr} -> {bodyStr}){PpAnnotation.ppAnnotation cfg info}"
  | .closure liftedName captures info _ =>
    let capsStr := ppCaptureList cfg indent captures
    s!"closure[{liftedName.display}]({capsStr}){PpAnnotation.ppAnnotation cfg info}"
  | .construct name _tag args info _ =>
    let argsStr := ppExprList cfg indent args
    if argsStr.isEmpty then
      name.display ++ PpAnnotation.ppAnnotation cfg info
    else
      s!"{name.display}({", ".intercalate argsStr}){PpAnnotation.ppAnnotation cfg info}"
  | .tuple elems info _ =>
    let elemsStr := ppExprList cfg indent elems
    s!"({", ".intercalate elemsStr}){PpAnnotation.ppAnnotation cfg info}"
  | .record fields info _ =>
    let fieldsStr := fields.toList.map (fun (name, expr) =>
      s!"{name} = {ppExpr cfg indent expr}") |> ", ".intercalate
    "{" ++ s!" {fieldsStr} " ++ "}" ++ PpAnnotation.ppAnnotation cfg info
  | .recordUpdate base updates info _ =>
    let baseStr := ppExpr cfg indent base
    let updatesStr := updates.toList.map (fun (name, expr) =>
      s!"{name} = {ppExpr cfg indent expr}") |> ", ".intercalate
    "{" ++ s!" {baseStr} | {updatesStr} " ++ "}" ++ PpAnnotation.ppAnnotation cfg info
  | .array elems info _ =>
    let elemsStr := ppExprList cfg indent elems
    s!"[{", ".intercalate elemsStr}]{PpAnnotation.ppAnnotation cfg info}"
  | .if_ cond then_ else_ info _ =>
    let ind := mkIndent indent
    let nextInd := indent + cfg.indent
    let condStr := ppExpr cfg indent cond
    let thenStr := ppExpr cfg nextInd then_
    let elseStr := ppExpr cfg nextInd else_
    s!"if {condStr}{PpAnnotation.ppAnnotation cfg info}\n{ind}then {thenStr}\n{ind}else {elseStr}"
  | .case scruts arms info _ =>
    let ind := mkIndent indent
    let scrutsStr := ppExprList cfg indent scruts
    let armsStr := ppArmList cfg (indent + cfg.indent) arms
    s!"case {", ".intercalate scrutsStr} of{PpAnnotation.ppAnnotation cfg info}\n{armsStr}"
  | .fieldAccess expr fieldName _idx info _ =>
    let exprStr := ppExpr cfg indent expr
    s!"{exprStr}.{fieldName}{PpAnnotation.ppAnnotation cfg info}"
  | .global name info _ =>
    name.display ++ PpAnnotation.ppAnnotation cfg info
  | .panic msg info _ =>
    s!"panic!(\"{msg}\"){PpAnnotation.ppAnnotation cfg info}"
  | .proj typeName fieldName _idx info _ =>
    s!"{typeName.display}.{fieldName}{PpAnnotation.ppAnnotation cfg info}"
  | .typeApp arg info _ =>
    let argStr := match arg with
      | .type ty => s!"@{ty.ty}"
      | .label name => s!"@{name}"
    s!"{argStr}{PpAnnotation.ppAnnotation cfg info}"

/-- Pretty print an expression list -/
partial def ppExprList [PpAnnotation α] (cfg : Config) (indent : Nat) : ExprList α scope → List String
  | .nil => []
  | .cons e es => ppExpr cfg indent e :: ppExprList cfg indent es

/-- Pretty print an arm -/
partial def ppArm [PpAnnotation α] (cfg : Config) (indent : Nat) : Arm α scope → String
  | .mk pats body _ =>
    let ind := mkIndent indent
    let patsStr := ", ".intercalate (ppPatternList cfg pats)
    let bodyStr := ppExpr cfg (indent + cfg.indent) body
    s!"{ind}| {patsStr} -> {bodyStr}"

/-- Pretty print an arm list -/
partial def ppArmList [PpAnnotation α] (cfg : Config) (indent : Nat) : ArmList α scope → String
  | .nil => ""
  | .cons a as =>
    let armStr := ppArm cfg indent a
    let restStr := ppArmList cfg indent as
    if restStr.isEmpty then armStr else s!"{armStr}\n{restStr}"

/-- Pretty print a capture list -/
partial def ppCaptureList [PpAnnotation α] (cfg : Config) (_indent : Nat) : CaptureList α scope → String
  | .nil => ""
  | .cons v info rest =>
    let varStr := s!"{v.original}{PpAnnotation.ppAnnotation cfg info}"
    let restStr := ppCaptureList cfg _indent rest
    if restStr.isEmpty then varStr else s!"{varStr}, {restStr}"

end

/-- Pretty print an untyped function -/
def ppUntypedFunction (cfg : Config) (fn : UntypedFunction) : String :=
  let paramsStr := fn.params.toList.map (·.2) |> ", ".intercalate
  let sigStr := match fn.declaredTypeSyntax with
    | some _ => " (has signature)"
    | none => ""
  let bodyStr := ppExpr (α := Unit) cfg cfg.indent fn.body
  s!"def {fn.name.display}({paramsStr}){sigStr} =\n{mkIndent cfg.indent}{bodyStr}"

/-- Pretty print a typed function -/
def ppTypedFunction (cfg : Config) (fn : Function) : String :=
  let paramsStr := fn.params.toList.map (fun (_, name, ty) =>
    if cfg.showTypes then s!"{name} : {ty}" else name) |> ", ".intercalate
  let retStr := if cfg.showTypes then s!" -> {fn.returnType}" else ""
  let bodyStr := ppExpr (α := MonoTy) cfg cfg.indent fn.body
  s!"def {fn.name.display}({paramsStr}){retStr} =\n{mkIndent cfg.indent}{bodyStr}"

/-- Pretty print an untyped instance -/
def ppUntypedInstance (cfg : Config) (inst : UntypedInstance) : String :=
  let methodsStr := inst.methods.toList.map (fun m =>
    let ind := mkIndent cfg.indent
    s!"{ind}{ppUntypedFunction { cfg with indent := cfg.indent * 2 } m}"
  ) |> "\n".intercalate
  s!"instance {inst.className} where\n{methodsStr}"

/-- Pretty print a typed instance -/
def ppTypedInstance (cfg : Config) (inst : Instance) : String :=
  let methodsStr := inst.methods.toList.map (fun m =>
    let ind := mkIndent cfg.indent
    s!"{ind}{ppTypedFunction { cfg with indent := cfg.indent * 2 } m}"
  ) |> "\n".intercalate
  s!"instance {inst.className} for {inst.instanceType} where\n{methodsStr}"

/-- Pretty print an untyped module -/
def ppUntypedModule (cfg : Config) (m : UntypedModule) : String :=
  let funcsStr := m.functions.toList.map (ppUntypedFunction cfg) |> "\n\n".intercalate
  let instsStr := m.instances.toList.map (ppUntypedInstance cfg) |> "\n\n".intercalate
  let sections := [
    s!"-- Module: {m.name}",
    if m.functions.isEmpty then "" else s!"-- Functions ({m.functions.size})\n\n{funcsStr}",
    if m.instances.isEmpty then "" else s!"-- Instances ({m.instances.size})\n\n{instsStr}"
  ].filter (· != "")
  "\n".intercalate sections

/-- Pretty print a typed module -/
def ppTypedModule (cfg : Config) (m : Module) : String :=
  let funcsStr := m.functions.toList.map (ppTypedFunction cfg) |> "\n\n".intercalate
  let instsStr := m.instances.toList.map (ppTypedInstance cfg) |> "\n\n".intercalate
  let sections := [
    s!"-- Module: {m.name}",
    if m.functions.isEmpty then "" else s!"-- Functions ({m.functions.size})\n\n{funcsStr}",
    if m.instances.isEmpty then "" else s!"-- Instances ({m.instances.size})\n\n{instsStr}"
  ].filter (· != "")
  "\n".intercalate sections

end Soma.Metal.Pretty
