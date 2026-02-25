import Soma.Syntax
import Soma.Core.Module
import Soma.Core.Function

namespace Soma.Dependent.Lower

open Soma.Syntax
open Soma (UniqueSupply)
open Soma.Core

structure Result where
  module : Soma.Core.UntypedModule
  diagnostics : Diagnostics

private def isSimpleVarPattern : Syntax.Pattern → Bool
  | .var _ => true
  | .wildcard _ => true
  | .parens inner _ => isSimpleVarPattern inner
  | .typed inner _ _ => isSimpleVarPattern inner
  | _ => false

private def extractVarName : Syntax.Pattern → String
  | .var n => n.value
  | .parens inner _ => extractVarName inner
  | .typed inner _ _ => extractVarName inner
  | _ => "_"

private partial def explicitArityOfType : Syntax.TypeExpr → Nat
  | .arrow _ to _ => 1 + explicitArityOfType to
  | .pi _ _ _ cod _ => 1 + explicitArityOfType cod
  | .implicit _ _ cod _ => explicitArityOfType cod
  | .forall_ _ body _ => explicitArityOfType body
  | .constrained _ body _ => explicitArityOfType body
  | .parens inner _ => explicitArityOfType inner
  | .kinded ty _ _ => explicitArityOfType ty
  | _ => 0

private def functionAttrsFromSyntax
    (attrs : Array Syntax.Attribute)
    (defaultExternName : Option String := none)
  : FunctionAttrs :=
  let externAttr := attrs.find? fun a => a.name.value == "extern"
  let externName := match externAttr with
    | some attr =>
      match attr.args[0]? with
      | some (Syntax.Expr.lit (Syntax.Literal.string s _)) => some s
      | _ => defaultExternName
    | none => none
  {
    inline := attrs.any fun a => a.name.value == "inline"
    noInline := attrs.any fun a => a.name.value == "noinline"
    total := attrs.any fun a => a.name.value == "total"
    deprecated := none
    extern := externName
    intrinsic := attrs.any fun a => a.name.value == "intrinsic"
  }

private def mkGlobalName
    (name : String)
  (attrs : FunctionAttrs)
    (supply : UniqueSupply)
  : Soma.Core.QualifiedName × UniqueSupply :=
  let _ := attrs
  let (u, s') := supply.fresh name
  (⟨u⟩, s')

private def registerGlobalNames
    (ast : Syntax.Module)
  : Std.HashMap String Soma.Core.QualifiedName × UniqueSupply :=
  Id.run do
    let mut supply := UniqueSupply.initial ast.name
    let mut names : Std.HashMap String Soma.Core.QualifiedName := {}

    for decl in ast.decls do
      match decl with
      | .def_ attrs name _ _ _ _ =>
        if names.get? name.value |>.isNone then
          let fnAttrs := functionAttrsFromSyntax attrs (some name.value)
          let (n, s') := mkGlobalName name.value fnAttrs supply
          supply := s'
          names := names.insert name.value n
      | .trait _ _ _ _ methods _ =>
        for m in methods do
          if names.get? m.name.value |>.isNone then
            let (u, s') := supply.fresh m.name.value
            supply := s'
            names := names.insert m.name.value ⟨u⟩
      | .instance_ _ _ _ _ methods _ =>
        for methodDecl in methods do
          match methodDecl with
          | .def_ attrs methodName _ _ _ _ =>
            if names.get? methodName.value |>.isNone then
              let fnAttrs := functionAttrsFromSyntax attrs (some methodName.value)
              let (n, s') := mkGlobalName methodName.value fnAttrs supply
              supply := s'
              names := names.insert methodName.value n
          | _ => pure ()
      | _ => pure ()

    (names, supply)

private def allSimplePatterns (patterns : Array Syntax.Pattern) : Bool :=
  patterns.all isSimpleVarPattern

private def lowerFunctionDecl
    (decl : Syntax.Decl)
  (globalNames : Std.HashMap String Soma.Core.QualifiedName)
  : Option Soma.Core.UntypedFunction × Diagnostics :=
  Id.run do
    match decl with
    | .def_ attrs name headerParams sig clauses span =>
      let fnAttrs := functionAttrsFromSyntax attrs (some name.value)
      let globalName := globalNames.getD name.value ⟨{ id := 0, module := "", original := name.value }⟩
      match clauses[0]? with
      | some clause =>
        let hasPatternClauses := clauses.any (fun c => c.patterns.size > 0)
        if hasPatternClauses then
          if let some sigTy := sig then
            let totalArity := explicitArityOfType sigTy
            let expectedArity := totalArity - headerParams.size
            if let some badClause := clauses.find? (fun c => c.patterns.size != expectedArity) then
              let d := Diagnostic.error
                (s!"definition '{name.value}' expects {expectedArity} pattern(s) from its signature, but got {badClause.patterns.size}")
                badClause.span
              return (none, #[d])

        let headerParamNames := headerParams.map (·.name.value)
        if allSimplePatterns clause.patterns then
          let params := headerParamNames ++ (clause.patterns.map extractVarName)
          return (some {
            name := globalName
            params := params
            body := clause.body
            span := span
            declaredTypeSyntax := sig
            closureInfo := none
            attrs := fnAttrs
          }, #[])

        let numClauseParams := clause.patterns.size
        let clauseParams := (List.range numClauseParams).toArray.map fun i => s!"_arg{i}"
        let params := headerParamNames ++ clauseParams
        let scrutineeSyntax : Array Syntax.Expr := clauseParams.map fun paramName =>
          Syntax.Expr.var ⟨paramName, span⟩
        let armsSyntax : Array Syntax.MatchArm := clauses.map fun c =>
          Syntax.MatchArm.mk c.patterns c.guard c.body c.span
        let caseSyntax := Syntax.Expr.case scrutineeSyntax armsSyntax span
        return (some {
          name := globalName
          params := params
          body := caseSyntax
          span := span
          declaredTypeSyntax := sig
          closureInfo := none
          attrs := fnAttrs
        }, #[])
      | none =>
        if fnAttrs.intrinsic || fnAttrs.extern.isSome then
          let body := Syntax.Expr.lit
            (Syntax.Literal.string s!"{if fnAttrs.intrinsic then "intrinsic" else "extern"}:{name.value}" span)
          return (some {
            name := globalName
            params := #[]
            body := body
            span := span
            declaredTypeSyntax := sig
            closureInfo := none
            attrs := fnAttrs
          }, #[])
        let d := Diagnostic.error
          (s!"definition '{name.value}' must have at least one clause or be marked @[intrinsic]/@[extern]")
          span
        return (none, #[d])
    | _ =>
      return (none, #[])

private def lowerTypeDecl
    (decl : Syntax.Decl)
    (supply : UniqueSupply)
  : Option Soma.Core.UntypedTypeDef × UniqueSupply :=
  match decl with
  | .inductive attrs name params constructors _ _ =>
    let (typeUnique, supply') := supply.fresh name.value
    let typeName : Soma.Core.QualifiedName := ⟨typeUnique⟩
    let typeVarNames := params.map (·.name.value)
    let ctors := Id.run do
      let mut acc : Array Soma.Core.UntypedConstructor := #[]
      let mut supply'' := supply'
      for i in [:constructors.size] do
        if hIdx : i < constructors.size then
          let ctor : Syntax.DataCon := constructors[i]'hIdx
          let (ctorUnique, supplyNext) := supply''.fresh ctor.name.value
          supply'' := supplyNext
          let ctorName : Soma.Core.QualifiedName := ⟨ctorUnique⟩
          let lowered : Soma.Core.UntypedConstructor := match ctor.sig with
            | some sig => { name := ctorName, tag := i, fieldTypeSyntax := #[], sigSyntax := some sig, attrs := ctor.attrs }
            | none =>
              let fieldTypes := ctor.fields.map (·.2)
              { name := ctorName, tag := i, fieldTypeSyntax := fieldTypes, sigSyntax := none, attrs := ctor.attrs }
          acc := acc.push lowered
      (acc, supply'')
    let (ctors, supply'') := ctors
    (some (.algebraic attrs typeName typeVarNames ctors), supply'')
  | .record attrs name params _ctorName fields _ =>
    let (typeUnique, supply') := supply.fresh name.value
    let typeName : Soma.Core.QualifiedName := ⟨typeUnique⟩
    let typeVarNames := params.map (·.name.value)
    let (ctorUnique, supply'') := supply'.fresh "New"
    let ctorQName : Soma.Core.QualifiedName := ⟨ctorUnique⟩
    let fieldsWithOptNames := fields.map fun field =>
      (field.name.map (·.value), field.type_)
    (some (.record attrs typeName typeVarNames ctorQName fieldsWithOptNames), supply'')
  | _ => (none, supply)

private def lowerTypeClassDecl
    (decl : Syntax.Decl)
  (globalNames : Std.HashMap String Soma.Core.QualifiedName)
    (supply : UniqueSupply)
  : Option Soma.Core.TypeClassMeta × UniqueSupply :=
  match decl with
  | .trait _ name params constraints methods span =>
    let className :=
      match globalNames.get? name.value with
      | some n => n
      | none =>
        let (u, _) := supply.fresh name.value
        ⟨u⟩
    let methodSigs := methods.map fun m =>
      let mName := globalNames.getD m.name.value ⟨{ id := 0, module := "", original := m.name.value }⟩
      (mName, m.type_)
    (some {
      name := className
      params := params
      superclasses := constraints
      methodSignatures := methodSigs
      span := span
    }, supply)
  | _ => (none, supply)

private def lowerInstanceDecl
    (decl : Syntax.Decl)
  (globalNames : Std.HashMap String Soma.Core.QualifiedName)
  : Option Soma.Core.UntypedInstance × Diagnostics :=
  match decl with
  | .instance_ _ traitName args constraints methods span =>
    let (methodFns, diags) := Id.run do
      let mut fns : Array Soma.Core.UntypedFunction := #[]
      let mut ds : Diagnostics := #[]
      for methodDecl in methods do
        let (fn?, fnDiags) := lowerFunctionDecl methodDecl globalNames
        ds := ds ++ fnDiags
        if let some fn := fn? then
          fns := fns.push fn
      (fns, ds)
    (some {
      className := traitName.value
      typeArgsSyntax := args
      constraintsSyntax := constraints
      methods := methodFns
      span := span
    }, diags)
  | _ => (none, #[])

private def lowerAbbrevDecl (decl : Syntax.Decl) : Option Soma.Core.TypeAbbrev :=
  match decl with
  | .abbrev name params expansion span =>
    some {
      name := name.value
      params := params.map (·.value)
      expansion := expansion
      span := span
    }
  | _ => none

/-- Lower a parsed syntax module directly to `UntypedModule` for type checking. -/
def lowerModule (ast : Syntax.Module) : Result :=
  Id.run do
    let (globalNames, supply0) := registerGlobalNames ast
    let mut supply := supply0
    let mut functions : Array Soma.Core.UntypedFunction := #[]
    let mut types : Array Soma.Core.UntypedTypeDef := #[]
    let mut instances : Array Soma.Core.UntypedInstance := #[]
    let mut typeClasses : Array Soma.Core.TypeClassMeta := #[]
    let mut abbreviations : Array Soma.Core.TypeAbbrev := #[]
    let mut diagnostics : Diagnostics := #[]

    for decl in ast.decls do
      let (fn?, fnDiags) := lowerFunctionDecl decl globalNames
      diagnostics := diagnostics ++ fnDiags
      if let some fn := fn? then
        functions := functions.push fn

      let (td?, supply') := lowerTypeDecl decl supply
      supply := supply'
      if let some td := td? then
        types := types.push td

      let (tc?, supply'') := lowerTypeClassDecl decl globalNames supply
      supply := supply''
      if let some tc := tc? then
        typeClasses := typeClasses.push tc

      let (inst?, instDiags) := lowerInstanceDecl decl globalNames
      diagnostics := diagnostics ++ instDiags
      if let some inst := inst? then
        instances := instances.push inst

      if let some ab := lowerAbbrevDecl decl then
        abbreviations := abbreviations.push ab

    {
      module := {
        name := ast.name
        functions := functions
        types := types
        instances := instances
        typeClasses := typeClasses
        abbreviations := abbreviations
      }
      diagnostics := diagnostics
    }

end Soma.Dependent.Lower
