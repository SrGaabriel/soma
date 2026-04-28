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
  uniqueSupply : Soma.UniqueSupply


private def isSimpleVarPattern : Syntax.Pattern → Bool
  | .var _ => true
  | .wildcard _ => true
  | .parens inner _ => isSimpleVarPattern inner
  | .typed inner _ _ => isSimpleVarPattern inner
  | _ => false

private def extractVarName : Syntax.Pattern → String
  | .var n => n.name
  | .parens inner _ => extractVarName inner
  | .typed inner _ _ => extractVarName inner
  | _ => "_"

/-- Count the minimum explicit parameter arity visible in a type expression -/
private partial def explicitArityOfType : Syntax.Expr → Option Nat
  | .arrow _ to _ => (explicitArityOfType to).map (· + 1)
  | .pi _ binder _ _ cod _ =>
      if binder == .explicit then
        (explicitArityOfType cod).map (· + 1)
      else
        explicitArityOfType cod
  | .forall_ _ body _ => explicitArityOfType body
  | .parens inner _ => explicitArityOfType inner
  | .typeAnnot ty _ _ => explicitArityOfType ty
  | .app _ _ _ => none
  | _ => some 0

/-- Collect the user-written binder names for each explicit Π -/
private partial def explicitBinderNames : Syntax.Expr → List String
  | .arrow _ to _ => "_" :: explicitBinderNames to
  | .pi _ binder name _ cod _ =>
      if binder == .explicit then
        name.name :: explicitBinderNames cod
      else
        explicitBinderNames cod
  | .forall_ _ body _ => explicitBinderNames body
  | .parens inner _ => explicitBinderNames inner
  | .typeAnnot ty _ _ => explicitBinderNames ty
  | _ => []

private def functionAttrsFromSyntax
    (attrs : Array Syntax.Attribute)
    (defaultExternName : Option String := none)
  : FunctionAttrs :=
  let externAttr := attrs.find? fun a => a.name.name == "extern"
  let externName := match externAttr with
    | some attr =>
      match attr.args[0]? with
      | some (Syntax.Expr.lit (Syntax.Literal.string s _)) => some s
      | _ => defaultExternName
    | none => none
  let intrinsicAttr := attrs.find? fun a => a.name.name == "intrinsic"
  let intrinsicTag := match intrinsicAttr with
    | some attr =>
      match attr.args[0]? with
      | some (Syntax.Expr.lit (Syntax.Literal.string s _)) => some s
      | _ => some ""
    | none => none
  let wiredInAttr := attrs.find? fun a => a.name.name == "wired_in"
  let wiredInRole := match wiredInAttr with
    | some attr =>
      match attr.args[0]? with
      | some (Syntax.Expr.lit (Syntax.Literal.string s _)) => some s
      | _ => none
    | none => none
  {
    inline := attrs.any fun a => a.name.name == "inline"
    noInline := attrs.any fun a => a.name.name == "noinline"
    total := attrs.any fun a => a.name.name == "total"
    partial_ := attrs.any fun a => a.name.name == "partial"
    irreducible := attrs.any fun a => a.name.name == "irreducible"
    deprecated := none
    extern := externName
    intrinsic := intrinsicTag
    wiredIn := wiredInRole
  }

private def mkGlobalName
    (name : String)
  (attrs : FunctionAttrs)
    (supply : UniqueSupply)
  : Soma.Core.QualifiedName × UniqueSupply :=
  let _ := attrs
  let (u, s') := supply.fresh name
  (⟨u⟩, s')

/-- Pre-registered names, split into two namespaces -/
structure GlobalNameRegistry where
  /-- Top-level names: types, functions, trait methods -/
  topLevel : Std.HashMap String Soma.Core.QualifiedName := {}
  /-- Constructor names: keyed by (parentTypeName, ctorSimpleName) -/
  ctors : Std.HashMap (String × String) Soma.Core.QualifiedName := {}

def GlobalNameRegistry.requireTopLevel (reg : GlobalNameRegistry) (name : String) : Soma.Core.QualifiedName :=
  match reg.topLevel.get? name with
  | some qn => qn
  | none => panic! s!"internal error: no pre-registered top-level name for '{name}'"

def GlobalNameRegistry.requireCtor (reg : GlobalNameRegistry) (parentType : String) (ctorName : String) : Soma.Core.QualifiedName :=
  match reg.ctors.get? (parentType, ctorName) with
  | some qn => qn
  | none => panic! s!"internal error: no pre-registered constructor name for '{parentType}::{ctorName}'"

private def registerGlobalNames
    (ast : Syntax.Module)
  : GlobalNameRegistry × UniqueSupply :=
  Id.run do
    let mut supply := UniqueSupply.initial ast.name
    let mut topLevel : Std.HashMap String Soma.Core.QualifiedName := {}
    let mut ctors : Std.HashMap (String × String) Soma.Core.QualifiedName := {}

    for decl in ast.decls do
      match decl with
      | .def_ attrs name _ _ _ _ | .theorem_ attrs name _ _ _ _ =>
        if topLevel.get? name.name |>.isNone then
          let fnAttrs := functionAttrsFromSyntax attrs (some name.name)
          let (n, s') := mkGlobalName name.name fnAttrs supply
          supply := s'
          topLevel := topLevel.insert name.name n
      | .inductive _ name _ constructors _ _ =>
        if topLevel.get? name.name |>.isNone then
          let (u, s') := supply.fresh name.name
          supply := s'
          topLevel := topLevel.insert name.name ⟨u⟩
        for ctor in constructors do
          let key := (name.name, ctor.name.name)
          if ctors.get? key |>.isNone then
            let (u, s') := supply.fresh ctor.name.name
            supply := s'
            ctors := ctors.insert key ⟨u⟩
      | .record _ name _ _ _ _ =>
        if topLevel.get? name.name |>.isNone then
          let (u, s') := supply.fresh name.name
          supply := s'
          topLevel := topLevel.insert name.name ⟨u⟩
      | .trait _ name _ methods _ =>
        if topLevel.get? name.name |>.isNone then
          let (u, s') := supply.fresh name.name
          supply := s'
          topLevel := topLevel.insert name.name ⟨u⟩
        for m in methods do
          if topLevel.get? m.name.name |>.isNone then
            let (u, s') := supply.fresh m.name.name
            supply := s'
            topLevel := topLevel.insert m.name.name ⟨u⟩
      | _ => pure ()

    ({ topLevel, ctors }, supply)

private def allSimplePatterns (patterns : Array Syntax.Pattern) : Bool :=
  patterns.all isSimpleVarPattern

/-- Core function lowering logic -/
private def lowerFunctionDeclCore
    (decl : Syntax.Decl)
    (globalName : Soma.Core.QualifiedName)
  : Option Soma.Core.UntypedFunction × Diagnostics :=
  Id.run do
    match decl with
    | .def_ attrs name headerParams sig clauses span
    | .theorem_ attrs name headerParams sig clauses span =>
      let fnAttrs := functionAttrsFromSyntax attrs (some name.name)
      match clauses[0]? with
      | some clause =>
        let hasPatternClauses := clauses.any (fun c => c.patterns.size > 0)
        if hasPatternClauses then
          if let some sigTy := sig then
            -- Arity check: only validate when the syntactic type is fully known
            match explicitArityOfType sigTy with
            | some totalArity =>
              let explicitHeaderParams := headerParams.filter (!·.isImplicit)
              let expectedArity := totalArity - explicitHeaderParams.size
              if let some badClause := clauses.find? (fun c => c.patterns.size != expectedArity) then
                return (none, #[Diagnostic.error
                  (s!"definition '{name.name}' expects {expectedArity} pattern(s) from its signature, but got {badClause.patterns.size}")
                  badClause.span])
            | none => pure ()  -- Alias application in tail: defer arity check to elaborator

        let headerParamNames := (headerParams.filter (!·.isImplicit)).map (·.name.name)
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

        let sigBinderNames : List String :=
          match sig with
          | some s =>
            let all := explicitBinderNames s
            all.drop headerParamNames.size
          | none => []
        let sigBinderArr : Array String := sigBinderNames.toArray
        let numClauseParams := clause.patterns.size
        let clauseParams := (List.range numClauseParams).toArray.map fun i =>
          if h : i < sigBinderArr.size then
            let n := sigBinderArr[i]
            -- TODO: review
            if n == "_" then s!"_arg{i}" else n
          else
            s!"_arg{i}"
        let params := headerParamNames ++ clauseParams
        let scrutineeSyntax : Array Syntax.Expr := clauseParams.map fun paramName =>
          Syntax.Expr.var ⟨#[], paramName, span⟩
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
        if fnAttrs.intrinsic.isSome || fnAttrs.extern.isSome then
          let body := Syntax.Expr.lit
            (Syntax.Literal.string s!"{if fnAttrs.intrinsic.isSome then "intrinsic" else "extern"}:{name.name}" span)
          return (some {
            name := globalName
            params := #[]
            body := body
            span := span
            declaredTypeSyntax := sig
            closureInfo := none
            attrs := fnAttrs
            isExternStub := true
          }, #[])
        if sig.isSome then
          let headerExplicitNames := (headerParams.filter (!·.isImplicit)).map (·.name.name)
          return (some {
            name := globalName
            params := headerExplicitNames
            body := Syntax.Expr.lit (Syntax.Literal.string "" span)
            span := span
            declaredTypeSyntax := sig
            closureInfo := none
            attrs := fnAttrs
            isBodilessExFalso := true
          }, #[])
        let d := Diagnostic.error
          (s!"definition '{name.name}' must have a body, at least one clause, an @[intrinsic]/@[extern] attribute, or a type signature")
          span
        return (none, #[d])
    | _ =>
      return (none, #[])

private def lowerFunctionDecl
    (decl : Syntax.Decl)
    (registry : GlobalNameRegistry)
  : Option Soma.Core.UntypedFunction × Diagnostics :=
  match decl with
  | .def_ _ name .. | .theorem_ _ name .. =>
    let globalName := registry.requireTopLevel name.name
    lowerFunctionDeclCore decl globalName
  | _ => (none, #[])

/-- Maximum number of constructors per data type -/
private def maxConstructors : Nat := 255

/-- Walk a type-level head-kind annotation like `A -> B -> Type` and
    project it into a telescope of anonymous binders `(_ : A) (_ : B)` -/
private partial def unfoldKindTelescope (e : Syntax.Expr) (defaultSpan : Span)
    : Array Syntax.TypeVarBinder :=
  match e with
  | .arrow from_ to _ =>
    let head : Syntax.TypeVarBinder :=
      .mk ⟨#[], "_", defaultSpan⟩ (some from_)
    #[head] ++ unfoldKindTelescope to defaultSpan
  | .pi _qty _binder name dom cod _ =>
    let head : Syntax.TypeVarBinder := .mk name (some dom)
    #[head] ++ unfoldKindTelescope cod defaultSpan
  | .parens inner _ => unfoldKindTelescope inner defaultSpan
  | _ => #[]

/-- Recognise the final sort at the tail of a kind annotation -/
private partial def headSortOfKind : Option Syntax.Expr → Soma.Core.Level
  | none => .lit 0
  | some (.con ⟨_, "Prop", _⟩) => .prop
  | some (.var ⟨_, "Prop", _⟩) => .prop
  | some (.parens inner _) => headSortOfKind (some inner)
  | some (.arrow _ to _) => headSortOfKind (some to)
  | some (.pi _ _ _ _ cod _) => headSortOfKind (some cod)
  | _ => .lit 0

private def lowerTypeDecl
    (decl : Syntax.Decl)
    (registry : GlobalNameRegistry)
    (supply : UniqueSupply)
  : Option Soma.Core.UntypedTypeDef × Diagnostics × UniqueSupply :=
  match decl with
  | .inductive attrs name params constructors kindAnnot span =>
    let diags : Diagnostics :=
      if constructors.size > maxConstructors then
        #[Diagnostic.error
          s!"data type '{name.name}' has {constructors.size} constructors, exceeding the maximum of {maxConstructors}"
          span]
      else #[]
    let typeName := registry.requireTopLevel name.name
    let extraBinders : Array Syntax.TypeVarBinder :=
      match kindAnnot with
      | none => #[]
      | some k => unfoldKindTelescope k span
    let fullParams := params ++ extraBinders
    let ctors := Id.run do
      let mut acc : Array Soma.Core.UntypedConstructor := #[]
      for i in [:constructors.size] do
        if hIdx : i < constructors.size then
          let ctor : Syntax.DataCon := constructors[i]'hIdx
          let ctorName := registry.requireCtor name.name ctor.name.name
          let lowered : Soma.Core.UntypedConstructor := match ctor.sig with
            | some sig => { name := ctorName, tag := i, fieldTypeSyntax := #[], sigSyntax := some sig, attrs := ctor.attrs }
            | none =>
              let fieldTypes := ctor.fields.map (·.2)
              { name := ctorName, tag := i, fieldTypeSyntax := fieldTypes, sigSyntax := none, attrs := ctor.attrs }
          acc := acc.push lowered
      acc
    let headSort := headSortOfKind kindAnnot
    (some (.algebraic attrs typeName fullParams ctors headSort span), diags, supply)
  | .record attrs name params _ctorName fields span =>
    let typeName := registry.requireTopLevel name.name
    let (ctorUnique, supply'') := supply.fresh "New"
    let ctorQName : Soma.Core.QualifiedName := ⟨ctorUnique⟩
    let fieldsWithOptNames := fields.map fun field =>
      (field.name.map (·.name), field.type_)
    (some (.record attrs typeName params ctorQName fieldsWithOptNames span), #[], supply'')
  | _ => (none, #[], supply)

/-- Rewrite single-field record types in arrow-domain position -/
private partial def rewriteRecordArrowsAsImplicits : Syntax.Expr → Syntax.Expr
  | .arrow (.recordTy #[(name, ty)] none _) body span =>
    .pi .omega .instance_ name
       (rewriteRecordArrowsAsImplicits ty)
       (rewriteRecordArrowsAsImplicits body) span
  | .arrow from_ to span =>
    .arrow (rewriteRecordArrowsAsImplicits from_) (rewriteRecordArrowsAsImplicits to) span
  | .forall_ vars body span =>
    .forall_ vars (rewriteRecordArrowsAsImplicits body) span
  | .parens inner span =>
    .parens (rewriteRecordArrowsAsImplicits inner) span
  | .pi qty binder name dom cod span =>
    .pi qty binder name
       (rewriteRecordArrowsAsImplicits dom)
       (rewriteRecordArrowsAsImplicits cod) span
  | .sigma qty name fst snd span =>
    .sigma qty name
       (rewriteRecordArrowsAsImplicits fst)
       (rewriteRecordArrowsAsImplicits snd) span
  | .app fn arg span =>
    .app (rewriteRecordArrowsAsImplicits fn) (rewriteRecordArrowsAsImplicits arg) span
  | other => other

private def lowerTypeClassDecl
    (decl : Syntax.Decl)
    (registry : GlobalNameRegistry)
    (supply : UniqueSupply)
  : Option Soma.Core.TypeClassMeta × UniqueSupply :=
  match decl with
  | .trait _ name binders methods span =>
    let className := registry.requireTopLevel name.name
    let methodSigs := methods.map fun m =>
      let mName := registry.requireTopLevel m.name.name
      (mName, rewriteRecordArrowsAsImplicits m.type_)
    (some {
      name := className
      binders := binders
      methodSignatures := methodSigs
      span := span
    }, supply)
  | _ => (none, supply)

/-- Lower a function declaration using an explicitly provided QualifiedName. -/
private def lowerFunctionDeclWithName
    (decl : Syntax.Decl)
    (globalName : Soma.Core.QualifiedName)
  : Option Soma.Core.UntypedFunction × Diagnostics :=
  lowerFunctionDeclCore decl globalName

private def lowerInstanceDecl
    (decl : Syntax.Decl)
    (supply : UniqueSupply)
  : Option Soma.Core.UntypedInstance × Diagnostics × UniqueSupply :=
  match decl with
  | .instance_ _ binders traitName args methods span =>
    let (methodFns, diags, supply') := Id.run do
      let mut fns : Array Soma.Core.UntypedFunction := #[]
      let mut ds : Diagnostics := #[]
      let mut sup := supply
      for methodDecl in methods do
        match methodDecl with
        | .def_ _ methodName _ _ _ _ =>
          let (u, sup') := sup.fresh methodName.name
          sup := sup'
          let methodQN : Soma.Core.QualifiedName := ⟨u⟩
          let (fn?, fnDiags) := lowerFunctionDeclWithName methodDecl methodQN
          ds := ds ++ fnDiags
          if let some fn := fn? then
            fns := fns.push fn
        | _ => pure ()
      (fns, ds, sup)
    (some {
      className := traitName
      typeArgsSyntax := args
      binders := binders
      methods := methodFns
      span := span
    }, diags, supply')
  | _ => (none, #[], supply)

private def lowerAbbrevDecl (decl : Syntax.Decl) : Option Soma.Core.TypeAbbrev :=
  match decl with
  | .abbrev name params expansion span =>
    some {
      name := name.name
      params := params.map (·.name)
      expansion := expansion
      span := span
    }
  | _ => none

/-- Lower a parsed syntax module directly to `UntypedModule` for type checking. -/
def lowerModule (ast : Syntax.Module) : Result :=
  Id.run do
    let (registry, supply0) := registerGlobalNames ast
    let mut supply := supply0
    let mut functions : Array Soma.Core.UntypedFunction := #[]
    let mut theorems : Array Soma.Core.UntypedFunction := #[]
    let mut types : Array Soma.Core.UntypedTypeDef := #[]
    let mut instances : Array Soma.Core.UntypedInstance := #[]
    let mut typeClasses : Array Soma.Core.TypeClassMeta := #[]
    let mut abbreviations : Array Soma.Core.TypeAbbrev := #[]
    let mut diagnostics : Diagnostics := #[]

    for decl in ast.decls do
      let (fn?, fnDiags) := lowerFunctionDecl decl registry
      diagnostics := diagnostics ++ fnDiags
      if let some fn := fn? then
        -- Route to the right bucket based on the original declaration kind
        match decl with
        | .theorem_ _ name _ _ _ span =>
          if fn.attrs.partial_ then
            diagnostics := diagnostics.push (Diagnostic.error
              s!"theorem '{name.name}' cannot be marked @[partial]" span
              |>.withHelp "drop @[partial], or make this a `def` if it's runtime code")
          else
            theorems := theorems.push fn
        | _ => functions := functions.push fn

      let (td?, tdDiags, supply') := lowerTypeDecl decl registry supply
      diagnostics := diagnostics ++ tdDiags
      supply := supply'
      if let some td := td? then
        types := types.push td

      let (tc?, supply'') := lowerTypeClassDecl decl registry supply
      supply := supply''
      if let some tc := tc? then
        typeClasses := typeClasses.push tc

      let (inst?, instDiags, supply''') := lowerInstanceDecl decl supply
      diagnostics := diagnostics ++ instDiags
      supply := supply'''
      if let some inst := inst? then
        instances := instances.push inst

      if let some ab := lowerAbbrevDecl decl then
        abbreviations := abbreviations.push ab

    {
      module := {
        name := ast.name
        functions := functions
        theorems := theorems
        types := types
        instances := instances
        typeClasses := typeClasses
        abbreviations := abbreviations
      }
      diagnostics := diagnostics
      uniqueSupply := supply
    }

end Soma.Dependent.Lower
