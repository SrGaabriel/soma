import Soma.Core.Value
import Soma.Core.Expr

namespace Soma.Core

open Soma (Unique)

private partial def matchArmTagPure (arm : Arm) (tag : Nat) : Bool :=
  match arm.patterns[0]? with
  | some (Pattern.ctor _ t _) => t == tag
  | some Pattern.wildcard => true
  | some (Pattern.var _) => true
  | _ => false

mutual

/-- Pure closure application for quoting (no TCM, no metas) -/
partial def applyClosurePure (clos : Closure) (arg : Value) : Value :=
  match clos with
  | .const _ v => v
  | .term name env body =>
    let env' := env.extend name arg
    evalExprPure env' body

/-- Pure Expr evaluation for quoting (no TCM, no metas) -/
partial def evalExprPure (env : Env) (e : Expr) : Value :=
  match e with
  | .bvar idx =>
    let lvl := env.size - idx - 1
    match env.lookup ⟨lvl⟩ with
    | some v => v
    | none => .vNeutral .type0 (.nVar ⟨s!"bvar{idx}", ⟨env.size⟩⟩)
  | .fvar id =>
    match env.lookupByName id.original with
    | some v => v
    | none => .vNeutral .type0 (.nVar ⟨id.original, ⟨env.size⟩⟩)
  | .mvar id => .vNeutral .type0 (.nMeta id)
  | .const name => .vNeutral .type0 (.nVar ⟨name.display, ⟨0⟩⟩)
  | .lit l =>
    match l with
    | .int n => .vIntLit n
    | .string s => .vStringLit s
    | .bool true => .vConstructor ⟨⟨0, "", "True"⟩⟩ 0 []
    | .bool false => .vConstructor ⟨⟨0, "", "False"⟩⟩ 1 []
  | .sort level => .vType level
  | .primTy p => .vPrimTy p
  | .rowSort => .vRowSort
  | .labelSort => .vLabelSort
  | .rowEmpty => .vRowEmpty
  | .labelLit name => .vLabelLit name
  | .recordTy row => .vRecord (evalExprPure env row)
  | .variantTy row => .vVariant (evalExprPure env row)
  | .rowExtend label fieldTy tail =>
    .vRowExtend (evalExprPure env label) (evalExprPure env fieldTy) (evalExprPure env tail)
  | .pi qty _info name domain codomain =>
    let domVal := evalExprPure env domain
    .vPi qty _info name domVal (Closure.mkWithBody name env codomain)
  | .sigma qty _info name fst snd =>
    let fstVal := evalExprPure env fst
    .vSigma qty name fstVal (Closure.mkWithBody name env snd)
  | .pair fst snd => .vPair (evalExprPure env fst) (evalExprPure env snd)
  | .projFst e =>
    match evalExprPure env e with
    | .vPair f _ => f
    | _ => .vNeutral .type0 (.nVar ⟨"fst", ⟨env.size⟩⟩)
  | .projSnd e =>
    match evalExprPure env e with
    | .vPair _ s => s
    | _ => .vNeutral .type0 (.nVar ⟨"snd", ⟨env.size⟩⟩)
  | .app fn arg =>
    let fnVal := evalExprPure env fn
    let argVal := evalExprPure env arg
    match fnVal with
    | .vLam _ body => applyClosurePure body argVal
    | .vNeutral ty neu => .vNeutral ty (.nApp neu argVal)
    | .vDataType id params => .vDataType id (params ++ [argVal])
    | other => other
  | .lam _info name _domain body =>
    .vLam name (Closure.mkWithBody name env body)
  | .let_ name _ty val body =>
    let valV := evalExprPure env val
    evalExprPure (env.extend name valV) body
  | .if_ cond then_ else_ =>
    match evalExprPure env cond with
    | .vConstructor _ 0 _ => evalExprPure env then_
    | .vConstructor _ 1 _ => evalExprPure env else_
    | _ => .vNeutral .type0 (.nVar ⟨"if", ⟨env.size⟩⟩)
  | .record fields =>
    .vRecordVal (fields.toList.map fun (n, e) => (n, evalExprPure env e))
  | .recordUpdate base updates =>
    let baseVal := evalExprPure env base
    match baseVal with
    | .vRecordVal fields =>
      let updates' := updates.toList.map fun (n, e) => (n, evalExprPure env e)
      let merged := fields.map fun (n, v) =>
        match updates'.find? (·.1 == n) with
        | some (_, newV) => (n, newV)
        | none => (n, v)
      .vRecordVal merged
    | _ => baseVal
  | .fieldAccess e field _idx =>
    match evalExprPure env e with
    | .vRecordVal fields =>
      match fields.find? (·.1 == field) with
      | some (_, v) => v
      | none => .vNeutral .type0 (.nFieldAccess (.nVar ⟨"rec", ⟨env.size⟩⟩) field)
    | _ => .vNeutral .type0 (.nFieldAccess (.nVar ⟨"rec", ⟨env.size⟩⟩) field)
  | .construct name tag args =>
    .vConstructor name tag (args.toList.map (evalExprPure env))
  | .«case» scruts arms =>
    match scruts[0]? with
    | some scrut =>
      let scrutVal := evalExprPure env scrut
      match scrutVal with
      | .vConstructor _ tag ctorArgs =>
        match arms.toList.find? (fun arm => matchArmTagPure arm tag) with
        | some arm =>
          let env' := ctorArgs.foldl (fun e arg => e.extend "_" arg) env
          evalExprPure env' arm.body
        | none => .vNeutral .type0 (.nVar ⟨"case", ⟨env.size⟩⟩)
      | _ => .vNeutral .type0 (.nVar ⟨"case", ⟨env.size⟩⟩)
    | none => .vNeutral .type0 (.nVar ⟨"case", ⟨env.size⟩⟩)
  | .inject _label _args =>
    .vNeutral .type0 (.nVar ⟨s!"inject:{_label}", ⟨env.size⟩⟩)
  | .dataTy id params => .vDataType id (params.toList.map (evalExprPure env))
  | .eqTy tyLevel ty lhs rhs =>
    .vEq tyLevel (evalExprPure env ty) (evalExprPure env lhs) (evalExprPure env rhs)
  | .refl ty x => .vRefl (evalExprPure env ty) (evalExprPure env x)
  | .transport tyLevel ty motive lhs rhs eq body =>
    let eqVal := evalExprPure env eq
    match eqVal with
    | .vRefl _ _ => evalExprPure env body
    | _ => .vTransport tyLevel (evalExprPure env ty) (evalExprPure env motive)
                       (evalExprPure env lhs) (evalExprPure env rhs)
                       eqVal (evalExprPure env body)
  | .panic msg => .vNeutral .type0 (.nVar ⟨s!"panic: {msg}", ⟨env.size⟩⟩)
  | .closure name _captures =>
    .vNeutral .type0 (.nVar ⟨name.display, ⟨0⟩⟩)
  | .array _elements => .vNeutral .type0 (.nVar ⟨"array", ⟨env.size⟩⟩)
  | .tuple elements =>
    let vals := elements.toList.map (evalExprPure env)
    match vals with
    | [a, b] => .vPair a b
    | _ =>
      let indexed := vals.foldl (fun (acc : List (String × Value)) v =>
        acc ++ [(s!"_{acc.length}", v)]) []
      .vRecordVal indexed
  | .proj _typeName _field _idx =>
    .vNeutral .type0 (.nVar ⟨s!"proj:{_field}", ⟨env.size⟩⟩)
  | .ann expr _ty => evalExprPure env expr

end

mutual

/-- Quote a value to an Expr at a given De Bruijn depth.
    The depth tracks how many binders we've entered during quoting,
    which converts De Bruijn levels to indices. -/
partial def quoteExpr (depth : DeBruijnLvl) (v : Value) : Expr :=
  match v with
  | .vType l => .sort l

  | .vPi qty binder name domain codomain =>
    let domainExpr := quoteExpr depth domain
    let argVal := Value.vNeutral domain (Neutral.nVar ⟨name, depth⟩)
    let codomainVal := applyClosurePure codomain argVal
    let codomainExpr := quoteExpr depth.succ codomainVal
    .pi qty binder name domainExpr codomainExpr

  | .vLam name body =>
    let argVal := Value.vNeutral Value.type0 (Neutral.nVar ⟨name, depth⟩)
    let bodyVal := applyClosurePure body argVal
    let bodyExpr := quoteExpr depth.succ bodyVal
    .lam .explicit name (.sort Level.zero) bodyExpr

  | .vSigma qty name fst snd =>
    let fstExpr := quoteExpr depth fst
    let argVal := Value.vNeutral fst (Neutral.nVar ⟨name, depth⟩)
    let sndVal := applyClosurePure snd argVal
    let sndExpr := quoteExpr depth.succ sndVal
    .sigma qty .explicit name fstExpr sndExpr

  | .vPair fst snd => .pair (quoteExpr depth fst) (quoteExpr depth snd)
  | .vNeutral _ neu => quoteNeutralExpr depth neu
  | .vPrimTy p => .primTy p
  | .vRowSort => .rowSort
  | .vLabelSort => .labelSort
  | .vIntLit n => .lit (.int n)
  | .vStringLit s => .lit (.string s)
  | .vRowEmpty => .rowEmpty
  | .vRowExtend l ft t =>
    .rowExtend (quoteExpr depth l) (quoteExpr depth ft) (quoteExpr depth t)
  | .vRecord row => .recordTy (quoteExpr depth row)
  | .vVariant row => .variantTy (quoteExpr depth row)
  | .vLabelLit name => .labelLit name
  | .vRecordVal fields =>
    .record (fields.map (fun (n, v) => (n, quoteExpr depth v)) |>.toArray)
  | .vDataType id params =>
    .dataTy id (params.map (quoteExpr depth) |>.toArray)
  | .vConstructor name tag args =>
    .construct name tag (args.map (quoteExpr depth) |>.toArray)
  | .vEq lv ty lhs rhs =>
    .eqTy lv (quoteExpr depth ty) (quoteExpr depth lhs) (quoteExpr depth rhs)
  | .vRefl ty x => .refl (quoteExpr depth ty) (quoteExpr depth x)
  | .vTransport lv ty mot lhs rhs eq body =>
    .transport lv (quoteExpr depth ty) (quoteExpr depth mot)
               (quoteExpr depth lhs) (quoteExpr depth rhs)
               (quoteExpr depth eq) (quoteExpr depth body)

/-- Quote a neutral term to an Expr -/
partial def quoteNeutralExpr (depth : DeBruijnLvl) (neu : Neutral) : Expr :=
  match neu with
  | .nVar v => .bvar (depth.lvl - v.level.lvl - 1)
  | .nMeta id => .mvar id
  | .nApp fn arg => .app (quoteNeutralExpr depth fn) (quoteExpr depth arg)
  | .nFst n => .projFst (quoteNeutralExpr depth n)
  | .nSnd n => .projSnd (quoteNeutralExpr depth n)
  | .nFieldAccess n field => .fieldAccess (quoteNeutralExpr depth n) field 0
  | .nCase scrut arms =>
    .«case» #[quoteNeutralExpr depth scrut]
      (arms.map (fun ac =>
        let argVal := Value.vNeutral Value.type0 (Neutral.nVar ⟨ac.pattern, depth⟩)
        let bodyVal := applyClosurePure ac.closure argVal
        Arm.mk #[.wildcard] (quoteExpr depth.succ bodyVal)
      ) |>.toArray)

end

/-- Quote a value to Expr at depth 0 -/
def quoteExpr0 (v : Value) : Expr :=
  quoteExpr ⟨0⟩ v

end Soma.Core
