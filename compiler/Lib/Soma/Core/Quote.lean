import Soma.Core.Value
import Soma.Core.Expr
import Soma.Core.Quantity
import Soma.Core.Level

namespace Soma.Core


mutual

/-- Convert neutral to string -/
partial def neutralToString (neu : Neutral) : String :=
  match neu with
  | .nVar v => v.name
  | .nMeta id => s!"?{id.id}"
  | .nApp fn arg => s!"{neutralToString fn} {valueToString arg}"
  | .nFst pair => s!"{neutralToString pair}.1"
  | .nSnd pair => s!"{neutralToString pair}.2"
  | .nFieldAccess record field => s!"{neutralToString record}.{field}"
  | .nCase scrutinee _ _ => s!"case {neutralToString scrutinee} of ..."
  | .nConst name _ => name.display

/-- Quote a value to a string (for error messages) -/
partial def valueToString (v : Value) : String :=
  match v with
  | .vType level =>
    match level with
    | .lit 0 => "Type"
    | .lit _ => s!"Type{Level.toSubscript level}"
    | _ => s!"Type{level}"

  | .vPi _qty binder name domain _codomain =>
    let binderStr := match binder with
      | .explicit => ""
      | .implicit => "implicit "
      | .instance_ => "instance "
      | .strictImplicit => "strict "
    let domStr := valueToString domain
    s!"({binderStr}{name} : {domStr}) -> ..."

  | .vLam name _body =>
    s!"fun({name}). ..."

  | .vSigma _qty name fst _snd =>
    let fstStr := valueToString fst
    s!"({name} : {fstStr}) × ..."

  | .vPair fst snd =>
    s!"({valueToString fst}, {valueToString snd})"

  | .vNeutral _ neu =>
    neutralToString neu

  | .vPrimTy p => p.name

  | .vRowSort => "Row"
  | .vLabelSort => "Label"

  | .vIntLit n => toString n

  | .vStringLit s => s!"\"{s}\""

  | .vRowEmpty => "{}"

  | .vRowExtend label fieldTy tail =>
    let labelStr := valueToString label
    let tyStr := valueToString fieldTy
    let tailStr := valueToString tail
    "{ " ++ labelStr ++ " : " ++ tyStr ++ " | " ++ tailStr ++ " }"

  | .vRecord row =>
    "{ " ++ valueToString row ++ " }"

  | .vVariant row =>
    "< " ++ valueToString row ++ " >"

  | .vLabelLit name => s!"'{name}"

  | .vRecordVal fields =>
    let fieldsStr := fields.map (fun (n, v) => n ++ " = " ++ valueToString v)
    "{ " ++ ", ".intercalate fieldsStr ++ " }"

  | .vDataType id params =>
    if params.isEmpty then id.original
    else
      let paramsStr := params.map valueToString
      s!"{id.original} {" ".intercalate paramsStr}"

  | .vConstructor name _ args _ =>
    if args.isEmpty then name.display
    else
      let argsStr := args.map valueToString
      s!"{name.display} {" ".intercalate argsStr}"

  | .vEq _ _ty lhs rhs =>
    s!"{valueToString lhs} = {valueToString rhs}"

  | .vRefl _ _ => "refl"

  | .vTransport _ _ motive _ _ eq body =>
    s!"transport {valueToString motive} {valueToString eq} {valueToString body}"

end

instance : ToString Value := ⟨valueToString⟩
instance : ToString Neutral := ⟨neutralToString⟩

mutual

/-- Check if two values are definitionally equal -/
partial def valueEq (v1 v2 : Value) : Bool :=
  match v1, v2 with
  | .vType l1, .vType l2 => l1 == l2
  | .vPrimTy p1, .vPrimTy p2 => p1 == p2
  | .vRowSort, .vRowSort => true
  | .vLabelSort, .vLabelSort => true
  | .vIntLit n1, .vIntLit n2 => n1 == n2
  | .vStringLit s1, .vStringLit s2 => s1 == s2
  | .vLabelLit n1, .vLabelLit n2 => n1 == n2
  | .vRowEmpty, .vRowEmpty => true
  | .vRowExtend l1 t1 r1, .vRowExtend l2 t2 r2 =>
    valueEq l1 l2 && valueEq t1 t2 && valueEq r1 r2
  | .vRecord r1, .vRecord r2 => valueEq r1 r2
  | .vVariant r1, .vVariant r2 => valueEq r1 r2
  | .vPair a1 b1, .vPair a2 b2 =>
    valueEq a1 a2 && valueEq b1 b2
  | .vNeutral _ n1, .vNeutral _ n2 => neutralEq n1 n2
  | .vDataType id1 ps1, .vDataType id2 ps2 =>
    id1 == id2 && ps1.length == ps2.length &&
    (ps1.zip ps2).all (fun (a, b) => valueEq a b)
  | .vConstructor n1 t1 as1 _, .vConstructor n2 t2 as2 _ =>
    n1 == n2 && t1 == t2 && as1.length == as2.length &&
    (as1.zip as2).all (fun (a, b) => valueEq a b)
  | .vEq l1 t1 a1 b1, .vEq l2 t2 a2 b2 =>
    l1 == l2 && valueEq t1 t2 && valueEq a1 a2 && valueEq b1 b2
  | .vRefl t1 x1, .vRefl t2 x2 =>
    valueEq t1 t2 && valueEq x1 x2
  | .vTransport l1 t1 m1 lhs1 rhs1 eq1 b1, .vTransport l2 t2 m2 lhs2 rhs2 eq2 b2 =>
    l1 == l2 && valueEq t1 t2 && valueEq m1 m2 && valueEq lhs1 lhs2 &&
    valueEq rhs1 rhs2 && valueEq eq1 eq2 && valueEq b1 b2
  | _, _ => false

/-- Check if two neutral terms are equal -/
partial def neutralEq (n1 n2 : Neutral) : Bool :=
  match n1, n2 with
  | .nVar v1, .nVar v2 => v1.level == v2.level
  | .nMeta m1, .nMeta m2 => m1 == m2
  | .nApp f1 a1, .nApp f2 a2 => neutralEq f1 f2 && valueEq a1 a2
  | .nFst p1, .nFst p2 => neutralEq p1 p2
  | .nSnd p1, .nSnd p2 => neutralEq p1 p2
  | .nFieldAccess r1 f1, .nFieldAccess r2 f2 => neutralEq r1 r2 && f1 == f2
  | .nConst n1 _, .nConst n2 _ => n1 == n2
  | _, _ => false

end

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
  | .fvar id _ =>
    match env.lookupByName id.original with
    | some v => v
    | none => .vNeutral .type0 (.nVar ⟨id.original, ⟨env.size⟩⟩)
  | .mvar id => .vNeutral .type0 (.nMeta id)
  | .const name tyExpr =>
    let tyVal := evalExprPure env tyExpr
    .vNeutral tyVal (.nConst name tyVal)
  | .lit l =>
    match l with
    | .int n => .vIntLit n
    | .string s => .vStringLit s
    | .bool true => .vConstructor ⟨⟨0, "", "True"⟩⟩ 0 [] (.vPrimTy .bool)
    | .bool false => .vConstructor ⟨⟨0, "", "False"⟩⟩ 1 [] (.vPrimTy .bool)
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
    | .vConstructor _ 0 _ _ => evalExprPure env then_
    | .vConstructor _ 1 _ _ => evalExprPure env else_
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
  | .construct name tag args rty =>
    .vConstructor name tag (args.toList.map (evalExprPure env)) (evalExprPure env rty)
  | .«case» scruts arms resultTyExpr =>
    match scruts[0]? with
    | some scrut =>
      let scrutVal := evalExprPure env scrut
      match scrutVal with
      | .vConstructor _ tag ctorArgs _ =>
        match arms.toList.find? (fun arm => matchArmTagPure arm tag) with
        | some arm =>
          let env' := ctorArgs.foldl (fun e arg => e.extend "_" arg) env
          evalExprPure env' arm.body
        | none => .vNeutral .type0 (.nVar ⟨"case-no-arm", ⟨env.size⟩⟩)
      | .vNeutral ty neu =>
        let resultTy := evalExprPure env resultTyExpr
        let armClosures := arms.toList.map fun arm =>
          let binds := arm.patterns.foldl (fun acc p => acc + p.bindingCount) 0
          let patName := match arm.patterns[0]? with
            | some (Pattern.ctor qn _ _) => qn.id.original
            | some (Pattern.var (some uid)) => uid.original
            | _ => s!"pat{binds}"
          if binds == 0 then
            ArmClosure.mk patName (.const patName (evalExprPure env arm.body)) arm.patterns
          else
            ArmClosure.mk patName (Closure.mkWithBody patName env arm.body) arm.patterns
        .vNeutral ty (.nCase neu armClosures resultTy)
      | _ => .vNeutral .type0 (.nVar ⟨"case-stuck", ⟨env.size⟩⟩)
    | none => .vNeutral .type0 (.nVar ⟨"case-empty", ⟨env.size⟩⟩)
  | .inject _label _args _ =>
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
    .vNeutral .type0 (.nConst name .type0)
  | .array _elements _ => .vNeutral .type0 (.nVar ⟨"array", ⟨env.size⟩⟩)
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
  | .vConstructor name tag args resultTy =>
    .construct name tag (args.map (quoteExpr depth) |>.toArray) (quoteExpr depth resultTy)
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
  | .nCase scrut arms resultTy =>
    .«case» #[quoteNeutralExpr depth scrut]
      (arms.map (fun ac =>
        let binds := ac.patterns.foldl (fun a p => a + p.bindingCount) 0
        let bodyDepth : DeBruijnLvl := ⟨depth.lvl + binds⟩
        if binds == 0 then
          let bodyVal := applyClosurePure ac.closure
            (Value.vNeutral Value.type0 (Neutral.nVar ⟨ac.pattern, depth⟩))
          Arm.mk ac.patterns (quoteExpr depth bodyVal)
        else
          let bodyVal := match ac.closure with
            | .const _ v => v
            | .term _ env body =>
              let env' := (List.range binds).foldl (fun e i =>
                let lvl : DeBruijnLvl := ⟨depth.lvl + i⟩
                e.extend s!"pat_{i}" (Value.vNeutral Value.type0
                  (Neutral.nVar ⟨s!"pat_{i}", lvl⟩))
              ) env
              evalExprPure env' body
          Arm.mk ac.patterns (quoteExpr bodyDepth bodyVal)
      ) |>.toArray)
      (quoteExpr depth resultTy)
  | .nConst name constTy => .const name (quoteExpr depth constTy)

end

/-- Quote a value to Expr at depth 0 -/
def quoteExpr0 (v : Value) : Expr :=
  quoteExpr ⟨0⟩ v

end Soma.Core
