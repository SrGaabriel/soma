import Soma.Core.Value
import Soma.Core.Expr
import Soma.Core.Quantity
import Soma.Core.Level

namespace Soma.Core


mutual

/-- Format a neutral head -/
partial def headToString : Head → String
  | .hVar v => v.name
  | .hMeta _ => "{unknown}"
  | .hConst name _ => name.display
  | .hCase scrutinees _ _ =>
    let scrutsStr := scrutinees.toList.map valueToString |> String.intercalate ", "
    s!"case {scrutsStr} of ..."

/-- Format an eliminator applied on top of an already-rendered prefix -/
partial def elimToString (acc : String) : Elim → String
  | .eApp arg => s!"{acc} {valueToString arg}"
  | .eFst => s!"{acc}.1"
  | .eSnd => s!"{acc}.2"
  | .eField name => s!"{acc}.{name}"

/-- Convert a neutral to a string by folding its spine over its head -/
partial def neutralToString (neu : Neutral) : String :=
  neu.spine.foldl elimToString (headToString neu.head)

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
  | .vFloatLit f => toString f

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
  | .vFloatLit f1, .vFloatLit f2 => f1 == f2
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

/-- Check if two heads are equal -/
partial def headEq (h1 h2 : Head) : Bool :=
  match h1, h2 with
  | .hVar v1, .hVar v2 => v1.level == v2.level
  | .hMeta m1, .hMeta m2 => m1 == m2
  | .hConst n1 _, .hConst n2 _ => n1 == n2
  | .hCase _ _ _, .hCase _ _ _ => false
  | _, _ => false

/-- Check if two eliminators are equal -/
partial def elimEq (e1 e2 : Elim) : Bool :=
  match e1, e2 with
  | .eApp a1, .eApp a2 => valueEq a1 a2
  | .eFst, .eFst => true
  | .eSnd, .eSnd => true
  | .eField f1, .eField f2 => f1 == f2
  | _, _ => false

/-- Check if two neutral terms are equal: same head, same spine -/
partial def neutralEq (n1 n2 : Neutral) : Bool :=
  headEq n1.head n2.head &&
    n1.spine.size == n2.spine.size &&
    (n1.spine.zip n2.spine).all (fun (e1, e2) => elimEq e1 e2)

end

mutual

/-- Pure counterpart of `Eval.matchPattern` -/
partial def matchPatternPure (pat : Pattern) (val : Value) : PatMatchResult :=
  match pat with
  | .wildcard => .matched #[]
  | .var none => .matched #[]
  | .var (some _) => .matched #[val]
  | .ctor _ tag fields =>
    match val with
    | .vConstructor _ vTag vArgs _ =>
      if tag != vTag then .mismatch
      else
        let vArgsArr := vArgs.toArray
        if fields.size != vArgsArr.size then .mismatch
        else matchPatternArraysPure fields vArgsArr
    | .vNeutral _ _ => .stuck
    | _ => .mismatch
  | .lit l =>
    match val with
    | .vIntLit n =>
      match l with
      | .int m => if n == m then .matched #[] else .mismatch
      | _ => .mismatch
    | .vStringLit s =>
      match l with
      | .string t => if s == t then .matched #[] else .mismatch
      | _ => .mismatch
    | .vFloatLit f =>
      match l with
      | .float g => if f == g then .matched #[] else .mismatch
      | _ => .mismatch
    | .vConstructor _ tag _ _ =>
      match l with
      | .bool true => if tag == 0 then .matched #[] else .mismatch
      | .bool false => if tag == 1 then .matched #[] else .mismatch
      | _ => .mismatch
    | .vNeutral _ _ => .stuck
    | _ => .mismatch
  | .inject label argPat =>
    match val with
    | .vConstructor name _ vArgs _ =>
      if name.display != label then .mismatch
      else match argPat with
        | none => if vArgs.isEmpty then .matched #[] else .mismatch
        | some inner =>
          match vArgs with
          | arg :: _ => matchPatternPure inner arg
          | [] => .mismatch
    | .vNeutral _ _ => .stuck
    | _ => .mismatch

partial def matchPatternArraysPure (pats : Array Pattern) (vals : Array Value)
    : PatMatchResult :=
  if pats.size != vals.size then .mismatch
  else matchPatternArraysPureGo pats vals 0 #[] false

partial def matchPatternArraysPureGo
    (pats : Array Pattern) (vals : Array Value)
    (i : Nat) (acc : Array Value) (stuck : Bool) : PatMatchResult :=
  if i >= pats.size then
    if stuck then .stuck else .matched acc
  else
    let pat := pats[i]!
    let val := vals[i]!
    match matchPatternPure pat val with
    | .matched bs => matchPatternArraysPureGo pats vals (i + 1) (acc ++ bs) stuck
    | .mismatch => .mismatch
    | .stuck => matchPatternArraysPureGo pats vals (i + 1) acc true

end

partial def selectArmPure (scrutVals : Array Value) (arms : Array Arm)
    : Option (Array Value × Expr) :=
  let rec go (i : Nat) : Option (Array Value × Expr) :=
    if i >= arms.size then none
    else
      let arm := arms[i]!
      match matchPatternArraysPure arm.patterns scrutVals with
      | .matched bs => some (bs, arm.body)
      | .mismatch => go (i + 1)
      | .stuck => none
  go 0

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
    | .float f => .vFloatLit f
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
    let scrutVals := scruts.map (evalExprPure env)
    match selectArmPure scrutVals arms with
    | some (bindings, body) =>
      let env' := bindings.foldl (fun e v => e.extend "_" v) env
      evalExprPure env' body
    | none =>
      let resultTy := evalExprPure env resultTyExpr
      let hasNeutral := scrutVals.any fun
        | .vNeutral _ _ => true
        | _ => false
      if !hasNeutral then
        .vNeutral .type0 (.nVar ⟨"case-no-arm", ⟨env.size⟩⟩)
      else
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
        .vNeutral resultTy (.nCase scrutVals armClosures resultTy)
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
  | .vFloatLit f => .lit (.float f)
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

/-- Quote a neutral head to an Expr at a given depth -/
partial def quoteHeadExpr (depth : DeBruijnLvl) : Head → Expr
  | .hVar v =>
    if v.level.lvl < depth.lvl then
      .bvar (depth.lvl - v.level.lvl - 1)
    else
      .fvar ⟨v.level.lvl, "__tyvar", v.name⟩ (.sort .zero)
  | .hMeta id => .mvar id
  | .hConst name constTy => .const name (quoteExpr depth constTy)
  | .hCase scrutinees arms resultTy =>
    .«case» (scrutinees.map (quoteExpr depth))
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

/-- Apply an eliminator on top of an already-quoted expression -/
partial def quoteElimExpr (depth : DeBruijnLvl) (acc : Expr) : Elim → Expr
  | .eApp arg => .app acc (quoteExpr depth arg)
  | .eFst => .projFst acc
  | .eSnd => .projSnd acc
  | .eField name => .fieldAccess acc name 0

/-- Quote a neutral term to an Expr by folding the spine over the head -/
partial def quoteNeutralExpr (depth : DeBruijnLvl) (neu : Neutral) : Expr :=
  neu.spine.foldl (quoteElimExpr depth) (quoteHeadExpr depth neu.head)

end

/-- Quote a value to Expr at depth 0 -/
def quoteExpr0 (v : Value) : Expr :=
  quoteExpr ⟨0⟩ v

end Soma.Core
