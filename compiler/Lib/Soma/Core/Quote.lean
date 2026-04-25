import Soma.Core.Value
import Soma.Core.Expr
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Eval

namespace Soma.Core


mutual

/-- Format a neutral head -/
partial def headToString : Head → String
  | .hVar v => v.name
  | .hMeta _ => "{unknown}"
  | .hConst name _ => name.display
  | .hCase scrutinees _ _ =>
    let scrutsStr := scrutinees.toList.map valueToString |> String.intercalate ", "
    s!"case {scrutsStr} of …"
  | .hErrored => "{errored}"

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
  | .vLam _ b1, .vLam _ b2 => closureEq b1 b2
  | _, _ => false

/-- Check if two heads are equal -/
partial def headEq (h1 h2 : Head) : Bool :=
  match h1, h2 with
  | .hVar v1, .hVar v2 => v1.level == v2.level
  | .hMeta m1, .hMeta m2 => m1 == m2
  | .hConst n1 _, .hConst n2 _ => n1 == n2
  | .hCase ss1 m1 as1, .hCase ss2 m2 as2 =>
    -- Two stuck cases are equal when their scrutinees, motive and arm closures all match structurally
    ss1.size == ss2.size &&
    (ss1.zip ss2).all (fun (s1, s2) => valueEq s1 s2) &&
    valueEq m1 m2 &&
    armsEq as1 as2
  | .hErrored, .hErrored => true
  | _, _ => false

/-- Check if two lists of arm closures are structurally equal -/
partial def armsEq (as1 as2 : List ArmClosure) : Bool :=
  as1.length == as2.length &&
  (as1.zip as2 |>.all (fun (a1, a2) =>
    a1.patterns.size == a2.patterns.size &&
    (a1.patterns.zip a2.patterns).all (fun (p1, p2) => p1 == p2) &&
    closureEq a1.closure a2.closure))

/-- Structural equality for closures -/
partial def closureEq (c1 c2 : Closure) : Bool :=
  match c1, c2 with
  | .const _ v1, .const _ v2 => valueEq v1 v2
  | .term _ env1 body1, .term _ env2 body2 =>
    body1 == body2 && envEq env1 env2
  | _, _ => false

/-- Pointwise value equality on captured environments -/
partial def envEq (e1 e2 : Env) : Bool :=
  e1.size == e2.size &&
  e1.values.length == e2.values.length &&
  (e1.values.zip e2.values |>.all (fun ((_, v1), (_, v2)) => valueEq v1 v2))

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

/-- Quote a value to an Expr at a given De Bruijn depth.
    The depth tracks how many binders we've entered during quoting,
    which converts De Bruijn levels to indices. -/
partial def quoteExpr (depth : DeBruijnLvl) (v : Value) : Expr :=
  match v with
  | .vType l => .sort l

  | .vPi qty binder name domain codomain =>
    let domainExpr := quoteExpr depth domain
    let argVal := Value.vNeutral domain (Neutral.nVar ⟨name, depth⟩)
    let codomainVal := codomain.applyPure argVal
    let codomainExpr := quoteExpr depth.succ codomainVal
    .pi qty binder name domainExpr codomainExpr

  | .vLam name body =>
    let argVal := Value.vNeutral Value.type0 (Neutral.nVar ⟨name, depth⟩)
    let bodyVal := body.applyPure argVal
    let bodyExpr := quoteExpr depth.succ bodyVal
    .lam .explicit name (.sort Level.zero) bodyExpr

  | .vSigma qty name fst snd =>
    let fstExpr := quoteExpr depth fst
    let argVal := Value.vNeutral fst (Neutral.nVar ⟨name, depth⟩)
    let sndVal := snd.applyPure argVal
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
      .tyvar v.level v.name
  | .hMeta id => .mvar id
  | .hConst name constTy => .const name (quoteExpr depth constTy)
  | .hCase scrutinees motive arms =>
    .«case» (scrutinees.map (quoteExpr depth))
      (quoteExpr depth motive)
      (arms.map (fun ac =>
        let binds := ac.patterns.foldl (fun a p => a + p.bindingCount) 0
        let bodyDepth : DeBruijnLvl := ⟨depth.lvl + binds⟩
        if binds == 0 then
          let bodyVal := ac.closure.applyPure
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
  | .hErrored => .panic "{errored}"

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
