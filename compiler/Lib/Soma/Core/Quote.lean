import Soma.Core.Value
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
  | .nCase scrutinee _ => s!"case {neutralToString scrutinee} of ..."

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
    if params.isEmpty then id.name
    else
      let paramsStr := params.map valueToString
      s!"{id.name} {" ".intercalate paramsStr}"

  | .vConstructor name _ args =>
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
  | .vConstructor n1 t1 as1, .vConstructor n2 t2 as2 =>
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
  | _, _ => false

end

end Soma.Core
