import Soma.Metal.Expr
import Soma.Typing.Ty

namespace Soma.Infer.Resolve

open Soma.Metal
open Soma.Typing

/-- Compute field index from a record's row type -/
def fieldIndexInRow (fieldName : String) (row : RowTy) : Option Nat :=
  go row 0
where
  go : RowTy → Nat → Option Nat
    | .rowEmpty, _ => none
    | .rowExtend label _ tail, idx =>
      match label.labelName? with
      | some name =>
        if name == fieldName then some idx
        else go tail (idx + 1)
      | none => none -- Label variable (shouldn't happen post-mono)
    | .var _, _ => none -- Row variable (shouldn't happen post-mono)
    | _, _ => none -- Other cases (shouldn't happen for RowTy)

/-- Get the row type from a MonoTy, handling both structural records and nominal types -/
def getExprRowType (ty : MonoTy) (lookupNominalRow : TypeId → Option RowTy) : Option RowTy :=
  match ty with
  | .record row => some row
  | .userCon _ typeId => lookupNominalRow typeId
  | _ => none

/-- Resolve field indices in a typed expression -/
partial def resolveFieldIndices {scope : Scope}
    (lookupNominalRow : TypeId → Option RowTy)
    (expr : TypedExpr scope) : TypedExpr scope :=
  match expr with
  | .fieldAccess e fieldName _oldIdx ty span =>
    let e' := resolveFieldIndices lookupNominalRow e
    let idx := match e'.getInfo with
      | some exprTy =>
        match getExprRowType exprTy lookupNominalRow with
        | some row => fieldIndexInRow fieldName row |>.getD 0
        | none => 0
      | none => 0
    .fieldAccess e' fieldName idx ty span

  | .var v info span => .var v info span
  | .lit lit span => .lit lit span

  | .call fn args info span =>
    .call (resolveFieldIndices lookupNominalRow fn) (resolveExprList lookupNominalRow args) info span

  | .lam params body info span =>
    .lam params (resolveFieldIndices lookupNominalRow body) info span

  | .let_ binder orig val body info span =>
    .let_ binder orig (resolveFieldIndices lookupNominalRow val) (resolveFieldIndices lookupNominalRow body) info span

  | .case scrutinees arms info span =>
    .case (resolveExprList lookupNominalRow scrutinees) (resolveArms lookupNominalRow arms) info span

  | .if_ cond then_ else_ info span =>
    .if_ (resolveFieldIndices lookupNominalRow cond)
         (resolveFieldIndices lookupNominalRow then_)
         (resolveFieldIndices lookupNominalRow else_) info span

  | .tuple elems info span =>
    .tuple (resolveExprList lookupNominalRow elems) info span

  | .record fields info span =>
    .record (resolveRecordFields lookupNominalRow fields) info span

  | .recordUpdate base updates info span =>
    .recordUpdate (resolveFieldIndices lookupNominalRow base) (resolveRecordFields lookupNominalRow updates) info span

  | .array elems info span =>
    .array (resolveExprList lookupNominalRow elems) info span

  | .construct name tag args info span =>
    .construct name tag (resolveExprList lookupNominalRow args) info span

  | .closure liftedName captures info span =>
    .closure liftedName (resolveCaptures lookupNominalRow captures) info span

  | .global name info span => .global name info span

  | .panic msg info span => .panic msg info span

  | .proj typeName fieldName fieldIndex info span =>
    .proj typeName fieldName fieldIndex info span

  | .typeApp arg info span =>
    .typeApp arg info span

where
  resolveExprList {scope : Scope} (lookupNominalRow : TypeId → Option RowTy)
      (exprs : ExprList MonoTy scope) : ExprList MonoTy scope :=
    match exprs with
    | .nil => .nil
    | .cons e es => .cons (resolveFieldIndices lookupNominalRow e) (resolveExprList lookupNominalRow es)

  resolveArms {scope : Scope} (lookupNominalRow : TypeId → Option RowTy)
      (arms : ArmList MonoTy scope) : ArmList MonoTy scope :=
    match arms with
    | .nil => .nil
    | .cons arm rest =>
      let arm' := match arm with
        | .mk patterns body span =>
          .mk patterns (resolveFieldIndices lookupNominalRow body) span
      .cons arm' (resolveArms lookupNominalRow rest)

  resolveCaptures {scope : Scope} (_lookupNominalRow : TypeId → Option RowTy)
      (captures : CaptureList MonoTy scope) : CaptureList MonoTy scope :=
    -- CaptureList just stores variable references and their types, no expressions to resolve
    captures

  resolveRecordFields {scope : Scope} (lookupNominalRow : TypeId → Option RowTy)
      (fields : RecordFieldList MonoTy scope) : RecordFieldList MonoTy scope :=
    match fields with
    | .nil => .nil
    | .cons name expr rest =>
      .cons name (resolveFieldIndices lookupNominalRow expr) (resolveRecordFields lookupNominalRow rest)

end Soma.Infer.Resolve
