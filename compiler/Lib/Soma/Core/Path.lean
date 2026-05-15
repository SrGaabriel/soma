namespace Soma.Core

inductive PathStep where
  | piDomain
  | piCodomain
  | lamBody
  | dataTypeParam (idx : Nat)
  | constructorArg (idx : Nat)
  | rowLabel
  | rowField
  | rowTail
  | recordRow
  | variantRow
  | spineArg (idx : Nat)
  | spineField (name : String)
  | recordField (name : String)
  deriving Repr, BEq, Hashable, Inhabited

namespace PathStep

def describe : PathStep → String
  | .piDomain => "domain"
  | .piCodomain => "codomain"
  | .lamBody => "body"
  | .dataTypeParam idx => s!"param {idx}"
  | .constructorArg idx => s!"arg {idx}"
  | .rowLabel => "row label"
  | .rowField => "row field"
  | .rowTail => "row tail"
  | .recordRow => "record row"
  | .variantRow => "variant row"
  | .spineArg idx => s!"applied arg {idx}"
  | .spineField name => s!"field .{name}"
  | .recordField name => s!"field `{name}`"

end PathStep

abbrev Path := Array PathStep

namespace Path

def empty : Path := #[]

def push (p : Path) (s : PathStep) : Path := Array.push p s

def describe (p : Path) : String :=
  if p.isEmpty then "root"
  else
    let parts : List String := p.toList.map fun s => PathStep.describe s
    String.intercalate " → " parts

end Path

end Soma.Core
