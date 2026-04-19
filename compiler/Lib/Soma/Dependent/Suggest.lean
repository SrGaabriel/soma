namespace Soma.Dependent.Suggest

/-- Damerau-Levenshtein edit distance -/
def editDistance (a b : String) : Nat := Id.run do
  let as := a.toList.toArray
  let bs := b.toList.toArray
  let m := as.size
  let n := bs.size
  if m == 0 then return n
  if n == 0 then return m

  let mut d : Array Nat := Array.replicate ((m + 1) * (n + 1)) 0
  let idx (i j : Nat) : Nat := i * (n + 1) + j
  for i in [:m+1] do
    d := d.set! (idx i 0) i
  for j in [:n+1] do
    d := d.set! (idx 0 j) j

  for i in [1:m+1] do
    for j in [1:n+1] do
      let ai := as[i - 1]!
      let bj := bs[j - 1]!
      let cost : Nat := if ai == bj then 0 else 1
      let del := d[idx (i-1) j]! + 1
      let ins := d[idx i (j-1)]! + 1
      let sub := d[idx (i-1) (j-1)]! + cost
      d := d.set! (idx i j) (min (min del ins) sub)

  return d[idx m n]!

/-- Case-insensitive variant: lowers both sides first -/
def editDistanceIgnoreCase (a b : String) : Nat :=
  editDistance a.toLower b.toLower

/-- Maximum edit distance we consider a plausible typo -/
def suggestionThreshold (target : String) : Nat :=
  let n := target.length
  if n ≤ 3 then 1
  else if n ≤ 6 then 2
  else 3

/-- Rank candidates by similarity to `target` and return the closest matches -/
def suggestSimilar (target : String) (candidates : Array String) (limit : Nat := 3)
    : Array String := Id.run do
  let threshold := suggestionThreshold target
  let mut scored : Array (Nat × String) := #[]
  for cand in candidates do
    if cand == target then continue
    let d := editDistanceIgnoreCase cand target
    if d ≤ threshold then
      scored := scored.push (d, cand)
  let sorted := scored.qsort fun (d1, c1) (d2, c2) =>
    if d1 != d2 then d1 < d2 else c1 < c2
  let topN := if limit < sorted.size then sorted.extract 0 limit else sorted
  return topN.map (·.2)

/-- Format a suggestion list as an inline help string -/
def formatSuggestions (suggestions : Array String) : Option String :=
  match suggestions.toList with
  | [] => none
  | [s] => some s!"did you mean `{s}`?"
  | ss =>
    let inner := String.intercalate ", " (ss.map fun s => s!"`{s}`")
    some s!"did you mean one of: {inner}?"

end Soma.Dependent.Suggest
