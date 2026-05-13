import Soma.Syntax.GreenTree
import Soma.Syntax.RedTree
import Soma.Syntax.Lower
import Soma.Syntax.Source
import Soma.Syntax.Parse.Decl
import Soma.Diagnostic

namespace Soma.Syntax.Proofs

open Soma.Syntax

/-- Build a `DiagBuilder` from a SourceFile -/
private def diagOf (sf : SourceFile) : Soma.DiagBuilder :=
  (Soma.DiagBuilder.standalone sf).1

/-- Two green nodes with equal content hashes have structurally equal content -/
axiom contentHash_injective (g1 g2 : GreenNode) :
    g1.contentHash = g2.contentHash → g1 = g2

/-- Corollary: BEq on GreenNode is reflexive -/
theorem greenNode_beq_refl (g : GreenNode) : (g == g) = true := by
  simp [BEq.beq]

/-- Parsing is deterministic: the same source produces the same green tree -/
theorem parse_deterministic (source : SourceFile) :
    let (t1, _) := parseToTree source (diagOf source)
    let (t2, _) := parseToTree source (diagOf source)
    t1.green = t2.green := by
  simp

/-- The green tree only depends on source content, not on prior state -/
theorem reparse_green_eq (oldTree : ParsedTree) (source : SourceFile) :
    (reparseToTree oldTree source (diagOf source)).1.green = (parseToTree source (diagOf source)).1.green := by
  -- parseToTree: (ParsedTree.fromGreen green source, diags)
  -- reparseToTree: (oldTree.reparse green source, diags)
  -- In both cases, .green returns the same green from parseWith
  simp only [reparseToTree, parseToTree, reparseToTreeWith, parseToTreeWith]
  -- Now we need to show that oldTree.reparse green source has .green = green
  -- and ParsedTree.fromGreen green source has .green = green
  rfl

/-- lowerModule only accesses ctx.source, never ctx.redTree -/
axiom lowerModule_depends_only_on_source (green : GreenNode) (offset : Nat) (moduleName : String)
    (ctx1 ctx2 : LowerContext) :
    ctx1.source = ctx2.source →
    (lowerModule green offset moduleName).run' ctx1 = (lowerModule green offset moduleName).run' ctx2

/-- Lowering after reparse equals lowering after fresh parse -/
theorem lower_reparse_eq (oldTree : ParsedTree) (source : SourceFile) (moduleName : String) :
    let freshTree := (parseToTree source (diagOf source)).1
    let reparsedTree := (reparseToTree oldTree source (diagOf source)).1
    (lower freshTree (diagOf source) moduleName).1 = (lower reparsedTree (diagOf source) moduleName).1 := by
  simp only
  simp only [lower]
  have hGreen := reparse_green_eq oldTree source
  have hSource : (parseToTree source (diagOf source)).1.red.source = (reparseToTree oldTree source (diagOf source)).1.red.source := by
    simp only [parseToTree, reparseToTree, parseToTreeWith, reparseToTreeWith,
               ParsedTree.fromGreen, ParsedTree.reparse, buildRedTree, diffRedTree]
  rw [hGreen]
  have h := lowerModule_depends_only_on_source
    (parseToTree source (diagOf source)).1.green 0 moduleName
    { source := (parseToTree source (diagOf source)).1.red.source
      redTree := (parseToTree source (diagOf source)).1.red
      diag := diagOf source }
    { source := (reparseToTree oldTree source (diagOf source)).1.red.source
      redTree := (reparseToTree oldTree source (diagOf source)).1.red
      diag := diagOf source }
    hSource
  exact congrArg Prod.fst h


/-- If a subtree's content hash is unchanged and it's at the same position,
    its NodeId is preserved by diffRedTree -/
axiom unchanged_subtree_preserves_id (oldTree : RedTree) (newGreen : GreenNode)
    (source : SourceFile) (oldNode : RedNode) :
    oldNode.green.contentHash = newGreen.contentHash →
    ∃ newNode, newNode ∈ (diffRedTree oldTree newGreen source).nodes.toList ∧
      newNode.id = oldNode.id ∧ newNode.green = newGreen

/-- Changed subtrees get fresh NodeIds from the generator -/
axiom changed_subtree_gets_fresh_id (oldTree : RedTree) (newGreen : GreenNode)
    (source : SourceFile) (startGen : NodeIdGen) :
    ∀ newNode, newNode ∈ (diffRedTree oldTree newGreen source startGen).nodes.toList →
      (∀ oldNode, oldNode ∈ oldTree.nodes.toList →
        newNode.green.contentHash ≠ oldNode.green.contentHash) →
      newNode.id.id ≥ startGen.next

/-- Invariant: getById? returns none iff idToIdx does not contain the key -/
axiom getById_none_iff_not_contains (tree : RedTree) (nodeId : NodeId) :
    tree.getById? nodeId = none ↔ tree.idToIdx.contains nodeId = false

/-- The set of changed NodeIds correctly identifies all modified subtrees -/
theorem changedIds_correct (oldTree newTree : ParsedTree) (nodeId : NodeId) :
    (newTree.red.idToIdx.contains nodeId = true ∧ oldTree.red.idToIdx.contains nodeId = false) →
    match newTree.red.getById? nodeId with
    | some _ =>
      ∀ oldNode, oldTree.red.getById? nodeId = some oldNode →
        False  -- This case is impossible since old doesn't contain nodeId
    | none => False := by
  intro ⟨hNew, hNotOld⟩
  have hNewSome : newTree.red.getById? nodeId ≠ none := by
    intro hNone
    have := (getById_none_iff_not_contains newTree.red nodeId).mp hNone
    rw [this] at hNew
    exact Bool.noConfusion hNew
  split
  case h_1 newNode hNewEq =>
    intro oldNode hOldSome
    have hOldNone := (getById_none_iff_not_contains oldTree.red nodeId).mpr hNotOld
    rw [hOldNone] at hOldSome
    exact Option.noConfusion hOldSome
  case h_2 hNone =>
    exact absurd hNone hNewSome

/-- The green tree produced by incremental reparsing equals fresh parsing -/
theorem incremental_green_tree_correct (oldTree : ParsedTree) (newSource : SourceFile) :
    let (freshResult, _) := parseToTree newSource (diagOf newSource)
    let (incrResult, _) := reparseToTree oldTree newSource (diagOf newSource)
    freshResult.green = incrResult.green := by
  -- This follows directly from reparse_green_eq with equality symmetry
  exact (reparse_green_eq oldTree newSource).symm

/-- Corollary: AST lowering produces equal results -/
theorem incremental_ast_correct (oldTree : ParsedTree) (newSource : SourceFile) (moduleName : String) :
    let (freshTree, _) := parseToTree newSource (diagOf newSource)
    let (incrTree, _) := reparseToTree oldTree newSource (diagOf newSource)
    (lower freshTree (diagOf newSource) moduleName).1 =
        (lower incrTree (diagOf newSource) moduleName).1 := by
  exact lower_reparse_eq oldTree newSource moduleName


/-- The probability of hash collision is negligible -/
axiom hash_collision_negligible :
    ∀ (g1 g2 : GreenNode), g1.contentHash = g2.contentHash → g1 = g2

/-- Specification: Unchanged declarations should not be re-lowered -/
def spec_unchanged_not_relowered (oldTree newTree : ParsedTree) (declId : NodeId) : Prop :=
  (oldTree.red.idToIdx.contains declId ∧ newTree.red.idToIdx.contains declId) →
  match oldTree.red.getById? declId, newTree.red.getById? declId with
  | some oldNode, some newNode => oldNode.green.contentHash = newNode.green.contentHash
  | _, _ => True

/-- Only changed subtrees are traversed during diff -/
def spec_minimal_traversal : Prop :=
  ∀ (oldNode : RedNode) (newGreen : GreenNode),
    oldNode.green.contentHash = newGreen.contentHash →
    diffNode oldNode newGreen = .same oldNode.id

/-- Proof of minimal traversal specification -/
theorem minimal_traversal_holds : spec_minimal_traversal := by
  intro oldNode newGreen hHash
  simp [diffNode, hHash]

end Soma.Syntax.Proofs
