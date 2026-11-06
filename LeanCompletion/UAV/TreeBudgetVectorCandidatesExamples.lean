import LeanCompletion.UAV.TreeBudgetVectorCandidates
import LeanCompletion.UAV.TreeFlowExamples

/-! Kernel-checked ordered-list regressions for the materialized candidate
generator. These check complete lists, including order and multiplicity, and
do not assert search/cache simulation or runtime bounds. -/
namespace UAVProof.TreeBudgetVectorCandidatesExamples

open TreeFlowExistence TreeBudgetVector TreeBudgetVectorChecker TreeBudgetVectorCandidates

/-- Pure zero-dimensional enumeration has one empty assignment. No rooted tree
on the empty vertex type is required. -/
theorem zero_dimension_singleton :
    boundedVectorsV 0 (encode Fin.elim0) = [encode Fin.elim0] := by
  decide +kernel

/-- Head-coordinate range is outermost; the tail varies first. -/
theorem two_coordinate_order :
    boundedVectorsV 2 (encode ![1, 2]) =
      [encode ![0, 0], encode ![0, 1], encode ![0, 2],
       encode ![1, 0], encode ![1, 1], encode ![1, 2]] := by
  decide +kernel

/-- A zero bound fixes that coordinate; it does not remove the coordinate. -/
theorem zero_coordinate_bound :
    boundedVectorsV 3 (encode ![1, 0, 1]) =
      [encode ![0, 0, 0], encode ![0, 0, 1],
       encode ![1, 0, 0], encode ![1, 0, 1]] := by
  decide +kernel

/-- The three-vertex path viewed as a star whose depot is the middle index. -/
def middleRootStar : RootedTree (Fin 3) where
  graph := SimpleGraph.pathGraph 3
  isTree := by
    classical
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨SimpleGraph.pathGraph_connected 2, ?_⟩
    simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    have he : (SimpleGraph.pathGraph 3).edgeFinset =
        {s((0 : Fin 3), 1), s((1 : Fin 3), 2)} := by
      ext e
      induction e using Sym2.inductionOn with
      | hf u v =>
        fin_cases u <;> fin_cases v <;>
          simp [SimpleGraph.mem_edgeFinset, SimpleGraph.pathGraph_adj, Sym2.eq]
    rw [he]
    decide +kernel
  root := 1
  parent := ![1, 1, 1]
  parent_root := rfl
  rank := ![0, 1, 0]
  parent_rank := by decide +kernel
  adj_iff := by
    intro u v
    rw [SimpleGraph.pathGraph_adj]
    fin_cases u <;> fin_cases v <;> decide +kernel

def starBound : Vector ℕ 3 := encode ![1, 7, 1]

/-- The original root bound is nonzero and the root is not the first index. -/
theorem middle_root_normalized_bound :
    TreeBudgetVector.normalize middleRootStar starBound = encode ![1, 0, 1] := by
  decide +kernel

/-- Normalizing before enumeration avoids eight duplicate copies of each row.
The root-count check removes both the zero row and the two-departure row. -/
theorem middle_root_candidates_order :
    candidatesV middleRootStar starBound (Vector.ofFn ![0, 0, 0]) 0 =
      [encode ![0, 0, 1], encode ![1, 0, 0]] := by
  decide +kernel

/-- Negative budget is meaningful with signed fees; filtering retains the
qualifying row even though it appears after a rejected candidate. -/
theorem signed_integer_candidates :
    candidatesV middleRootStar starBound (Vector.ofFn ![-2, 999, 1]) (-2) =
      [encode ![1, 0, 0]] ∧
    candidatesV middleRootStar starBound (Vector.ofFn ![-2, 999, 1]) (-3) = [] := by
  decide +kernel

/-- All nonroot fractions and both budgets are deliberately unreduced.
Costs are -1/2 and -3/4: equality is accepted, and order survives filtering. -/
theorem unreduced_signed_candidates :
    candidatesVScaled middleRootStar starBound
      (Vector.ofFn ![-2, 999, -6]) (encode ![4, 2, 8]) (-6) 8 =
        [encode ![0, 0, 1]] ∧
    candidatesVScaled middleRootStar starBound
      (Vector.ofFn ![-2, 999, -6]) (encode ![4, 2, 8]) (-4) 8 =
        [encode ![0, 0, 1], encode ![1, 0, 0]] ∧
    candidatesVScaled middleRootStar starBound
      (Vector.ofFn ![-2, 999, -6]) (encode ![4, 2, 8]) (-7) 8 = [] := by
  decide +kernel

/-- Stable filtering never deduplicates repeated accepted elements. -/
theorem filter_preserves_duplicates {α : Type*} [DecidableEq α]
    (a b : α) (hab : a ≠ b) :
    [a, b, a].filter (fun x => decide (x = a)) = [a, a] := by
  simp [Ne.symm hab]

end UAVProof.TreeBudgetVectorCandidatesExamples

#print axioms UAVProof.TreeBudgetVectorCandidatesExamples.zero_dimension_singleton
#print axioms UAVProof.TreeBudgetVectorCandidatesExamples.two_coordinate_order
#print axioms UAVProof.TreeBudgetVectorCandidatesExamples.zero_coordinate_bound
#print axioms UAVProof.TreeBudgetVectorCandidatesExamples.middle_root_normalized_bound
#print axioms UAVProof.TreeBudgetVectorCandidatesExamples.middle_root_candidates_order
#print axioms UAVProof.TreeBudgetVectorCandidatesExamples.signed_integer_candidates
#print axioms UAVProof.TreeBudgetVectorCandidatesExamples.unreduced_signed_candidates
#print axioms UAVProof.TreeBudgetVectorCandidatesExamples.filter_preserves_duplicates
