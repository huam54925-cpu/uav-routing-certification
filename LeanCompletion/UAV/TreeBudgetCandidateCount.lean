import LeanCompletion.UAV.TreeBudgetMemoBounds

/-! Length bounds for the executable candidate list. The enumeration proof
counts list positions directly and does not assume duplicate-free candidates.
These are combinatorial counts, not bounds on candidate-generation time. -/
namespace UAVProof.TreeBudgetCandidateCount
open TreeFlowExistence TreeBudgetPatterns TreeBudgetFiniteSearch TreeBudgetMemoBounds

/-- Enumerating each coordinate independently gives this exact list length. -/
theorem boundedVectors_length (n : ℕ) (b : Fin n → ℕ) :
    (boundedVectors n b).length = ∏ i : Fin n, (b i + 1) := by
  induction n with
  | zero => simp [boundedVectors]
  | succ n ih =>
    simp [boundedVectors, List.length_flatMap, ih, Fin.prod_univ_succ]

variable {n : ℕ}

/-- The normalized root coordinate contributes exactly one enumerated value. -/
theorem boundedVectors_bound_length (R : RootedTree (Fin n)) (H : Fin n → ℕ) :
    (boundedVectors n (bound R H)).length = stateBound R H := by
  rw [boundedVectors_length]
  simp only [stateBound, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro v _
  by_cases hv : v = R.root <;> simp [bound, hv]

/-- Filtering for legal rows cannot increase the number of candidate positions. -/
theorem candidates_length_le_stateBound (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (candidates R H s T).length ≤ stateBound R H := by
  rw [← boundedVectors_bound_length R H]
  exact List.length_filter_le _ _

end UAVProof.TreeBudgetCandidateCount

#print axioms UAVProof.TreeBudgetCandidateCount.boundedVectors_length
#print axioms UAVProof.TreeBudgetCandidateCount.boundedVectors_bound_length
#print axioms UAVProof.TreeBudgetCandidateCount.candidates_length_le_stateBound
