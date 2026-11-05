import LeanCompletion.UAV.TreeBudgetSearchCostBounds
import LeanCompletion.UAV.TreeBudgetStateParameters

/-! Parameterized logical operation bounds at the formal cold-cache entry.
This module closes the numerical consequences of the existing counts. It does
not assert a bit-operation or elapsed-time bound for the executable. -/
namespace UAVProof.TreeBudgetParameterizedBounds
open TreeFlowExistence TreeBudgetPatterns TreeBudgetMemoState TreeBudgetMemoSearch
open TreeBudgetSearchStats TreeBudgetMemoBounds TreeBudgetSearchStatsBounds
open TreeBudgetSearchCostBounds TreeBudgetCandidateCount TreeBudgetStateParameters
variable {n : ℕ}

/-- Root children form a subset of the nonroot coordinates. -/
theorem rootCount_le_totalMultiplicity (R : RootedTree (Fin n)) (H : Fin n → ℕ) :
    rootCount R H ≤ totalMultiplicity R H := by
  apply Finset.sum_le_sum_of_subset
  intro v hv
  simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  simp [nonrootVertices, hv.1]

theorem totalMultiplicity_eq_sum_positiveCoordinates
    (R : RootedTree (Fin n)) (H : Fin n → ℕ) :
    totalMultiplicity R H = ∑ v ∈ positiveCoordinates R H, H v := by
  change (∑ v ∈ nonrootVertices R, H v) =
    ∑ v ∈ (nonrootVertices R).filter (fun v => 0 < H v), H v
  symm
  apply Finset.sum_filter_of_ne
  intro v _ hv
  omega

/-- M <= t*U also covers empty positive support. -/
theorem totalMultiplicity_le_positiveCount_mul_maxMultiplicity
    (R : RootedTree (Fin n)) (H : Fin n → ℕ) :
    totalMultiplicity R H ≤ positiveCount R H * maxMultiplicity R H := by
  rw [totalMultiplicity_eq_sum_positiveCoordinates]
  calc
    (∑ v ∈ positiveCoordinates R H, H v) ≤
        ∑ _v ∈ positiveCoordinates R H, maxMultiplicity R H := by
      apply Finset.sum_le_sum
      intro v hv
      simp only [positiveCoordinates, nonrootVertices, Finset.mem_filter,
        Finset.mem_univ, true_and] at hv
      exact multiplicity_le_maxMultiplicity R H v hv.1
    _ = positiveCount R H * maxMultiplicity R H := by simp [positiveCount]

/-- Seven reusable bounds, with B any upper bound on the state count.
The insertion field uses natural division and counts insertion-filter scans,
which must also be charged for full-key comparisons in a cost model. -/
structure ParameterBounds (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (B : ℕ) : Prop where
  candidateLength : (TreeBudgetFiniteSearch.candidates R H s T).length ≤ B
  expansions : (memoRowsStat R H s T (rootCount R H) H emptyCache).2.expansions ≤ B
  cacheLength : (memoRowsStat R H s T (rootCount R H) H emptyCache).1.2.length ≤ B
  candidates : (memoRowsStat R H s T (rootCount R H) H emptyCache).2.candidates ≤ B ^ 2
  calls : (memoRowsStat R H s T (rootCount R H) H emptyCache).2.calls ≤ 1 + B ^ 2
  insertionScans : (memoRowsStat R H s T (rootCount R H) H emptyCache).2.insertionScans ≤
    B * (B - 1) / 2
  lookupComparisons : (memoRowsStat R H s T (rootCount R H) H emptyCache).2.lookupComparisons ≤
    B + B ^ 3

theorem initial_bounds_of_stateBound_le (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (B : ℕ) (hB : stateBound R H ≤ B) :
    ParameterBounds R H s T B := by
  refine ⟨(candidates_length_le_stateBound R H s T).trans hB,
    (initial_expansions_le R H s T).trans hB, ?_, ?_, ?_, ?_, ?_⟩
  · rw [memoRowsStat, memoStat_empty_cache_length]
    exact (initial_expansions_le R H s T).trans hB
  · exact (initial_candidates_le_stateBound_sq R H s T).trans (Nat.pow_le_pow_left hB 2)
  · exact (initial_calls_le_stateBound_sq R H s T).trans
      (Nat.add_le_add_left (Nat.pow_le_pow_left hB 2) 1)
  · simpa only [triangle_closed] using
      (initial_insertionScans_le R H s T).trans (triangle_mono hB)
  · exact (initial_lookupComparisons_le_stateBound_cube R H s T).trans
      (Nat.add_le_add hB (Nat.pow_le_pow_left hB 3))

/-- Every field specializes to B = 2^M; no runtime claim is made. -/
theorem initial_bounds_two_pow_totalMultiplicity
    (R : RootedTree (Fin n)) (H : Fin n → ℕ) (s : Fin n → ℚ) (T : ℚ) :
    ParameterBounds R H s T (2 ^ totalMultiplicity R H) :=
  initial_bounds_of_stateBound_le R H s T _ (stateBound_le_two_pow_totalMultiplicity R H)

/-- Every field specializes to B = (U+1)^t, including t=0. -/
theorem initial_bounds_maxMultiplicity_pow_positiveCount
    (R : RootedTree (Fin n)) (H : Fin n → ℕ) (s : Fin n → ℚ) (T : ℚ) :
    ParameterBounds R H s T ((maxMultiplicity R H + 1) ^ positiveCount R H) :=
  initial_bounds_of_stateBound_le R H s T _
    (stateBound_le_maxMultiplicity_pow_positiveCount R H)

/-- A successful row-list witness has exactly the initial route count. This
holds even without assuming H(root)=0; success itself supplies the witness. -/
theorem initial_success_length_eq_rootCount (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (rows : Rows n)
    (hs : (memoRowsStat R H s T (rootCount R H) H emptyCache).1.1 = some rows) :
    rows.length = rootCount R H := by
  rw [memoRowsStat_erase] at hs
  exact (memoRows_sound R H s T (rootCount R H) H emptyCache rows
    (cacheValid_empty R H s T) hs).1

/-- This bounds the number of rows, not bytes or function-evaluation costs. -/
theorem initial_success_length_le_totalMultiplicity
    (R : RootedTree (Fin n)) (H : Fin n → ℕ) (s : Fin n → ℚ) (T : ℚ) (rows : Rows n)
    (hs : (memoRowsStat R H s T (rootCount R H) H emptyCache).1.1 = some rows) :
    rows.length ≤ totalMultiplicity R H := by
  rw [initial_success_length_eq_rootCount R H s T rows hs]
  exact rootCount_le_totalMultiplicity R H

end UAVProof.TreeBudgetParameterizedBounds

#print axioms UAVProof.TreeBudgetParameterizedBounds.rootCount_le_totalMultiplicity
#print axioms UAVProof.TreeBudgetParameterizedBounds.totalMultiplicity_eq_sum_positiveCoordinates
#print axioms
  UAVProof.TreeBudgetParameterizedBounds.totalMultiplicity_le_positiveCount_mul_maxMultiplicity
#print axioms UAVProof.TreeBudgetParameterizedBounds.initial_bounds_of_stateBound_le
#print axioms UAVProof.TreeBudgetParameterizedBounds.initial_bounds_two_pow_totalMultiplicity
#print axioms
  UAVProof.TreeBudgetParameterizedBounds.initial_bounds_maxMultiplicity_pow_positiveCount
#print axioms UAVProof.TreeBudgetParameterizedBounds.initial_success_length_eq_rootCount
#print axioms UAVProof.TreeBudgetParameterizedBounds.initial_success_length_le_totalMultiplicity
