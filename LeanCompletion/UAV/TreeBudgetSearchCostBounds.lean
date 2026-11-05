import LeanCompletion.UAV.TreeBudgetSearchStatsBounds
import LeanCompletion.UAV.TreeBudgetCandidateCount

/-! Candidate and association-list comparison bounds for the existing executor.
Generic lookup bounds allow arbitrary candidate lists and raw caches. The final
tree-entry corollaries combine them with the candidate-length and state bounds.
These count visited cache entries, not the internal cost of full-key comparisons,
candidate generation, arithmetic, witness construction or elapsed time. -/
namespace UAVProof.TreeBudgetSearchCostBounds
open TreeFlowExistence TreeBudgetPatterns TreeBudgetMemoState TreeBudgetSearchStats
open TreeBudgetMemoBounds TreeBudgetSearchStatsBounds TreeBudgetCandidateCount
variable {n : ℕ}

/-- Even an unsuccessful lookup visits each list entry at most once. Duplicate
keys count as separate entries; a hit may stop before reaching the end. -/
theorem lookupStat_comparisons_le_length (cs : Cache n) (q : Key n) :
    (lookupStat cs q).2 ≤ cs.length := by
  induction cs with
  | nil => simp [lookupStat]
  | cons e cs ih =>
    by_cases he : e.1 = q
    · simp [lookupStat, he]
    · simp only [lookupStat, if_neg he, List.length_cons]
      omega

/-- A failed child's final cache is the suffix's initial cache. The existing
growth theorem bounds both segments' comparisons by the final cache length. -/
theorem scanStat_lookupComparisons_le_cache_length
    (solve : (Fin n → ℕ) → Cache n → Measured (Answer n × Cache n))
    (hg : ∀ r cs, (solve r cs).1.2.length = cs.length + (solve r cs).2.expansions)
    (hl : ∀ r cs, (solve r cs).2.lookupComparisons ≤
      (solve r cs).2.calls * (solve r cs).1.2.length)
    (r : Fin n → ℕ) (tail : List (Fin n → ℕ)) (cs : Cache n) :
    (scanStat solve r tail cs).2.lookupComparisons ≤
      (scanStat solve r tail cs).2.calls * (scanStat solve r tail cs).1.2.length := by
  induction tail generalizing cs with
  | nil => simp [scanStat]
  | cons p tail ih =>
    by_cases hp : ∀ v, p v ≤ r v
    · have hc := hl (r - p) cs
      cases ha : (solve (r - p) cs).1.1 with
      | none =>
        have ht := ih (solve (r - p) cs).1.2
        have hlen := scanStat_cache_length solve hg r tail (solve (r - p) cs).1.2
        have hmono : (solve (r - p) cs).1.2.length ≤
            (scanStat solve r tail (solve (r - p) cs).1.2).1.2.length := by
          rw [hlen]
          omega
        have hc' := hc.trans (Nat.mul_le_mul_left (solve (r - p) cs).2.calls hmono)
        simp only [scanStat, if_pos hp, ha, bump, Counts.add, Nat.zero_add, Nat.add_mul]
        omega
      | some rows =>
        simpa only [scanStat, if_pos hp, ha, bump, Counts.add, Nat.zero_add] using hc
    · simpa only [scanStat, if_neg hp, bump, Counts.add, Nat.zero_add] using ih cs

/-- All calls compare against a cache no longer than the returned cache. -/
theorem memoStat_lookupComparisons_le_cache_length (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    (memoStat ps k r cs).2.lookupComparisons ≤
      (memoStat ps k r cs).2.calls * (memoStat ps k r cs).1.2.length := by
  induction k generalizing r cs with
  | zero =>
    have hl := lookupStat_comparisons_le_length cs (0, r)
    cases hm : lookup cs (0, r) with
    | some a => simpa [memoStat, lookupStat_erase, hm] using hl
    | none =>
      simp only [memoStat, lookupStat_erase, hm, insertStat, Counts.add]
      rw [insert_length_of_lookup_none cs (0, r) _ hm]
      simp only [Nat.add_zero, Nat.one_mul]
      omega
  | succ k ih =>
    have hl := lookupStat_comparisons_le_length cs (k + 1, r)
    cases hm : lookup cs (k + 1, r) with
    | some a => simpa [memoStat, lookupStat_erase, hm] using hl
    | none =>
      have hs := scanStat_lookupComparisons_le_cache_length (memoStat ps k)
        (memoStat_cache_length ps k) ih r ps cs
      have hg := scanStat_cache_length (memoStat ps k) (memoStat_cache_length ps k) r ps cs
      have hp := scanStat_parent_lookup_none ps ps k r cs hm
      simp only [memoStat, lookupStat_erase, hm, insertStat, Counts.add]
      rw [insert_length_of_lookup_none _ _ _ hp]
      simp only [Nat.add_zero]
      nlinarith

/-- General raw-cache bound. K0 includes duplicate entries, even on a warm hit. -/
theorem memoStat_lookupComparisons_le (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) (cs : Cache n) :
    (memoStat ps k r cs).2.lookupComparisons ≤
      (memoStat ps k r cs).2.calls * (cs.length + (memoStat ps k r cs).2.expansions) := by
  rw [← memoStat_cache_length]
  exact memoStat_lookupComparisons_le_cache_length ps k r cs

theorem memoStat_empty_lookupComparisons_le (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) :
    (memoStat ps k r emptyCache).2.lookupComparisons ≤
      (memoStat ps k r emptyCache).2.calls * (memoStat ps k r emptyCache).2.expansions := by
  simpa only [emptyCache, List.length_nil, Nat.zero_add] using
    memoStat_lookupComparisons_le ps k r emptyCache

/-- Cold-run bound retaining the length of the supplied candidate list. -/
theorem memoStat_empty_lookupComparisons_le_polynomial (ps : List (Fin n → ℕ))
    (k : ℕ) (r : Fin n → ℕ) :
    (memoStat ps k r emptyCache).2.lookupComparisons ≤
      (memoStat ps k r emptyCache).2.expansions +
        ps.length * (memoStat ps k r emptyCache).2.expansions ^ 2 := by
  have hc := (memoStat_calls_le ps k r emptyCache).trans
    (Nat.add_le_add_left (memoStat_candidates_le ps k r emptyCache) 1)
  have h := (memoStat_empty_lookupComparisons_le ps k r).trans
    (Nat.mul_le_mul_right (memoStat ps k r emptyCache).2.expansions hc)
  nlinarith

theorem initial_candidates_le_stateBound_sq (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (memoRowsStat R H s T (rootCount R H) H emptyCache).2.candidates ≤ (stateBound R H) ^ 2 := by
  have h := (initial_candidates_le R H s T).trans
    (Nat.mul_le_mul_right (stateBound R H) (candidates_length_le_stateBound R H s T))
  simpa only [pow_two] using h

theorem initial_calls_le_stateBound_sq (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (memoRowsStat R H s T (rootCount R H) H emptyCache).2.calls ≤ 1 + (stateBound R H) ^ 2 := by
  exact (memoStat_calls_le _ _ _ _).trans
    (Nat.add_le_add_left (initial_candidates_le_stateBound_sq R H s T) 1)

theorem initial_lookupComparisons_le_calls_mul_stateBound
    (R : RootedTree (Fin n)) (H : Fin n → ℕ) (s : Fin n → ℚ) (T : ℚ) :
    (memoRowsStat R H s T (rootCount R H) H emptyCache).2.lookupComparisons ≤
      (memoRowsStat R H s T (rootCount R H) H emptyCache).2.calls * stateBound R H := by
  exact (memoStat_empty_lookupComparisons_le _ _ _).trans
    (Nat.mul_le_mul_left _ (initial_expansions_le R H s T))

theorem initial_lookupComparisons_le (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (memoRowsStat R H s T (rootCount R H) H emptyCache).2.lookupComparisons ≤
      stateBound R H +
        (TreeBudgetFiniteSearch.candidates R H s T).length * (stateBound R H) ^ 2 := by
  have h := (initial_lookupComparisons_le_calls_mul_stateBound R H s T).trans
    (Nat.mul_le_mul_right (stateBound R H) (initial_calls_le R H s T))
  nlinarith

theorem initial_lookupComparisons_le_stateBound_cube
    (R : RootedTree (Fin n)) (H : Fin n → ℕ) (s : Fin n → ℚ) (T : ℚ) :
    (memoRowsStat R H s T (rootCount R H) H emptyCache).2.lookupComparisons ≤
      stateBound R H + (stateBound R H) ^ 3 := by
  have h := (initial_lookupComparisons_le_calls_mul_stateBound R H s T).trans
    (Nat.mul_le_mul_right (stateBound R H) (initial_calls_le_stateBound_sq R H s T))
  nlinarith

end UAVProof.TreeBudgetSearchCostBounds

#print axioms UAVProof.TreeBudgetSearchCostBounds.lookupStat_comparisons_le_length
#print axioms UAVProof.TreeBudgetSearchCostBounds.scanStat_lookupComparisons_le_cache_length
#print axioms UAVProof.TreeBudgetSearchCostBounds.memoStat_lookupComparisons_le_cache_length
#print axioms UAVProof.TreeBudgetSearchCostBounds.memoStat_lookupComparisons_le
#print axioms UAVProof.TreeBudgetSearchCostBounds.memoStat_empty_lookupComparisons_le
#print axioms UAVProof.TreeBudgetSearchCostBounds.memoStat_empty_lookupComparisons_le_polynomial
#print axioms UAVProof.TreeBudgetSearchCostBounds.initial_candidates_le_stateBound_sq
#print axioms UAVProof.TreeBudgetSearchCostBounds.initial_calls_le_stateBound_sq
#print axioms UAVProof.TreeBudgetSearchCostBounds.initial_lookupComparisons_le_calls_mul_stateBound
#print axioms UAVProof.TreeBudgetSearchCostBounds.initial_lookupComparisons_le
#print axioms UAVProof.TreeBudgetSearchCostBounds.initial_lookupComparisons_le_stateBound_cube
