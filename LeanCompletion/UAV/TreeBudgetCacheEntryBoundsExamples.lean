import LeanCompletion.UAV.TreeBudgetCacheEntryBounds

/-! A structural regression: a shadowed duplicate may contain any row list,
even when lookup validity and key reachability both hold. -/
namespace UAVProof.TreeBudgetCacheEntryBoundsExamples
open TreeFlowExistence TreeBudgetPatterns TreeBudgetMemoState TreeBudgetMemoReachability
open TreeBudgetResidualSearch
variable {n : ℕ}

def shadowedCache (rows : Rows n) : Cache n :=
  [((0, 0), some []), ((0, 0), some rows)]

/-- The arbitrary hidden answer is not constrained by CacheValid. -/
theorem shadowed_answers_unconstrained (R : RootedTree (Fin n))
    (s : Fin n → ℚ) (T : ℚ) (rows : Rows n) :
    CacheValid R 0 s T (shadowedCache rows) ∧
      AllKeysReachable R 0 s T (shadowedCache rows) ∧
      lookup (shadowedCache rows) (0, 0) = some (some []) ∧
      ((0, 0), some rows) ∈ shadowedCache rows ∧
      ¬ KeysNodup (shadowedCache rows) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q answer hh
    by_cases hq : (0, (0 : Fin n → ℕ)) = q
    · subst q
      have ha : answer = some [] := by simpa [shadowedCache, lookup] using hh.symm
      subst answer
      simp [AnswerValid, ResidualWitness]
    · simp [shadowedCache, lookup, hq] at hh
  · intro e he
    have hr : ReachableResidual R 0 s T 0 0 := by
      simpa [rootCount] using (ReachableResidual.initial (R := R) (H := 0) (s := s) (T := T))
    simp only [shadowedCache, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> exact hr
  · simp [shadowedCache, lookup]
  · simp [shadowedCache]
  · simp [shadowedCache, KeysNodup]

/-- A successful hidden entry can have more rows than its reachable key count. -/
theorem shadowed_success_can_exceed_key_count (R : RootedTree (Fin n))
    (s : Fin n → ℚ) (T : ℚ) :
    CacheValid R 0 s T (shadowedCache [0]) ∧
      AllKeysReachable R 0 s T (shadowedCache [0]) ∧
      ((0, 0), some [0]) ∈ shadowedCache (n := n) [0] ∧
      (0 : ℕ) < ([0] : Rows n).length := by
  have h := shadowed_answers_unconstrained R s T [0]
  exact ⟨h.1, h.2.1, h.2.2.2.1, by simp⟩

end UAVProof.TreeBudgetCacheEntryBoundsExamples

#print axioms UAVProof.TreeBudgetCacheEntryBoundsExamples.shadowed_answers_unconstrained
#print axioms UAVProof.TreeBudgetCacheEntryBoundsExamples.shadowed_success_can_exceed_key_count
