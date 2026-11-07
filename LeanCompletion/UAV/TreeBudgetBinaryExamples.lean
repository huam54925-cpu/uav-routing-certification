import LeanCompletion.UAV.TreeBudgetBinaryInput
import LeanCompletion.UAV.TreeBudgetBinarySearch
import LeanCompletion.UAV.TreeBudgetBinaryCodecExamples

namespace UAVProof.TreeBudgetBinaryExamples
open TreeBudgetBinaryInput TreeBudgetBinaryCodec TreeBudgetBinarySearch
open TreeBudgetVectorMemoState TreeBudgetSearchStats

theorem accepted_nonfirst_root_preserves_fields :
    (parse (encodeInput TreeBudgetBinaryCodecExamples.sample)).map
      (fun I => (I.n, I.parents.root.val, I.H.toList, I.numerators.toList,
        I.denominators.toList, I.budgetNumerator, I.budgetDenominator)) =
      some (2, 1, [3, 77], [-12, 0], [6, 2], -2, 4) := by rfl

theorem rejected_parent_cycle :
    (parse (encodeInput ⟨3, 0, [0, 2, 1], [0, 1, 1], [0, 1, 1], [1, 1, 1], 2, 1⟩)).isNone = true := by
  decide +kernel

theorem rejected_zero_denominators :
    (parse (encodeInput { TreeBudgetBinaryCodecExamples.sample with denominators := [0, 2] })).isNone = true ∧
    (parse (encodeInput { TreeBudgetBinaryCodecExamples.sample with budgetDenominator := 0 })).isNone = true := by
  decide +kernel

def one : Vector ℕ 1 := #v[1]
def zero : Vector ℕ 1 := #v[0]

theorem binary_search_success_exact :
    (search [one] 1 one []).value =
      (some [one], [((1, one), some [one]), ((0, zero), some [])]) := by
  apply Prod.ext
  · decide +kernel
  · decide +kernel

theorem binary_search_events_exact :
    (search [one] 1 one []).events =
      { calls := 2, hits := 0, expansions := 2, candidates := 1,
        lookupComparisons := 0, insertionScans := 1 } := by decide +kernel

theorem binary_failed_first_hit_masks_duplicate :
    (search [] 0 zero [((0, zero), none), ((0, zero), some [])]).value =
      (none, [((0, zero), none), ((0, zero), some [])]) := by
  apply Prod.ext
  · decide +kernel
  · decide +kernel

theorem binary_empty_success_is_present :
    (search [] 0 zero []).value.1 = some [] ∧
      0 < (search [] 0 zero []).work ∧ 0 < (search [] 0 zero []).allocations := by
  decide +kernel

end UAVProof.TreeBudgetBinaryExamples
