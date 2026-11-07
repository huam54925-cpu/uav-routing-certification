import LeanCompletion.UAV.TreeBudgetSearchStore

namespace UAVProof.TreeBudgetSearchStoreExamples
open TreeBudgetSearchStore TreeBudgetAllocationBounds

def sample : ℕ × Heap :=
  let (key₁, h₁) := allocateBlob #[] (encodeKey (1, [0, 1]))
  let (key₂, h₂) := allocateBlob h₁ (encodeKey (2, [0, 2]))
  let (yes, h₃) := allocateBlob h₂ (encodeAnswer (some [[0, 1]]))
  let (no, h₄) := allocateBlob h₃ (encodeAnswer none)
  let (nil, h₅) := emptyCache h₄
  let (old, h₆) := prependCache h₅ key₁ no nil
  let (middle, h₇) := prependCache h₆ key₂ no old
  prependCache h₇ key₁ yes middle

theorem first_duplicate_wins :
    lookupStore (sample.2.size + 1) sample.2 sample.1 (encodeKey (1, [0, 1])) =
      some (some (some [[0, 1]])) := by decide +kernel

theorem stored_failure_distinct_from_miss :
    lookupStore (sample.2.size + 1) sample.2 sample.1 (encodeKey (2, [0, 2])) =
      some (some none) := by decide +kernel

theorem miss_is_not_malformed :
    lookupStore (sample.2.size + 1) sample.2 sample.1 (encodeKey (3, [0, 3])) =
      some none := by decide +kernel

theorem invalid_address_rejected : lookupStore 10 sample.2 (sample.2.size + 1) [] = none := by
  decide +kernel

theorem ordered_decoder_retains_duplicates :
    decodeCacheStore (sample.2.size + 1) sample.2 sample.1 =
      some [((1, [0, 1]), some [[0, 1]]), ((2, [0, 2]), none), ((1, [0, 1]), none)] := by
  decide +kernel

end UAVProof.TreeBudgetSearchStoreExamples

#print axioms UAVProof.TreeBudgetSearchStoreExamples.first_duplicate_wins
#print axioms UAVProof.TreeBudgetSearchStoreExamples.stored_failure_distinct_from_miss
#print axioms UAVProof.TreeBudgetSearchStoreExamples.miss_is_not_malformed
#print axioms UAVProof.TreeBudgetSearchStoreExamples.invalid_address_rejected

#print axioms UAVProof.TreeBudgetSearchStoreExamples.ordered_decoder_retains_duplicates
