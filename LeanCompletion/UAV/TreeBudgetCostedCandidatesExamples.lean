import LeanCompletion.UAV.TreeBudgetCostedCandidates

namespace UAVProof.TreeBudgetCostedCandidatesExamples
open TreeBudgetCostedCandidates TreeBudgetParentArray

def starTwo : ParentArray 2 := ⟨0, #v[0, 0]⟩

theorem starTwo_valid : Valid starTwo :=
  (validateB_eq_true starTwo).mp (by decide +kernel)

theorem bounded_order :
    ((boundedCost 2 #v[1, 2]).value.map Vector.toList) =
      [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2]] := by decide +kernel

theorem normalized_root_ignored :
    ((candidateCost starTwo #v[99, 2] #v[1, 1] 1).value.map Vector.toList) =
      [[0, 1]] := by decide +kernel

theorem signed_fee_accepted :
    ((candidateCost starTwo #v[99, 2] #v[1, -3] (-2)).value.map Vector.toList) =
      [[0, 1]] := by decide +kernel

theorem root_count_binary : (rootCountCost starTwo #v[500, 7]).value = 7 := by decide +kernel

end UAVProof.TreeBudgetCostedCandidatesExamples

#print axioms UAVProof.TreeBudgetCostedCandidatesExamples.starTwo_valid
#print axioms UAVProof.TreeBudgetCostedCandidatesExamples.bounded_order
#print axioms UAVProof.TreeBudgetCostedCandidatesExamples.normalized_root_ignored
#print axioms UAVProof.TreeBudgetCostedCandidatesExamples.signed_fee_accepted
#print axioms UAVProof.TreeBudgetCostedCandidatesExamples.root_count_binary
