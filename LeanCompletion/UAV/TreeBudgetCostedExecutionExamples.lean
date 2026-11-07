import LeanCompletion.UAV.TreeBudgetBinaryTotalWork

namespace UAVProof.TreeBudgetCostedExecutionExamples
open TreeBudgetBinaryCodec TreeBudgetCostedExecution

def emptyInstance : RawInput := ⟨1, 0, [0], [99], [-12], [6], -2, 4⟩
def oneEdgeInstance : RawInput := ⟨2, 0, [0, 0], [77, 1], [0, 0], [1, 1], 0, 1⟩

theorem complete_empty_matrix :
    ((execute (encodeInput emptyInstance)).value.map (fun out => out.output)) =
      some (some [false]) := by decide +kernel

theorem complete_one_edge_matrix :
    ((execute (encodeInput oneEdgeInstance)).value.bind
      (fun out => out.output.bind parseMatrix)) = some [[0, 1]] := by decide +kernel

theorem complete_infeasible_is_accepted :
    ((execute (encodeInput { oneEdgeInstance with budgetNumerator := -1 })).value.map
      (fun out => out.output)) = some none := by decide +kernel

theorem complete_invalid_parent_is_rejected :
    (execute (encodeInput { oneEdgeInstance with parents := [0, 1] })).value.isNone = true := by
  decide +kernel

end UAVProof.TreeBudgetCostedExecutionExamples
