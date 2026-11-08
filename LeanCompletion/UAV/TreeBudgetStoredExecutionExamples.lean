import LeanCompletion.UAV.TreeBudgetStoredExecution
import LeanCompletion.UAV.TreeBudgetCostedExecutionExamples
import LeanCompletion.UAV.TreeBudgetBinaryExamples

namespace UAVProof.TreeBudgetStoredExecutionExamples
open TreeBudgetBinaryCodec TreeBudgetStoredExecution TreeBudgetCostedExecutionExamples

def status (bits : Bits) : Option (Option Bits) :=
  match (executeStored bits).value with
  | .invalid => none
  | .storageError => some (some [])
  | .accepted out => some out.output

def agrees (bits : Bits) : Bool :=
  decide (observeStored (executeStored bits).value =
    some (observeReference (TreeBudgetBinaryPipeline.run bits)))

-- Nonfirst root; signed fees/budget; unreduced rational input.
#guard agrees (encodeInput TreeBudgetBinaryCodecExamples.sample)
#guard status (encodeInput emptyInstance) = some (some [false])
#guard ((status (encodeInput oneEdgeInstance)).bind id).bind parseMatrix = some [[0, 1]]
#guard status (encodeInput { oneEdgeInstance with budgetNumerator := -1 }) = some none
#guard agrees (encodeInput { oneEdgeInstance with budgetNumerator := -1 })
#guard status (encodeInput { oneEdgeInstance with parents := [0, 1] }) = none
#guard status (encodeInput ⟨3, 0, [0, 2, 1], [0, 1, 1], [0, 1, 1], [1, 1, 1], 2, 1⟩) = none
#guard status (encodeInput { oneEdgeInstance with denominators := [0, 1] }) = none
#guard status (encodeInput { oneEdgeInstance with budgetDenominator := 0 }) = none
#guard status ((encodeInput oneEdgeInstance).dropLast) = none
#guard status (encodeInput oneEdgeInstance ++ [false]) = none
#guard status [] = none
#guard agrees []
#guard agrees (encodeInput oneEdgeInstance)

end UAVProof.TreeBudgetStoredExecutionExamples
