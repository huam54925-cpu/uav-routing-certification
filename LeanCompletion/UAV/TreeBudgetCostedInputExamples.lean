import LeanCompletion.UAV.TreeBudgetCostedInput

namespace UAVProof.TreeBudgetCostedInputExamples
open TreeBudgetCostedInput TreeBudgetBinaryCodec

def sample : RawInput := ⟨2, 0, [0, 0], [99, 2], [1, -3], [2, 2], -2, 1⟩

theorem accepted : (decodeRawCost sample).value.isSome = true := by decide +kernel

theorem bad_index : (decodeParentsCost 0 [0, 4]).value.isSome = false := by decide +kernel

theorem nonroot_cycle : (decodeParentsCost 0 [0, 2, 1]).value.isSome = false := by decide +kernel

theorem bad_denominator :
    (decodeRawCost { sample with denominators := [2, 0] }).value.isSome = false := by decide +kernel

theorem bad_shape :
    (decodeRawCost { sample with multiplicities := [2] }).value.isSome = false := by decide +kernel

end UAVProof.TreeBudgetCostedInputExamples

#print axioms UAVProof.TreeBudgetCostedInputExamples.accepted
#print axioms UAVProof.TreeBudgetCostedInputExamples.bad_index
#print axioms UAVProof.TreeBudgetCostedInputExamples.nonroot_cycle
#print axioms UAVProof.TreeBudgetCostedInputExamples.bad_denominator
#print axioms UAVProof.TreeBudgetCostedInputExamples.bad_shape
