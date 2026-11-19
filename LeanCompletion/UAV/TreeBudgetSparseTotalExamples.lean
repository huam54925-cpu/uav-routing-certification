import LeanCompletion.UAV.TreeBudgetSparseTotalWork
import LeanCompletion.UAV.TreeBudgetSparseA4Examples

/-! End-to-end executions of the costed entry, including early and late
rejections. General work bounds are independent of these finite examples. -/
namespace UAVProof.TreeBudgetSparseTotalExamples
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetSparseVerifier
open TreeBudgetSparseCostedFrontend TreeBudgetSparseTotalWork TreeBudgetCostedCandidates
open TreeBudgetSparseWireExamples TreeBudgetSparseA4Examples

theorem accepted_duplicate_rows :
    (verifyD signedInput (encodeRaw [(1, [1, 0]), (2, [1, 0])])).value = true := by
  rw [verifyD_value]
  decide +kernel

theorem accepted_zero_count :
    (verifyD signedInput (encodeRaw [(0, [1, 0]), (3, [1, 0])])).value = true := by
  rw [verifyD_value]
  decide +kernel

theorem rejected_zero_count_row :
    (verifyD signedInput (encodeRaw [(0, [0, 0]), (3, [1, 0])])).value = false := by
  rw [verifyD_value]
  decide +kernel

theorem rejected_huge_fields : (verifyD signedInput hugeWire).value = false := by
  rw [verifyD_value]
  exact huge_fields_rejected

theorem rejected_huge_fields_total_bound :
    work (verifyD signedInput hugeWire) ≤
      4194304 * (signedInput.length + hugeWire.length + 1) ^ 6 := verifyD_work _ _

theorem rejected_huge_route_count :
    (verifyD (encodeSpecified (2 ^ 80) signedRaw) hugeWire).value = false := by
  rw [verifyD_value]
  decide +kernel

theorem rejected_later_truncation : (verifyD signedInput partialWire).value = false := by
  rw [verifyD_value]
  decide +kernel

theorem rejected_row_dimension :
    (verifyD signedInput (encodeRaw [(3, [1])])).value = false := by
  rw [verifyD_value]
  decide +kernel

theorem rejected_parent_cycle :
    (verifyD (encodeSpecified 3 { signedRaw with parents := [0, 1] }) hugeWire).value = false := by
  rw [verifyD_value]
  decide +kernel

theorem rejected_denominator :
    (verifyD (encodeSpecified 3 { signedRaw with denominators := [0, 1] }) hugeWire).value = false := by
  rw [verifyD_value]
  decide +kernel

theorem rejected_empty_input : (verifyD [] hugeWire).value = false := by
  rw [verifyD_value]
  decide +kernel

theorem rejected_shape :
    (verifyD (encodeSpecified 3 { signedRaw with n := 2 ^ 80 }) hugeWire).value = false := by
  rw [verifyD_value]
  decide +kernel

theorem rejected_signed_large_row :
    (verifyD (encodeSpecified 1 ⟨3, 2, [1, 2, 2], [1, 1, 0],
      [2 ^ 80, -(2 ^ 80), 0], [1, 1, 1], 0, 1⟩)
      (encodeRaw [(1, [2 ^ 80, 1, 0])])).value = false := by
  rw [verifyD_value]
  decide +kernel

theorem accepted_empty_singleton :
    (verifyD (encodeSpecified 0 ⟨1, 0, [0], [999], [0], [1], 0, 1⟩) (encodeRaw [])).value = true := by
  rw [verifyD_value]
  decide +kernel

end UAVProof.TreeBudgetSparseTotalExamples
