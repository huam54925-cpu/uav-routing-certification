import LeanCompletion.UAV.TreeBudgetBinaryCodec

namespace UAVProof.TreeBudgetBinaryCodecExamples
open TreeBudgetBinaryCodec

theorem natural_binary_boundaries :
    encodeNat 0 = [false] ∧ encodeNat 1 = [true, true, false] ∧
    encodeNat 2 = [true, false, true, true, false] ∧
    (encodeNat 7).length = 7 ∧ (encodeNat 8).length = 9 := by decide +kernel

theorem noncanonical_high_zero_rejected :
    parseNat (word [true, false]) = none ∧ parseNat (word [false]) = none := by
  decide +kernel

theorem malformed_words_rejected :
    parseNat [] = none ∧ parseNat [true] = none ∧ parseNat [true, true] = none := by
  decide +kernel

theorem signed_zero_and_unreduced_numerators :
    parseInt (true :: encodeNat 0) = none ∧
    parseInt (encodeInt (-12) ++ [true, false]) = some (-12, [true, false]) ∧
    parseInt (encodeInt 0) = some (0, []) := by decide +kernel

/-- The length guard rejects before invoking a million recursive iterations. -/
theorem giant_count_rejected_before_allocation :
    parseNats (encodeNat (2 ^ 20)) = none := by decide +kernel

def sample : RawInput :=
  ⟨2, 1, [1, 1], [3, 77], [-12, 0], [6, 2], -2, 4⟩

theorem input_roundtrip_preserves_raw_fields :
    parseInput (encodeInput sample) = some sample := by decide +kernel

theorem wrong_array_length_rejected :
    parseInput (encodeInput { sample with parents := [1] }) = none := by decide +kernel

theorem trailing_input_rejected :
    parseInput (encodeInput sample ++ [false]) = none := by decide +kernel

theorem truncated_budget_rejected :
    parseInput ((encodeInput sample).take ((encodeInput sample).length - 1)) = none := by
  decide +kernel

theorem explicit_matrix_roundtrip :
    parseMatrix (encodeMatrix [[0, 7, 0], [1, 0, 255]]) = some [[0, 7, 0], [1, 0, 255]] ∧
    parseMatrix (encodeMatrix []) = some [] := by decide +kernel

theorem framing_counts_only_consumed_prefix :
    (scanWord (word [true, false] ++ [true, true, true])).2 = 5 ∧
    (scanWord [true, false, true]).2 = 3 := by decide +kernel

end UAVProof.TreeBudgetBinaryCodecExamples
#print axioms UAVProof.TreeBudgetBinaryCodecExamples.natural_binary_boundaries
#print axioms UAVProof.TreeBudgetBinaryCodecExamples.noncanonical_high_zero_rejected
#print axioms UAVProof.TreeBudgetBinaryCodecExamples.malformed_words_rejected
#print axioms UAVProof.TreeBudgetBinaryCodecExamples.signed_zero_and_unreduced_numerators
#print axioms UAVProof.TreeBudgetBinaryCodecExamples.giant_count_rejected_before_allocation
#print axioms UAVProof.TreeBudgetBinaryCodecExamples.sample
#print axioms UAVProof.TreeBudgetBinaryCodecExamples.input_roundtrip_preserves_raw_fields
#print axioms UAVProof.TreeBudgetBinaryCodecExamples.wrong_array_length_rejected
#print axioms UAVProof.TreeBudgetBinaryCodecExamples.trailing_input_rejected
#print axioms UAVProof.TreeBudgetBinaryCodecExamples.truncated_budget_rejected
#print axioms UAVProof.TreeBudgetBinaryCodecExamples.explicit_matrix_roundtrip
#print axioms UAVProof.TreeBudgetBinaryCodecExamples.framing_counts_only_consumed_prefix
