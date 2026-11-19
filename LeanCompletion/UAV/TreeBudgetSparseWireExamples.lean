import LeanCompletion.UAV.TreeBudgetSparseWireBounds

/-! Kernel-checked wire regressions. Every verifier call uses the public input
and certificate bitstrings, including malformed and large-count cases. -/
namespace UAVProof.TreeBudgetSparseWireExamples

open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetSparseVerifier

def signedRaw : RawInput :=
  ⟨2, 1, [1, 1], [3, 999], [-1, 999], [1, 1], -1, 1⟩

def signedInput : Bits := encodeSpecified 3 signedRaw

theorem duplicate_rows_accept :
    verify signedInput (encodeRaw [(1, [1, 0]), (2, [1, 0])]) = true := by decide +kernel

theorem legal_zero_count_accept :
    verify signedInput (encodeRaw [(0, [1, 0]), (3, [1, 0])]) = true := by decide +kernel

theorem illegal_zero_count_reject :
    verify signedInput (encodeRaw [(0, [0, 0]), (3, [1, 0])]) = false := by decide +kernel

theorem wrong_row_length_reject :
    verify signedInput (encodeRaw [(3, [1])]) = false := by decide +kernel

theorem wrong_root_coordinate_reject :
    verify signedInput (encodeRaw [(3, [1, 1])]) = false := by decide +kernel

theorem wrong_total_count_reject :
    verify signedInput (encodeRaw [(2, [1, 0])]) = false := by decide +kernel

theorem wrong_specified_routes_reject :
    verify (encodeSpecified 2 signedRaw) (encodeRaw [(3, [1, 0])]) = false := by decide +kernel

theorem certificate_trailing_bit_reject :
    verify signedInput (encodeRaw [(3, [1, 0])] ++ [false]) = false := by decide +kernel

theorem input_trailing_bit_reject :
    verify (signedInput ++ [false]) (encodeRaw [(3, [1, 0])]) = false := by decide +kernel

theorem truncated_certificate_reject : verify signedInput [true] = false := by decide +kernel

theorem noncanonical_certificate_header_reject :
    verify signedInput [true, false, false] = false := by decide +kernel

theorem bad_parent_cycle_reject :
    verify (encodeSpecified 3 {signedRaw with parents := [0, 1]})
      (encodeRaw [(3, [1, 0])]) = false := by decide +kernel

theorem zero_denominator_reject :
    verify (encodeSpecified 3 {signedRaw with denominators := [0, 1]})
      (encodeRaw [(3, [1, 0])]) = false := by decide +kernel

theorem zero_budget_denominator_reject :
    verify (encodeSpecified 3 {signedRaw with budgetDenominator := 0})
      (encodeRaw [(3, [1, 0])]) = false := by decide +kernel

theorem out_of_range_root_reject :
    verify (encodeSpecified 3 {signedRaw with root := 2})
      (encodeRaw [(3, [1, 0])]) = false := by decide +kernel

theorem inconsistent_input_shape_reject :
    verify (encodeSpecified 3 {signedRaw with n := 3})
      (encodeRaw [(3, [1, 0])]) = false := by decide +kernel

theorem weighted_descendant_column_reject :
    verify (encodeSpecified 2 ⟨3, 2, [1, 2, 2], [4, 2, 999], [-1, 0, 999], [1, 1, 1], -1, 1⟩)
      (encodeRaw [(2, [1, 1, 0])]) = false := by decide +kernel

theorem unreduced_signed_fees_accept :
    verify (encodeSpecified 3 { signedRaw with
        numerators := [-2, 999]
        denominators := [2, 1]
        budgetNumerator := -3
        budgetDenominator := 3 })
      (encodeRaw [(3, [1, 0])]) = true := by decide +kernel

def singletonRaw : RawInput := ⟨1, 0, [0], [999], [-10], [3], -99, 7⟩

theorem singleton_empty_fleet_accept :
    verify (encodeSpecified 0 singletonRaw) (encodeRaw []) = true := by decide +kernel

theorem singleton_nonempty_fleet_reject :
    verify (encodeSpecified 1 singletonRaw) (encodeRaw []) = false := by decide +kernel

theorem nonempty_tree_empty_fleet_accept :
    verify (encodeSpecified 0 {signedRaw with multiplicities := [0, 999]}) (encodeRaw []) = true := by
  decide +kernel

def huge : ℕ := 2 ^ 80

/-- One entry, although the route multiplicity exceeds machine-word range. -/
theorem binary_large_count_accept :
    verify (encodeSpecified huge {signedRaw with multiplicities := [huge, 999]})
      (encodeRaw [(huge, [1, 0])]) = true := by decide +kernel

theorem enormous_declared_entry_count_reject :
    verify signedInput (encodeNat huge) = false := by decide +kernel

theorem enormous_declared_row_length_reject :
    verify signedInput (encodeNat 1 ++ encodeNat 3 ++ encodeNat huge) = false := by decide +kernel

theorem entry_order_roundtrip :
    parseRaw (encodeRaw [(0, [1, 0]), (2, [1, 0]), (1, [0, 1])]) =
      some [(0, [1, 0]), (2, [1, 0]), (1, [0, 1])] := parseRaw_encode _

end UAVProof.TreeBudgetSparseWireExamples
