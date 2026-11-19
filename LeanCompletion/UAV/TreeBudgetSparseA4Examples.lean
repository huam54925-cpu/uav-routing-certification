import LeanCompletion.UAV.TreeBudgetSparseCostedParsing
import LeanCompletion.UAV.TreeBudgetSparseWeightedCost
import LeanCompletion.UAV.TreeBudgetSparseWireExamples

/-! Rejection and partial-prefix regressions. Kernel evaluation only.
The cost theorems cover parsing and column execution, not the entire verifier. -/
namespace UAVProof.TreeBudgetSparseA4Examples
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetSparseVerifier
open TreeBudgetSparsePrefixBounds TreeBudgetSparseCostedParsing TreeBudgetSparseWeightedCost
open TreeBudgetSparseWireExamples

def hugeEntries : RawCertificate := [(2 ^ 80, [2 ^ 70, 0]), (0, [1, 0])]
def hugeWire : Bits := encodeRaw hugeEntries

theorem huge_fields_parse : (parseRawD hugeWire).value = some hugeEntries := by
  simp [hugeWire]

theorem huge_fields_exceed_target : weightedSum (columnPairs hugeEntries 0) > 3 := by
  decide +kernel

theorem huge_fields_rejected : verify signedInput hugeWire = false := by decide +kernel

theorem huge_count_valid_row_rejected :
    verify signedInput (encodeRaw [(2 ^ 80, [1, 0])]) = false := by decide +kernel

theorem huge_column_value : (columnD hugeEntries 0).value = 2 ^ 150 := by
  rw [columnD_value]
  decide +kernel

theorem huge_column_width : (columnD hugeEntries 0).value.size = 151 := by
  rw [huge_column_value, Nat.size_pow]

theorem huge_wire_occupation : Occupies hugeWire hugeEntries := by
  exact ⟨encodeNat hugeEntries.length, [], by simp [hugeWire, encodeRaw, encodeList]⟩

theorem huge_rejected_column_work :
    (columnD hugeEntries 0).steps + (columnD hugeEntries 0).allocations ≤
      hugeWire.length * (164 * (hugeWire.length + 1)) +
      hugeWire.length * (320 * (hugeWire.length / 2 + 1) ^ 2) + 3 :=
  occupied_column_work hugeWire hugeEntries 0 hugeWire.length huge_wire_occupation
    (by decide +kernel) (by simp)

def partialEntries : RawCertificate := [(2 ^ 80, [2 ^ 70, 0])]
def partialWire : Bits := encodeNat 2 ++ partialEntries.flatMap encodeEntry ++ [true]

theorem partial_header : parseNat partialWire =
    some (2, partialEntries.flatMap encodeEntry ++ [true]) := by
  simp [partialWire, List.append_assoc, parseNat_append]

theorem partial_first_entry :
    parseMany parseEntry 1 (partialEntries.flatMap encodeEntry ++ [true]) =
      some (partialEntries, [true]) := by
  exact parseMany_append encodeEntry parseEntry parseEntry_append partialEntries [true]

theorem truncated_later_entry_rejected : (parseRawD partialWire).value = none := by
  rw [parseRawD_value]
  decide +kernel

theorem partial_wire_occupation : Occupies partialWire partialEntries :=
  certificate_prefix_occupies _ _ _ _ _ _ partial_header partial_first_entry

theorem rejected_partial_accumulator_width :
    (weightedSum (columnPairs partialEntries 0)).size ≤ partialWire.length / 2 :=
  column_accumulator_width _ _ _ partial_wire_occupation

theorem empty_prefix_width : (weightedSum (columnPairs [] 0)).size = 0 := by decide +kernel

theorem zero_count_illegal_row_parses :
    (parseRawD (encodeRaw [(0, [0, 0]), (3, [1, 0])])).value =
      some [(0, [0, 0]), (3, [1, 0])] := by simp

theorem zero_count_illegal_row_rejected :
    verify signedInput (encodeRaw [(0, [0, 0]), (3, [1, 0])]) = false := by decide +kernel

theorem huge_entry_count_rejected :
    (parseRawD (encodeNat (2 ^ 80) ++ [false])).value = none := by
  rw [parseRawD_value]
  decide +kernel

theorem huge_row_length_rejected :
    (parseRawD (encodeNat 1 ++ encodeNat 0 ++ encodeNat (2 ^ 80) ++ [false])).value = none := by
  rw [parseRawD_value]
  decide +kernel

theorem trailing_bit_rejected : (parseRawD (hugeWire ++ [false])).value = none := by
  simpa [hugeWire] using parseRaw_trailing_rejected hugeEntries [false] (by decide)

theorem noncanonical_header_rejected :
    (parseRawD [true, false, false]).value = none := by
  rw [parseRawD_value]
  decide +kernel

theorem missing_coordinate_zero : (columnD [(7, [])] 999).value = 0 := by
  rw [columnD_value]
  decide +kernel

theorem empty_certificate_parses : (parseRawD (encodeRaw [])).value = some [] := by simp

end UAVProof.TreeBudgetSparseA4Examples
