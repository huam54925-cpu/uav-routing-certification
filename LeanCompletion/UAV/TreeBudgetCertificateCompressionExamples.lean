import LeanCompletion.UAV.TreeBudgetCertificateCompression
import LeanCompletion.UAV.TreeBudgetResidualBranchExamples

/-! Kernel-checked compression regressions, including the one-way checker contract. -/
namespace UAVProof.TreeBudgetCertificateCompressionExamples
open TreeBudgetPatterns TreeBudgetCertificate TreeBudgetBranchCertificate
open TreeBudgetCertificateCompression TreeBudgetExamples TreeFlowExamples
open TreeBudgetBranchExamples TreeBudgetResidualExamples

def p : Fin 3 → ℕ := ![1, 0, 0]
def q : Fin 3 → ℕ := ![0, 0, 1]
def r : Fin 3 → ℕ := ![1, 0, 1]

def mixed : List (Entry 3) := [(p, 2), (q, 0), (p, 3), (r, 1)]

theorem empty_entries : compressEntries ([] : List (Entry 3)) = [] := by decide +kernel

theorem empty_certificate :
    entries (compressCertificate (ofEntries ([] : List (Entry 3)))) = [] := by
  decide +kernel

theorem nonadjacent_duplicates_and_zero : compressEntries mixed = [(p, 5), (r, 1)] := by
  decide +kernel

theorem first_positive_occurrence_order :
    compressEntries [(p, 0), (q, 2), (p, 3), (q, 1)] = [(q, 3), (p, 3)] := by decide +kernel

theorem all_zero_counts_removed : compressEntries [(p, 0), (q, 0), (p, 0)] = [] := by decide +kernel

theorem distinct_positive_entries_unchanged :
    compressEntries [(p, 2), (q, 1), (r, 3)] = [(p, 2), (q, 1), (r, 3)] := by decide +kernel

theorem equal_cost_different_rows_kept :
    cost centerThree p (fun _ => 0) = cost centerThree q (fun _ => 0) ∧
      compressEntries [(p, 2), (q, 3)] = [(p, 2), (q, 3)] := by decide +kernel

def deepOne : Fin 4 → ℕ := ![0, 1, 1, 0]
def deepTwo : Fin 4 → ℕ := ![0, 1, 2, 0]

theorem equal_support_different_vectors_kept :
    (∀ v, 0 < deepOne v ↔ 0 < deepTwo v) ∧
      cost pathFour deepOne (fun _ => 0) = cost pathFour deepTwo (fun _ => 0) ∧
      compressEntries [(deepOne, 1), (deepTwo, 2)] = [(deepOne, 1), (deepTwo, 2)] := by
  decide +kernel

theorem full_vector_includes_root_coordinate :
    compressEntries [(p, 1), (![1, 99, 0], 2)] = [(p, 1), (![1, 99, 0], 2)] := by decide +kernel

theorem compressed_rows_positive_and_distinct : Reduced (compressEntries mixed) := by
  unfold Reduced
  decide +kernel

theorem compressed_pattern_totals :
    patternCount (compressEntries mixed) p = 5 ∧
      patternCount (compressEntries mixed) q = 0 ∧
      patternCount (compressEntries mixed) r = 1 := by decide +kernel

theorem compressed_total_and_columns :
    ((compressEntries mixed).map Prod.snd).sum = (mixed.map Prod.snd).sum ∧
      ∀ v, ((compressEntries mixed).map (fun e => e.2 * e.1 v)).sum =
        (mixed.map (fun e => e.2 * e.1 v)).sum := by decide +kernel

theorem repeated_compression_unchanged :
    compressEntries (compressEntries mixed) = compressEntries mixed := by decide +kernel

theorem repeated_certificate_compression_unchanged :
    entries (compressCertificate (compressCertificate (ofEntries mixed))) =
      entries (compressCertificate (ofEntries mixed)) := by decide +kernel

def validMixed : Certificate (Fin 3) := ofEntries [(p, 1), (q, 0), (p, 1), (q, 3)]

theorem valid_input_and_output_checked :
    checkCertificate centerThree directCounts 5 directFees 10 validMixed = true ∧
      checkCertificate centerThree directCounts 5 directFees 10
        (compressCertificate validMixed) = true := by decide +kernel

theorem compressed_size_bounds :
    (compressCertificate validMixed).size = 2 ∧
      (compressCertificate validMixed).size ≤ validMixed.size ∧
      (compressCertificate validMixed).size ≤ 5 := by decide +kernel

def invalidZero : Certificate (Fin 3) := ofEntries [(p, 2), (![0, 1, 0], 0)]

/-- A deliberately invalid zero-count row is checked before compression, but removed after it. -/
theorem checker_equality_is_not_unconditional :
    checkCertificate centerThree ![2, 99, 0] 2 (fun _ => 0) 0 invalidZero = false ∧
      checkCertificate centerThree ![2, 99, 0] 2 (fun _ => 0) 0
        (compressCertificate invalidZero) = true := by decide +kernel

theorem local_search_repeated_rows_compressed :
    (searchCompressed centerThree ![2, 99, 0] 2 (fun _ => 0) 0).map entries =
      some [(p, 2)] := by decide +kernel

theorem root_search_output_compressed_and_checked :
    (searchByRootCompressed centerThree directCounts 5 directFees 10).map
      (fun C => (C.size, checkCertificate centerThree directCounts 5 directFees 10 C)) =
        some (2, true) := by decide +kernel

theorem zero_fleet_negative_budget_checked :
    (searchByRootCompressed depotOnly (fun _ => 99) 0 (fun _ => 999) (-1)).map
      (fun C => (C.size, checkCertificate depotOnly (fun _ => 99) 0 (fun _ => 999) (-1) C)) =
        some (0, true) := by decide +kernel

theorem wrong_fleet_failure_preserved :
    (searchByRootCompressed centerThree directCounts 4 directFees 10).isSome = false := by
  decide +kernel

theorem backtracking_success_preserved :
    (searchCompressed pathFour backtrackH 2 backtrackFees 2).map
      (checkCertificate pathFour backtrackH 2 backtrackFees 2) = some true := by decide +kernel

theorem demand_signed_cancellation_checked :
    (solveByRootCompressed pathFour ![999, 2, 2, 1] 1 ![999, 0, 6, -8] 4).map
      (checkCertificate pathFour (TreeBudgetChecker.multiplicities pathFour ![999, 2, 2, 1])
        1 ![999, 0, 6, -8] 4) = some true := by decide +kernel

theorem invalid_demand_failure_preserved :
    (solveByRootCompressed pathFour ![0, 0, 0, 1] 1 (fun _ => 0) 100).isSome = false := by
  decide +kernel

end UAVProof.TreeBudgetCertificateCompressionExamples

#print axioms UAVProof.TreeBudgetCertificateCompressionExamples.first_positive_occurrence_order
#print axioms UAVProof.TreeBudgetCertificateCompressionExamples.equal_support_different_vectors_kept
#print axioms
  UAVProof.TreeBudgetCertificateCompressionExamples.checker_equality_is_not_unconditional
#print axioms
  UAVProof.TreeBudgetCertificateCompressionExamples.root_search_output_compressed_and_checked
#print axioms UAVProof.TreeBudgetCertificateCompressionExamples.demand_signed_cancellation_checked
