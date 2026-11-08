import LeanCompletion.UAV.TreeBudgetStoredExecution
import LeanCompletion.UAV.TreeBudgetBinaryTotalWork

/-! Polynomial work, including auxiliary allocations, for every rejected
bitstring. This theorem invokes no search and assumes no phase-cost bound. -/
namespace UAVProof.TreeBudgetStoredRejectionBounds
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetCostedParsing TreeBudgetCostedInput
open TreeBudgetStoredExecution TreeBudgetBitMachine TreeBudgetCostedCandidates

theorem executeStored_rejection_work (bits : Bits) (h : parse bits = none) :
    (executeStored bits).steps + (executeStored bits).allocations ≤
      262144 * (bits.length + 1) ^ 3 := by
  have hp := parseInputD_steps bits
  have ha := parseInputD_allocations_le_steps bits
  have h2 : (bits.length + 1) ^ 2 ≤ (bits.length + 1) ^ 3 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ (bits.length + 1) ^ 3 := one_le_pow₀ (by omega)
  cases he : parseInput bits with
  | none =>
    simp only [executeStored, parseInputD_value, he, executeRaw]
    nlinarith only [hp, ha, h2, h1]
  | some raw =>
    have hd : decodeRaw raw = none := by simpa [TreeBudgetBinaryInput.parse, he] using h
    have hv := TreeBudgetBinaryTotalWork.decodeRawCost_work_encoded raw
      (parseInput_canonical bits raw he).2
    rw [← (parseInput_canonical bits raw he).1] at hv
    simp only [executeStored, parseInputD_value, he, executeRaw, decodeRawCost_value,
      hd, executeChecked]
    unfold work at hv
    nlinarith only [hp, ha, h2, h1, hv]

end UAVProof.TreeBudgetStoredRejectionBounds
