import LeanCompletion.UAV.TreeBudgetSparseTotalWork
import LeanCompletion.UAV.TreeBudgetSparseNPBridge

/-! The same short witness from A3 has an instance-only reference work bound.
This is not a bound on TM2 transitions. -/
namespace UAVProof.TreeBudgetSparseWitnessWork
open TreeBudgetBinaryCodec TreeBudgetSparseVerifier TreeBudgetSparseNPBridge
open TreeBudgetSparseWireBounds TreeBudgetSparseCostedFrontend TreeBudgetSparseTotalWork
open TreeBudgetCostedCandidates TreeBudgetBitMachine

theorem short_pair_length (L W : ℕ) (h : W ≤ L * (L / 2 + 1)) :
    L + W + 1 ≤ (L + 1) ^ 2 := by
  have hd : L / 2 ≤ L := Nat.div_le_self _ _
  have hm := Nat.mul_le_mul_left L hd
  nlinarith

theorem language_iff_short_bounded_work (x : Bits) :
    x ∈ language ↔ ∃ y : Bits,
      y.length ≤ x.length * (x.length / 2 + 1) ∧ verify x y = true ∧
      work (verifyD x y) ≤ 4194304 * (x.length + 1) ^ 12 := by
  constructor
  · intro hx
    obtain ⟨y, hy, hv⟩ := (language_iff_short_witness x).mp hx
    refine ⟨y, hy, hv, (verifyD_work x y).trans ?_⟩
    have hp := Nat.pow_le_pow_left (short_pair_length x.length y.length hy) 6
    calc
      4194304 * (x.length + y.length + 1) ^ 6 ≤
          4194304 * ((x.length + 1) ^ 2) ^ 6 := Nat.mul_le_mul_left _ hp
      _ = 4194304 * (x.length + 1) ^ 12 := by rw [← pow_mul]
  · rintro ⟨y, _, hv, _⟩
    exact accepted_in_language x y hv

end UAVProof.TreeBudgetSparseWitnessWork
