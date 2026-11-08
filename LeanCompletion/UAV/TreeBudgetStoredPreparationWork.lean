import LeanCompletion.UAV.TreeBudgetStoredSearchWork
import LeanCompletion.UAV.TreeBudgetStoredInputBounds

namespace UAVProof.TreeBudgetStoredPreparationWork
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetCostedCandidates TreeBudgetAllocationBounds TreeBudgetTypedStore
open TreeBudgetSharedAnswerStore TreeBudgetChargedCache TreeBudgetStoredSearch TreeBudgetStoredPreparation
open TreeBudgetStoredWork TreeBudgetStoredPayloadWork TreeBudgetStoredAllocation TreeBudgetStoredInputBounds
open TreeBudgetStoredWorkInvariant TreeBudgetStoredSearchWork TreeBudgetBinaryCodec TreeBudgetSearchStore
open TreeBudgetCostedSearchBounds TreeBudgetBinaryInput TreeBudgetBinaryPipeline TreeBudgetBinaryPreprocessing
open TreeBudgetBinaryPipelineBounds TreeBudgetBinaryExecutionBounds TreeBudgetBinaryTotalWork

set_option maxHeartbeats 1000000 in
theorem rowsWrite_work {n : ℕ} (heap : Heap) (ps : List (Vector ℕ n))
    (H : Vector ℕ n) (K B N W : ℕ) (hb : PayloadBounds K H B)
    (hh : WellFormed heap) (hps : ∀ p ∈ ps, VecSmall H p)
    (hw : (8 * (N + B + 1)).size ≤ W)
    (hc : (rowsWrite heap ps).value.2.size ≤ N) :
    work (rowsWrite heap ps) ≤ 32768 * (B + 1) ^ 3 * (W + 2) * (ps.length + 1) := by
  have hpow : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by omega)
  have hm := Nat.mul_le_mul_right (W + 2) hpow
  induction ps generalizing heap with
  | nil =>
    have hsize := rowsWrite_size (n := n) heap [] hh
    simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hsize
    have ha := alloc_work heap [.bit false] W
      (width_in_capacity B N W _ hw (by simp only [List.length_cons, List.length_nil]; omega))
    simp only [rowsWrite, List.length_nil, Nat.zero_add, Nat.mul_one]
    norm_num only [List.length_cons, List.length_nil] at ha
    nlinarith only [ha, hm]
  | cons p ps ih =>
    let tail := (rowsWrite heap ps).value
    have ht := rowsWrite_correct heap ps hh
    have hs := rowsWrite_size heap (p :: ps) hh
    have htSize := rowsWrite_size heap ps hh
    have hvSize := vectorWrite_size tail.2 p
    simp only [List.map_cons, List.sum_cons] at hs
    have htailN : tail.2.size ≤ N := by dsimp [tail]; omega
    have hrowN : tail.2.size + rowSlots p + 3 ≤ N := by dsimp [tail]; omega
    have hi := ih heap hh (fun p hp => hps p (by simp [hp])) htailN
    have hsp := hps p (by simp)
    have hv := vectorWrite_work tail.2 p B W hb.dimension
      (fun i => (Nat.size_le_size (hsp i)).trans (hb.coordinates i)) (rows_bytes hb hsp)
      (width_in_capacity B N W _ hw (by omega))
    have ha := alloc_work (vectorWrite tail.2 p).value.2
      [.bit true, .ref (vectorWrite tail.2 p).value.1, .ref tail.1] W
      (width_in_capacity B N W _ hw (by simp only [List.length_cons, List.length_nil]; omega))
    norm_num only [List.length_cons, List.length_nil] at ha
    simp only [rowsWrite, work_bind, work_charge, List.length_cons]
    change work (rowsWrite heap ps) + (work (vectorWrite tail.2 p) + (1 + 3 +
      work (alloc (vectorWrite tail.2 p).value.2
        [.bit true, .ref (vectorWrite tail.2 p).value.1, .ref tail.1]))) ≤ _
    nlinarith only [hi, hv, ha, hm]

set_option maxHeartbeats 1000000 in
theorem initializeStore_work {n : ℕ} (P : Prepared n) (K B N W : ℕ)
    (hb : PayloadBounds K P.residual B) (hps : ∀ p ∈ P.candidates, VecSmall P.residual p)
    (hw : (8 * (N + B + 1)).size ≤ W) (hc : (initializeStore P).value.heap.size ≤ N) :
    work (initializeStore P) ≤ 65536 * (B + 1) ^ 3 * (W + 2) * (P.candidates.length + 2) := by
  let root := allocateBlock #[] [.bit false]
  have hroot : WellFormed root := by
    apply wellFormed_allocateBlock
    · simp [WellFormed, TreeBudgetAllocationBounds.read]
    · simp
  let rows := (rowsWrite root P.candidates).value
  have hs := initializeStore_size P
  have hrowsSize := rowsWrite_size root P.candidates hroot
  have hrootSize : root.size = 1 := by simp [root, allocateBlock_size]
  have hrowsN : rows.2.size + rowSlots P.residual + 1 ≤ N := by dsimp [rows]; omega
  have hr := rowsWrite_work root P.candidates P.residual K B N W hb hroot hps hw (by omega)
  have hv := vectorWrite_work rows.2 P.residual B W hb.dimension hb.coordinates
    (rows_bytes hb (fun _ => le_rfl)) (width_in_capacity B N W _ hw (by omega))
  have ha := alloc_work #[] [.bit false] W
    (width_in_capacity B N W _ hw (by simp; omega))
  have hvecSize := vectorWrite_size rows.2 P.residual
  have he := alloc_work (vectorWrite rows.2 P.residual).value.2 [.bit false] W
    (width_in_capacity B N W _ hw (by simp only [List.length_cons, List.length_nil]; omega))
  norm_num only [List.length_cons, List.length_nil] at ha he
  have hpow : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by omega)
  have hm := Nat.mul_le_mul_right (W + 2) hpow
  simp only [initializeStore, work_bind, alloc_value #[] [.bit false] (by simp)]
  change work (alloc #[] [.bit false]) + (work (rowsWrite root P.candidates) +
    (work (vectorWrite rows.2 P.residual) +
      (work (alloc (vectorWrite rows.2 P.residual).value.2 [.bit false]) + 6))) ≤ _
  nlinarith only [ha, hr, hv, he, hm]

set_option maxHeartbeats 1000000 in
theorem prepareInput_work (I : RawInput) (J : Input) (hj : decodeRaw I = some J) :
    work (prepareInput J) ≤ 1000000 * ((encodeInput I).length + 1) ^ 4 * (states J) ^ 3 := by
  have hfields := decodeRaw_fields I J hj
  have hn := (prepared_widths I J hj).1
  have hnorm := normalizeCost_work_input I J.parents J.H hfields.2.2.1
  have hpre := preprocessing_steps I J hj
  have hfees := scaleFeesCost_allocations J.numerators J.denominators J.budgetDenominator
  have hbudget := scaleBudgetCost_allocations J.denominators J.budgetNumerator
  have hcand := candidateCost_work_input_poly I (decodeRaw_shape I J hj) J.parents J.valid
    J.H (normalizeCost J.parents J.H).value
    (scaleFeesCost J.numerators J.denominators J.budgetDenominator).value
    (scaleBudgetCost J.denominators J.budgetNumerator).value hfields.2.2.1 (normalized_le J)
    (by rw [scaleFeesCost_value _ _ _ J.positive]; exact scaled_fee_width I J hj)
    (by rw [scaleBudgetCost_value _ _ _ J.budgetPositive]; exact scaled_budget_width I J hj)
  have hcount := rootCountCost_work_input I (decodeRaw_shape I J hj) J.parents J.H
    (normalizeCost J.parents J.H).value hfields.2.2.1 (normalized_le J)
  have hnorm' : work (normalizeCost J.parents J.H) ≤ 128 * ((encodeInput I).length + 1) ^ 2 :=
    hnorm.trans (by nlinarith only [Nat.mul_le_mul_right ((encodeInput I).length + 1) (Nat.add_le_add_right hn 1)])
  have hcount' : work (rootCountCost J.parents (normalizeCost J.parents J.H).value) ≤
      1024 * ((encodeInput I).length + 1) ^ 2 := by
    have hm := Nat.mul_le_mul_right (2 * (encodeInput I).length + 1) (Nat.add_le_add_right hn 1)
    nlinarith only [hcount, hm]
  have hcand' : work (candidateCost J.parents (normalizeCost J.parents J.H).value
      (scaleFeesCost J.numerators J.denominators J.budgetDenominator).value
      (scaleBudgetCost J.denominators J.budgetNumerator).value) ≤
      310000 * ((encodeInput I).length + 1) ^ 3 * states J := by
    simpa only [states, normalizeCost_value J.parents J.valid J.H, TreeBudgetVector.decode_normalize] using hcand
  have hS := states_positive J
  have hS3 : 1 ≤ (states J) ^ 3 := one_le_pow₀ hS
  have hSle : states J ≤ (states J) ^ 3 := by simpa only [pow_one] using Nat.pow_le_pow_right hS (show 1 ≤ 3 by omega)
  have h2 : ((encodeInput I).length + 1) ^ 2 ≤ ((encodeInput I).length + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : ((encodeInput I).length + 1) ^ 3 ≤ ((encodeInput I).length + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm2 := Nat.mul_le_mul h2 hS3
  have hm3 := Nat.mul_le_mul h3 hSle
  have hm4 := Nat.mul_le_mul_left (((encodeInput I).length + 1) ^ 4) hS3
  dsimp only [prepareInput, work] at hnorm' hcount' hcand' ⊢
  nlinarith only [hnorm', hcount', hcand', hpre, hfees, hbudget, hm2, hm3, hm4]

end UAVProof.TreeBudgetStoredPreparationWork
