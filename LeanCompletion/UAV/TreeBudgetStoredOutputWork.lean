import LeanCompletion.UAV.TreeBudgetStoredSearchWork
import LeanCompletion.UAV.TreeBudgetStoredOutput
import LeanCompletion.UAV.TreeBudgetBinaryOutputBounds

namespace UAVProof.TreeBudgetStoredOutputWork
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetCostedCandidates TreeBudgetAllocationBounds TreeBudgetSharedAnswerStore
open TreeBudgetChargedCache TreeBudgetStoredSearch TreeBudgetStoredOutput TreeBudgetStoredCursor
open TreeBudgetStoredWork TreeBudgetStoredReadWork TreeBudgetStoredNodeWork TreeBudgetBinaryCodec
open TreeBudgetStoredPayloadWork TreeBudgetSearchStore

theorem rowRead_work (heap : Heap) (a : ℕ) (row : List ℕ) (B W : ℕ)
    (hh : WellFormed heap) (hr : RowRep heap a row)
    (hb : (encodeNats row).length ≤ B) (hW : 1 ≤ W) (hw : (heap.size + 1).size ≤ W) :
    work (rowRead heap a) ≤ 8192 * (B + 1) ^ 2 * (W + 2) := by
  have hblob := blobRead_work heap a (encodeNats row) W hh hr hW hw
  have hparse := parseNatsD_steps (encodeNats row)
  have haparse := parseNatsD_allocations_le_steps (encodeNats row)
  have hp : (parseNatsD (encodeNats row)).value = some (row, []) := by
    simpa using parseNats_append row []
  have hlen := Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2
  have hlin := Nat.mul_le_mul_right (W + 2) (Nat.add_le_add_right hb 1)
  have hpow : B + 1 ≤ (B + 1) ^ 2 := by nlinarith only [Nat.zero_le B]
  have hm := Nat.mul_le_mul_right (W + 2) hpow
  have hprod : (B + 1) ^ 2 ≤ (B + 1) ^ 2 * (W + 2) := Nat.le_mul_of_pos_right _ (by omega)
  rw [rowRead, work_then_some _ _ _ (blobRead_correct _ _ _ hh hr), work_then_some _ _ _ hp]
  simp only [work_ret]
  unfold work at hblob ⊢
  nlinarith only [hblob, hparse, haparse, hlen, hlin, hm, hprod]

set_option maxHeartbeats 1000000 in
theorem rowsRead_work (heap : Heap) (a : ℕ) (rows : Matrix) (fuel B W : ℕ)
    (hh : WellFormed heap) (hr : RowsRep heap a rows) (hf : a < fuel)
    (hb : ∀ row ∈ rows, (encodeNats row).length ≤ B)
    (hW : 1 ≤ W) (hfw : fuel.size ≤ W) (hw : (heap.size + 4).size ≤ W) :
    work (rowsRead fuel heap a) ≤ 16384 * (B + 1) ^ 2 * (W + 2) * (rows.length + 1) := by
  have hp : 1 ≤ (B + 1) ^ 2 := one_le_pow₀ (by omega)
  have hm := Nat.mul_le_mul_right (W + 2) hp
  induction hr generalizing fuel with
  | nil a header =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha := rowsRep_address_lt (RowsRep.nil a header)
      have hhead := rowsHead_work heap a W ((Nat.size_le_size (by omega)).trans hw)
      have hcur := cursor_work (fuel + 1) W hfw hW
      rw [rowsRead, work_then_some _ _ _ (cursorStep_succ fuel),
        work_then_some _ _ _ (rowsHead_nil _ _ hh header)]
      simp only [work_ret, List.length_nil, Nat.zero_add, Nat.mul_one]
      nlinarith only [hhead, hcur, hm]
  | cons a row tail p ps header hp hps hl ht ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha := rowsRep_address_lt (RowsRep.cons a row tail p ps header hp hps hl ht)
      have hhead := rowsHead_work heap a W ((Nat.size_le_size (by omega)).trans hw)
      have hcur := cursor_work (fuel + 1) W hfw hW
      have hrw := rowRead_work heap row p B W hh hp (hb p (by simp)) hW
        ((Nat.size_le_size (by omega)).trans hw)
      have htail := ih fuel (by omega) (fun p hp => hb p (by simp [hp]))
        ((Nat.size_le_size (Nat.le_succ fuel)).trans hfw)
      rw [rowsRead, work_then_some _ _ _ (cursorStep_succ fuel),
        work_then_some _ _ _ (rowsHead_cons _ _ _ _ hh header),
        work_then_some _ _ _ (rowRead_correct _ _ _ hh hp),
        work_then_some _ _ _ (rowsRead_correct heap tail ps hh hps fuel (by omega))]
      simp only [work_charge, work_ret, List.length_cons]
      nlinarith only [hhead, hcur, hrw, htail, hm]

theorem answerRead_work (heap : Heap) (a : ℕ) (ans : WireAnswer) (m B W : ℕ)
    (hh : WellFormed heap) (hr : SharedAnswerRep heap a ans)
    (hl : ∀ rows, ans = some rows → rows.length ≤ m)
    (hb : ∀ rows, ans = some rows → ∀ row ∈ rows, (encodeNats row).length ≤ B)
    (hW : 1 ≤ W) (hw : (heap.size + 4).size ≤ W) :
    work (answerRead heap a) ≤ 32768 * (B + 1) ^ 2 * (W + 2) * (m + 1) := by
  have ha := answerRep_address_lt hr
  have hhead := answerHead_work heap a W ((Nat.size_le_size (by omega)).trans hw)
  have hp : 1 ≤ (B + 1) ^ 2 := one_le_pow₀ (by omega)
  have hm := Nat.mul_le_mul_right (W + 2) hp
  have hp' : (B + 1) ^ 2 * (W + 2) ≤ (B + 1) ^ 2 * (W + 2) * (m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  cases ans with
  | none =>
    rw [answerRead, work_then_some _ _ _ (answerHead_failure _ _ hh hr)]
    simp only [work_ret]
    nlinarith only [hhead, hm, hp']
  | some rows =>
    obtain ⟨r, hread, hrows⟩ := answerHead_success _ _ _ hh hr
    have hbnd := rowsRep_address_lt hrows
    have hw' : (heap.size + 1).size ≤ W := (Nat.size_le_size (by omega)).trans hw
    have hc := rowsRead_work heap r rows (heap.size + 1) B W hh hrows (by omega) (hb rows rfl) hW hw' hw
    have hfuel := (arithmetic_work heap.size 1 W
      ((Nat.size_le_size (by omega)).trans hw) (by simpa using hW)).2.2
    have hm' := Nat.mul_le_mul_left (16384 * (B + 1) ^ 2 * (W + 2)) (Nat.add_le_add_right (hl rows rfl) 1)
    rw [answerRead, work_then_some _ _ _ hread, work_bind, addNatD_value,
      work_then_some _ _ _ (rowsRead_correct heap r rows hh hrows _ (by omega))]
    simp only [work_charge, work_ret]
    nlinarith only [hhead, hc, hfuel, hm', hm, hp']

set_option maxHeartbeats 1000000 in
theorem emitStored_work (heap : Heap) (a : ℕ) (ans : WireAnswer) (m B W : ℕ)
    (hh : WellFormed heap) (hr : SharedAnswerRep heap a ans)
    (hl : ∀ rows, ans = some rows → rows.length ≤ m)
    (hb : ∀ rows, ans = some rows → ∀ row ∈ rows,
      (encodeNats row).length ≤ B ∧ row.length ≤ B ∧ ∀ x ∈ row, x.size ≤ B)
    (hW : 1 ≤ W) (hw : (heap.size + 4).size ≤ W) :
    work (emitStored heap a) ≤ 65536 * (B + 1) ^ 3 * (W + 2) * (m + 1) ^ 2 := by
  have hread := answerRead_work heap a ans m B W hh hr hl (fun rows hr row hp => (hb rows hr row hp).1) hW hw
  have hp : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : m + 1 ≤ (m + 1) ^ 2 := by nlinarith only [Nat.zero_le m]
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul_right (W + 2) hp) hm
  have h1 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by omega)
  have h2 : 1 ≤ (m + 1) ^ 2 := one_le_pow₀ (by omega)
  have hpos : 1 ≤ (B + 1) ^ 3 * (W + 2) * (m + 1) ^ 2 := by
    have := Nat.mul_le_mul h1 h2
    nlinarith only [this, Nat.zero_le ((B + 1) ^ 3 * W * (m + 1) ^ 2)]
  rw [emitStored, work_then_some _ _ _ (answerRead_correct _ _ _ hh hr)]
  cases ans with
  | none => simp only [work_ret]; nlinarith only [hread, hprod, hpos]
  | some rows =>
    have hs := encodeMatrixD_steps rows m B B (hl rows rfl)
      (fun row hp => (hb rows rfl row hp).2.1) (fun row hp => (hb rows rfl row hp).2.2)
    have ha := encodeMatrixD_allocations_le_steps rows
    have hlin : B + 1 ≤ (B + 1) ^ 2 := by nlinarith only [Nat.zero_le B]
    have hinner : 512 * (B + 1) ^ 2 * (B + 1) + 8 * (B + 1) * (B + 1) + 3 ≤
        523 * (B + 1) ^ 3 := by nlinarith only [hp, h1]
    have hc := Nat.mul_le_mul hm hinner
    have hn := Nat.mul_le_mul_right ((m + 1) ^ 2) h1
    have hw' : (B + 1) ^ 3 * (m + 1) ^ 2 ≤ (B + 1) ^ 3 * (W + 2) * (m + 1) ^ 2 := by
      exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
    simp only [work_bind, work_charge, work_ret]
    unfold work at hread ⊢
    nlinarith only [hread, hs, ha, hprod, hpos, hc, hn, hw']

end UAVProof.TreeBudgetStoredOutputWork
