import LeanCompletion.UAV.TreeBudgetStoredNodeWork

namespace UAVProof.TreeBudgetStoredPayloadWork
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetCostedCandidates TreeBudgetAllocationBounds TreeBudgetSharedAnswerStore
open TreeBudgetChargedCache TreeBudgetStoredWork TreeBudgetStoredReadWork TreeBudgetStoredSearch
open TreeBudgetBinaryCodec TreeBudgetSearchStore TreeBudgetStoredAllocation

theorem natsEncode_allocations_le_steps (xs : List ℕ) :
    (encodeNatsD xs).allocations ≤ (encodeNatsD xs).steps :=
  encodeListD_allocations_le_steps encodeNatD xs (fun x _ => encodeNatD_allocations_le_steps x)

theorem vectorRead_work {n : ℕ} (heap : Heap) (a : ℕ) (v : Vector ℕ n) (B W : ℕ)
    (hh : WellFormed heap) (hr : RowRep heap a v.toList)
    (hn : n ≤ B) (hb : (encodeNats v.toList).length ≤ B)
    (hW : 1 ≤ W) (hw : (heap.size + 1).size ≤ W) :
    work (vectorRead n heap a) ≤ 16384 * (B + 1) ^ 2 * (W + 2) := by
  have hblob := blobRead_work heap a (encodeNats v.toList) W hh hr hW hw
  have hparse := parseNatsD_steps (encodeNats v.toList)
  have haparse := parseNatsD_allocations_le_steps (encodeNats v.toList)
  have hlen := lengthD_steps v.toList
  have halen := lengthD_allocations_le_steps v.toList
  have heq := (arithmetic_work n n B
    ((TreeBudgetAllocationBounds.size_le_self n).trans hn)
    ((TreeBudgetAllocationBounds.size_le_self n).trans hn)).1
  have hp : (parseNatsD (encodeNats v.toList)).value = some (v.toList, []) := by
    simpa using parseNats_append v.toList []
  have hm₁ := Nat.mul_le_mul_right (W + 2) (Nat.add_le_add_right hb 1)
  have hm₂ := Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2
  have hm₃ := Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2
  have hprod : (B + 1) ^ 2 ≤ (B + 1) ^ 2 * (W + 2) := Nat.le_mul_of_pos_right _ (by omega)
  have hlin : B + 1 ≤ (B + 1) ^ 2 := by nlinarith [Nat.zero_le B]
  unfold vectorRead
  rw [work_then_some _ _ _ (blobRead_correct _ _ _ hh hr), work_then_some _ _ _ hp]
  simp only [lengthD_value, Vector.length_toList, eqNatD_value, decide_true, ↓reduceDIte]
  simp only [work, Vector.length_toList] at hblob hlen halen heq ⊢
  nlinarith only [hblob, hparse, haparse, hlen, halen, heq, hm₁, hm₂, hm₃, hprod, hlin, hn]

theorem blobWrite_work (heap : Heap) (bits : Bits) (B W : ℕ)
    (hb : bits.length ≤ B) (hw : (heap.size + (blobSlots bits).length).size ≤ W) :
    work (blobWrite heap bits) ≤ 4096 * (B + 1) ^ 2 * (W + 2) := by
  have hs := alloc_work heap (blobSlots bits) W hw
  have hl := lengthD_steps bits
  have ha := lengthD_allocations_le_steps bits
  have hm := Nat.mul_le_mul_right (W + 2) (Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2)
  have hprod : (bits.length + 1) ^ 2 ≤ (bits.length + 1) ^ 2 * (W + 2) :=
    Nat.le_mul_of_pos_right _ (by omega)
  simp only [blobWrite, work, lengthD_value, blobSlots_length] at hs ⊢
  nlinarith only [hs, hl, ha, hm, hprod, Nat.zero_le bits.length]

theorem vectorWrite_work {n : ℕ} (heap : Heap) (v : Vector ℕ n) (B W : ℕ)
    (hn : n ≤ B) (hv : ∀ i : Fin n, v[i].size ≤ B)
    (hb : (encodeNats v.toList).length ≤ B) (hw : (heap.size + rowSlots v).size ≤ W) :
    work (vectorWrite heap v) ≤ 8192 * (B + 1) ^ 3 * (W + 2) := by
  have hv' : ∀ x ∈ v.toList, x.size ≤ B := by
    intro x hx
    obtain ⟨i, hi, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    subst x
    exact hv ⟨i, hi⟩
  have hs := encodeNatsD_steps v.toList B B (by simpa using hn) hv'
  have ha := natsEncode_allocations_le_steps v.toList
  have hb' := blobWrite_work heap (encodeNats v.toList) B W hb (by
    simpa [blobSlots_length, rowSlots] using hw)
  have hpow : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm := Nat.mul_le_mul_right (W + 2) hpow
  have hprod : (B + 1) ^ 3 ≤ (B + 1) ^ 3 * (W + 2) := Nat.le_mul_of_pos_right _ (by omega)
  simp only [vectorWrite, work_bind, encodeNatsD_value]
  unfold work at hb' ⊢
  nlinarith only [hs, ha, hb', hm, hprod]

theorem keyWrite_work {n : ℕ} (heap : Heap) (k : ℕ) (v : Vector ℕ n) (B W : ℕ)
    (hn : n ≤ B) (hk : k.size ≤ B) (hv : ∀ i : Fin n, v[i].size ≤ B)
    (hb : (encodeKey (k, v.toList)).length ≤ B)
    (hw : (heap.size + keySlots k v).size ≤ W) :
    work (keyWrite heap k v) ≤ 16384 * (B + 1) ^ 3 * (W + 2) := by
  have hv' : ∀ x ∈ v.toList, x.size ≤ B := by
    intro x hx
    obtain ⟨i, hi, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    subst x
    exact hv ⟨i, hi⟩
  have hs := encodeNatsD_steps v.toList B B (by simpa using hn) hv'
  have ha := natsEncode_allocations_le_steps v.toList
  have hcount := encodeNatD_steps k
  have hacount := encodeNatD_allocations_le_steps k
  have hb' := blobWrite_work heap (encodeKey (k, v.toList)) B W hb (by
    simpa [blobSlots_length, keySlots] using hw)
  have hpow : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hlin : B + 1 ≤ (B + 1) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ B + 1 by omega) (show 1 ≤ 3 by omega)
  have hm := Nat.mul_le_mul_right (W + 2) hpow
  have hprod : (B + 1) ^ 3 ≤ (B + 1) ^ 3 * (W + 2) := Nat.le_mul_of_pos_right _ (by omega)
  simp only [keyWrite, work_bind, encodeNatD_value, encodeNatsD_value, appendD_value]
  change work (encodeNatD k) + (work (encodeNatsD v.toList) +
    (work (appendD (encodeNat k) (encodeNats v.toList)) + work (blobWrite heap (encodeKey (k, v.toList))))) ≤ _
  simp only [work, appendD_steps, appendD_allocations, encodeNat_length] at hb' ⊢
  nlinarith only [hs, ha, hcount, hacount, hb', hm, hprod, hlin, hk]

end UAVProof.TreeBudgetStoredPayloadWork
