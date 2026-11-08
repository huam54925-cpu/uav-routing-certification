import LeanCompletion.UAV.TreeBudgetStoredWork

namespace UAVProof.TreeBudgetStoredReadWork
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetCostedCandidates TreeBudgetAllocationBounds TreeBudgetAddressedBlocks
open TreeBudgetSharedAnswerStore TreeBudgetChargedCache TreeBudgetStoredCursor
open TreeBudgetStoredWork TreeBudgetBinaryCodec TreeBudgetSearchStore TreeBudgetTypedStore

theorem lengthRead_work (heap : Heap) (a k fuel W : ℕ)
    (hh : WellFormed heap) (hk : k < fuel) (hW : 1 ≤ W)
    (hfw : fuel.size ≤ W) (haw : (a + k + 1).size ≤ W)
    (ht : ∀ i < k, read heap (a + i) = some (.bit true))
    (hf : read heap (a + k) = some (.bit false)) :
    work (lengthRead fuel heap a) ≤ 512 * (k + 1) * (W + 1) := by
  induction k generalizing a fuel with
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hload : (load heap a).value = some (.bit false) := by
        rw [load_value _ _ hh]; simpa using hf
      have hc := cursor_work (fuel + 1) W hfw hW
      have hl := load_work heap a W ((Nat.size_le_size (by omega : a ≤ a + 0 + 1)).trans haw)
      have ha := (arithmetic_work a 1 W
        ((Nat.size_le_size (by omega : a ≤ a + 0 + 1)).trans haw) (by simpa using hW)).2.2
      rw [lengthRead, work_then_some _ _ _ (cursorStep_succ fuel)]
      rw [work_then_some _ _ _ hload]
      simp only [work_bind, work_ret]
      nlinarith only [hc, hl, ha]
  | succ k ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hload : (load heap a).value = some (.bit true) := by
        rw [load_value _ _ hh]; simpa using ht 0 (by omega)
      have ht' : ∀ i < k, read heap (a + 1 + i) = some (.bit true) := by
        intro i hi
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht (i + 1) (by omega)
      have hf' : read heap (a + 1 + k) = some (.bit false) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf
      have hfw' := (Nat.size_le_size (Nat.le_succ fuel)).trans hfw
      have haw' : (a + 1 + k + 1).size ≤ W := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using haw
      have hi := ih (a + 1) fuel (by omega) hfw' haw' ht' hf'
      have hrec : (lengthRead fuel heap (a + 1)).value = some (k, a + 1 + k + 1) := by
        rw [lengthRead_value _ _ _ hh]
        exact readLength_correct heap (a + 1) k fuel (by omega) ht' hf'
      have hc := cursor_work (fuel + 1) W hfw hW
      have hl := load_work heap a W ((Nat.size_le_size (by omega : a ≤ a + (k + 1) + 1)).trans haw)
      have ha := (arithmetic_work a 1 W
        ((Nat.size_le_size (by omega : a ≤ a + (k + 1) + 1)).trans haw) (by simpa using hW)).2.2
      have hlen := (arithmetic_work k 1 W
        ((Nat.size_le_size (by omega : k ≤ fuel + 1)).trans hfw) (by simpa using hW)).2.2
      rw [lengthRead, work_then_some _ _ _ (cursorStep_succ fuel)]
      rw [work_then_some _ _ _ hload]
      simp only [work_bind, addNatD_value]
      rw [work_then_some _ _ _ hrec]
      simp only [work_bind, work_charge, work_ret]
      nlinarith only [hi, hc, hl, ha, hlen]

theorem readWord_work_endpoint (heap : Heap) (b : Block) (bits : Bits) (width : ℕ)
    (hh : WellFormed heap) (hr : WordRep heap b bits)
    (hfit : b.base + b.length ≤ 2 ^ width) :
    work (readWordD width heap b) ≤ 1024 * (b.length + 1) * (width + 2) := by
  have hb := readBlockD_steps width heap b.base b.length hfit
  have hd := decodeWordD_steps (bits.map Slot.bit)
  have hl : b.length = bits.length := by simpa using hr.2.1
  have hv : (readBlockD width heap b.base b.length).value = some (bits.map Slot.bit) := by
    rw [readBlockD_value _ _ _ _ hh hfit]
    have hs := readSlots_correct heap b.base (bits.map Slot.bit) hr.2.2
    simpa [List.length_map, hl] using hs
  have ha := readWordD_allocations_le_steps width heap b
  have hs : (readWordD width heap b).steps ≤ 512 * (b.length + 1) * (width + 2) := by
    simp only [readWordD, hv]
    simp only [List.length_map] at hd
    nlinarith only [hb, hd, hl]
  unfold work
  nlinarith only [hs, ha]

theorem blobRead_work (heap : Heap) (a : ℕ) (bits : Bits) (W : ℕ)
    (hh : WellFormed heap) (hr : BlobRep heap a bits)
    (hW : 1 ≤ W) (hw : (heap.size + 1).size ≤ W) :
    work (blobRead heap a) ≤ 4096 * (bits.length + 1) * (W + 2) := by
  have hsize : a + (2 * bits.length + 1) ≤ heap.size := hr.1
  have ht : ∀ i < bits.length, read heap (a + i) = some (.bit true) := by
    intro i hi
    have hread := hr.2.2 i (by rw [blobSlots_length]; omega)
    simpa [blobSlots, List.getElem_append_left hi, hi] using hread
  have hf : read heap (a + bits.length) = some (.bit false) := by
    have hread := hr.2.2 bits.length (by rw [blobSlots_length]; omega)
    simpa [blobSlots] using hread
  have hlength : (lengthRead (heap.size + 1) heap a).value =
      some (bits.length, a + bits.length + 1) := by
    rw [lengthRead_value _ _ _ hh]
    exact readLength_correct heap a bits.length (heap.size + 1) (by omega) ht hf
  have hword : WordRep heap ⟨a + bits.length + 1, bits.length⟩ bits := by
    refine ⟨by simp; omega, by simp, ?_⟩
    intro i hi
    have hii : i < bits.length := by simpa using hi
    have hread := hr.2.2 (bits.length + 1 + i) (by rw [blobSlots_length]; omega)
    simp only [blobSlots] at hread
    rw [List.getElem_append_right (by simp; omega)] at hread
    simp only [List.length_replicate] at hread
    have hindex : bits.length + (1 + i) - bits.length = i + 1 := by omega
    simpa only [Nat.add_assoc, hindex, List.getElem_cons_succ, List.getElem_map] using hread
  have hwidth : ∀ x, x ≤ heap.size + 1 → x.size ≤ W :=
    fun x hx => (Nat.size_le_size hx).trans hw
  have hinit := (arithmetic_work heap.size 1 W (hwidth _ (by omega)) (by simpa using hW)).2.2
  have hlen := lengthRead_work heap a bits.length (heap.size + 1) W hh (by omega) hW hw
    (hwidth _ (by omega)) ht hf
  let top := a + bits.length + 1 + bits.length
  have htop : top.size ≤ W := hwidth _ (by dsimp [top]; omega)
  have hadd := (arithmetic_work (a + bits.length + 1) bits.length W
    (hwidth _ (by omega)) (hwidth _ (by omega))).2.2
  have hdata := readWord_work_endpoint heap _ bits top.size hh hword (Nat.lt_size_self top).le
  have hm := Nat.mul_le_mul_left (1024 * (bits.length + 1)) (Nat.add_le_add_right htop 2)
  unfold blobRead
  rw [work_bind, addNatD_value, work_then_some _ _ _ hlength]
  simp only [work, addNatD_value, (widthNat_spec _).1, (widthNat_spec _).2.1,
    (widthNat_spec _).2.2] at hinit hlen hadd hdata ⊢
  change _ ≤ 4096 * (bits.length + 1) * (W + 2)
  dsimp only [top] at htop hm hdata
  nlinarith only [hinit, hlen, hadd, hdata, hm, htop]

end UAVProof.TreeBudgetStoredReadWork
