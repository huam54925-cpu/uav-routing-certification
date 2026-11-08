import LeanCompletion.UAV.TreeBudgetStoredPreparation

/-! Actual heap footprints of the addressed constructors and initialization.
These are slot counts, distinct from `Costed.allocations`, which also includes
codec and arithmetic workspace. No capacity assumption is used. -/
namespace UAVProof.TreeBudgetStoredAllocation
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec
open TreeBudgetAllocationBounds TreeBudgetTypedStore TreeBudgetSearchStore
open TreeBudgetSharedAnswerStore TreeBudgetChargedCache TreeBudgetStoredSearch
open TreeBudgetStoredPreparation TreeBudgetBinaryCodec

def rowSlots {n : ℕ} (v : Vector ℕ n) : ℕ := 2 * (encodeNats v.toList).length + 1
def keySlots {n : ℕ} (k : ℕ) (v : Vector ℕ n) : ℕ :=
  2 * (encodeKey (k, v.toList)).length + 1

theorem alloc_size (heap : Heap) (slots : List Slot)
    (href : ∀ a, Slot.ref a ∈ slots → a < heap.size) :
    (alloc heap slots).value.2.size = heap.size + slots.length := by
  rw [alloc_value heap slots href]
  exact allocateBlock_size heap slots

theorem alloc_heap_le_allocations (heap : Heap) (slots : List Slot)
    (href : ∀ a, Slot.ref a ∈ slots → a < heap.size) :
    (alloc heap slots).value.2.size ≤ heap.size + (alloc heap slots).allocations := by
  rw [alloc_size heap slots href]
  simp only [alloc, nodeD_allocations]
  omega

theorem vectorWrite_size {n : ℕ} (heap : Heap) (v : Vector ℕ n) :
    (vectorWrite heap v).value.2.size = heap.size + rowSlots v := by
  rw [vectorWrite_value]
  simp [allocateBlob, allocateBlock_size, blobSlots_length, rowSlots]

theorem keyWrite_size {n : ℕ} (heap : Heap) (k : ℕ) (v : Vector ℕ n) :
    (keyWrite heap k v).value.2.size = heap.size + keySlots k v := by
  rw [keyWrite_value]
  simp [allocateBlob, allocateBlock_size, blobSlots_length, keySlots]

theorem vectorWrite_heap_le_allocations {n : ℕ} (heap : Heap) (v : Vector ℕ n) :
    (vectorWrite heap v).value.2.size ≤ heap.size + (vectorWrite heap v).allocations := by
  have h := alloc_heap_le_allocations heap (blobSlots (encodeNats v.toList)) (by simp [blobSlots])
  rw [alloc_size heap _ (by simp [blobSlots])] at h
  rw [vectorWrite_size]
  simp only [vectorWrite, TreeBudgetBitMachine.bind, encodeNatsD_value, blobWrite]
  rw [blobSlots_length] at h
  dsimp [rowSlots]
  omega

theorem rowsWrite_size {n : ℕ} (heap : Heap) (ps : List (Vector ℕ n))
    (hh : WellFormed heap) :
    (rowsWrite heap ps).value.2.size =
      heap.size + 1 + (ps.map fun p => rowSlots p + 3).sum := by
  induction ps generalizing heap with
  | nil => simp [rowsWrite, alloc_value heap [.bit false] (by simp), allocateBlock_size]
  | cons p ps ih =>
    let tail := (rowsWrite heap ps).value
    obtain ⟨ht, hw, he⟩ := rowsWrite_correct heap ps hh
    let row := (vectorWrite tail.2 p).value
    have hr : RowRep row.2 row.1 p.toList := by
      dsimp [row]; rw [vectorWrite_value]; exact allocateBlob_correct _ _
    have he' : Extends tail.2 row.2 := by
      dsimp [row]; rw [vectorWrite_value]; exact allocateBlock_extends ..
    have hbrow := blobRep_address_lt _ _ _ hr
    have hbtail := rowsRep_address_lt (rowsRep_persist he' _ _ ht)
    have href : ∀ a, Slot.ref a ∈ [.bit true, .ref row.1, .ref tail.1] → a < row.2.size := by
      intro a ha
      simp at ha
      rcases ha with rfl | rfl <;> assumption
    have hs := alloc_size row.2 [.bit true, .ref row.1, .ref tail.1] href
    have hv := vectorWrite_size tail.2 p
    have hi := ih heap hh
    simp only [rowsWrite, costBind_value, charge, List.map_cons, List.sum_cons]
    change (alloc row.2 [.bit true, .ref row.1, .ref tail.1]).value.2.size = _
    rw [hs]
    change row.2.size = tail.2.size + rowSlots p at hv
    change tail.2.size = _ at hi
    simp only [List.length_cons, List.length_nil]
    omega

theorem initializeStore_size {n : ℕ} (P : Prepared n) :
    (initializeStore P).value.heap.size =
      3 + rowSlots P.residual + (P.candidates.map fun p => rowSlots p + 3).sum := by
  have hw : WellFormed (allocateBlock #[] [.bit false]) := by
    apply wellFormed_allocateBlock
    · simp [WellFormed, TreeBudgetAllocationBounds.read]
    · simp
  have hs := rowsWrite_size (allocateBlock #[] [.bit false]) P.candidates hw
  simp only [initializeStore, costBind_value, alloc_value #[] [.bit false] (by simp),
    alloc_value _ [.bit false] (by simp), allocateBlock_size] at *
  simp only [List.length_cons, List.length_nil, Array.size_empty] at *
  rw [vectorWrite_size]
  omega

/-- Every retained cache node allocates exactly four cells. The old nodes stay
in the append-only heap; no live-cache bound is substituted for this count. -/
theorem insert_heap_growth (heap : Heap) (a key answer : ℕ) (cs : WireCache)
    (q : WireKey) (ans : WireAnswer) (hh : WellFormed heap)
    (hc : TreeBudgetChargedCache.CacheRep heap a cs) (hk : KeyRep heap key q)
    (hv : SharedAnswerRep heap answer ans) :
    ∃ root after, (insertD heap a key answer).value = some ((root, after), cs.length) ∧
      after.size ≤ heap.size + 4 * cs.length + 4 := by
  obtain ⟨root, after, ho, _, _, _, hs⟩ := insertD_correct heap a key answer cs q ans hh hc hk hv
  refine ⟨root, after, ho, ?_⟩
  have hl : (keep cs q).length ≤ cs.length := List.length_filter_le ..
  omega

/-- Any represented object present in an earlier heap remains within the final
capacity. This applies to retained and obsolete nodes alike. -/
theorem prefix_capacity {earlier final : Heap} (he : Extends earlier final) :
    earlier.size ≤ final.size ∧ ∀ address, address < earlier.size → address < final.size :=
  ⟨he.size_le, fun _ ha => ha.trans_le he.size_le⟩

theorem prefix_address_width {earlier final : Heap} (he : Extends earlier final)
    (address : ℕ) (ha : address < earlier.size) :
    (widthNat address).value ≤ final.size.size := by
  rw [(widthNat_spec address).1]
  exact Nat.size_le_size (ha.le.trans he.size_le)

/-- Allocation measures the new endpoint, not merely the old allocation base. -/
theorem allocation_endpoint_width (heap : Heap) (slots : List Slot)
    (href : ∀ a, Slot.ref a ∈ slots → a < heap.size) :
    (widthNat (addNatD heap.size (lengthD slots).value).value).value =
      (alloc heap slots).value.2.size.size := by
  rw [lengthD_value, addNatD_value, (widthNat_spec _).1, alloc_size heap slots href]

end UAVProof.TreeBudgetStoredAllocation
