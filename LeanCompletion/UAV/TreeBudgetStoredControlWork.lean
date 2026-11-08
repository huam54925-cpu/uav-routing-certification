import LeanCompletion.UAV.TreeBudgetStoredWorkInvariant

namespace UAVProof.TreeBudgetStoredControlWork
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetCostedCandidates TreeBudgetAllocationBounds TreeBudgetSharedAnswerStore
open TreeBudgetChargedCache TreeBudgetStoredWork TreeBudgetStoredReadWork TreeBudgetStoredNodeWork
open TreeBudgetStoredPayloadWork TreeBudgetStoredCacheWork TreeBudgetStoredWorkInvariant
open TreeBudgetStoredSearch TreeBudgetBinaryCodec TreeBudgetSearchStore TreeBudgetStoredAllocation
open TreeBudgetCostedSearchBounds TreeBudgetVectorMemoState TreeBudgetSearchStats

theorem capacity_local (B : ℕ) (before final : Heap) (he : before.size ≤ final.size)
    (a : ℕ) (ha : a ≤ 5 * before.size + B + 6) : a.size ≤ addressWidth B final := by
  apply addressWidth_bound
  dsimp [capacity]
  omega

theorem failResult_work (heap : Heap) (cache W : ℕ) (hw : (heap.size + 1).size ≤ W) :
    work (failResult heap cache) ≤ 4096 * (W + 2) := by
  have h := alloc_work heap [.bit false] W (by simpa using hw)
  simp only [failResult, work_bind, work_ret]
  simp only [List.length_cons, List.length_nil] at h
  norm_num only at h
  omega

theorem prependResult_work (heap : Heap) (row rows cache W : ℕ) (events : Counts)
    (hr : row < heap.size) (ht : rows < heap.size) (hw : (heap.size + 5).size ≤ W) :
    work (prependResult heap row rows cache events) ≤ 16384 * (W + 2) := by
  have href : ∀ a, Slot.ref a ∈ [.bit true, .ref row, .ref rows] → a < heap.size := by
    intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption
  have h₁ := alloc_work heap [.bit true, .ref row, .ref rows] W
    ((Nat.size_le_size (by simp <;> omega)).trans hw)
  have h₂ := alloc_work (allocateBlock heap [.bit true, .ref row, .ref rows])
    [.bit true, .ref heap.size] W (by simpa [allocateBlock_size, Nat.add_assoc] using hw)
  simp only [prependResult, work_bind, alloc_value heap _ href, work_ret]
  simp only [List.length_cons, List.length_nil] at h₁ h₂
  norm_num only at h₁ h₂
  omega

theorem zeroResult_work {n : ℕ} (heap : Heap) (residual cache B W : ℕ) (r : Vector ℕ n)
    (hh : WellFormed heap) (hr : RowRep heap residual r.toList)
    (hn : n ≤ B) (hrw : ∀ i : Fin n, r[i].size ≤ B)
    (hb : (encodeNats r.toList).length ≤ B) (hW : 1 ≤ W) (hw : (heap.size + 3).size ≤ W) :
    work (zeroResult n heap residual cache) ≤ 65536 * (B + 1) ^ 3 * (W + 2) := by
  have hread := vectorRead_work heap residual r B W hh hr hn hb hW
    ((Nat.size_le_size (by omega)).trans hw)
  have hz := zeroV_steps r B hrw
  have haz := (TreeBudgetBitPrimitives.vector_allocations_le_steps r r).2.2.2
  have h₁ := alloc_work heap [.bit false] W ((Nat.size_le_size (by simp <;> omega)).trans hw)
  have h₂ := alloc_work (allocateBlock heap [.bit false]) [.bit true, .ref heap.size] W
    (by simpa [allocateBlock_size, Nat.add_assoc] using hw)
  have hfail := failResult_work heap cache W ((Nat.size_le_size (by omega)).trans hw)
  have hp : (B + 1) ^ 2 ≤ (B + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm := Nat.mul_le_mul_right (W + 2) hp
  have hpos : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by omega)
  have hwprod := Nat.mul_le_mul_right (W + 2) hpos
  have hp' : (B + 1) ^ 2 ≤ (B + 1) ^ 3 * (W + 2) :=
    hp.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hdim := Nat.mul_le_mul_right (B + 1) (Nat.add_le_add_right hn 1)
  unfold zeroResult
  rw [work_then_some _ _ _ (vectorRead_correct _ _ _ hh hr), work_bind]
  simp only [zeroV_value]
  by_cases he : TreeBudgetVector.isZero r = true
  · simp only [he, ↓reduceIte, work_bind, alloc_value heap [.bit false] (by simp), work_ret]
    simp only [List.length_cons, List.length_nil] at h₁ h₂
    norm_num only at h₁ h₂
    unfold work at hread h₁ h₂ hfail ⊢
    nlinarith only [hread, hz, haz, h₁, h₂, hm, hp', hwprod, hdim]
  · simp only [he, Bool.false_eq_true, ↓reduceIte]
    unfold work at hread h₁ h₂ hfail ⊢
    nlinarith only [hread, hz, haz, hfail, hm, hp', hwprod, hdim]

theorem saveResult_work {n : ℕ} (out : Result) (frame key : ℕ) (q : KeyV n)
    (ans : AnswerV n) (cs : CacheV n) (events : Counts) (B W : ℕ)
    (hh : WellFormed out.heap) (hf : read out.heap (frame + 1) = some (.ref key))
    (hk : KeyRep out.heap key (wireKey q)) (ha : SharedAnswerRep out.heap out.answer (wireAnswer ans))
    (hc : TreeBudgetChargedCache.CacheRep out.heap out.cache (wireCache cs))
    (hW : 1 ≤ W) (hframe : (frame + 1).size ≤ W)
    (hw : (out.heap.size + 4 * cs.length + 4).size ≤ W)
    (hcs : ∀ e ∈ wireCache cs, (encodeKey e.1).length ≤ B) (hq : (encodeKey (wireKey q)).length ≤ B) :
    work (saveResult out frame events) ≤ cacheUnit B W * (cs.length + 2) + 512 * (W + 2) := by
  have hload := loadRef_work out.heap frame 1 W hframe
  have hi := insertD_work out.heap out.cache key out.answer (wireCache cs) (wireKey q)
    (wireAnswer ans) B W hh hc hk ha hW (by simpa [wireCache] using hw) hcs hq
  have hret := work_then_le (insertD out.heap out.cache key out.answer)
    (fun saved => ret (Result.mk out.answer saved.1.1 saved.1.2
      (events.add (out.events.add { insertionScans := saved.2 }))))
    1 (by intro saved hs; rfl)
  unfold saveResult
  rw [work_then_some _ _ _ (loadRef_value _ _ _ _ hh hf)]
  simp only [wireCache, List.length_map] at hi
  omega

end UAVProof.TreeBudgetStoredControlWork
