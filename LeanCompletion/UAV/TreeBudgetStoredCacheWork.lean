import LeanCompletion.UAV.TreeBudgetStoredNodeWork

namespace UAVProof.TreeBudgetStoredCacheWork
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetCostedCandidates TreeBudgetAllocationBounds TreeBudgetSharedAnswerStore
open TreeBudgetChargedCache TreeBudgetStoredWork TreeBudgetStoredReadWork TreeBudgetStoredNodeWork
open TreeBudgetBinaryCodec TreeBudgetSearchStore TreeBudgetStoredCursor

def cacheUnit (B W : ℕ) : ℕ := 32768 * (B + 1) * (W + 2)

theorem cache_unit_envelope (B W : ℕ) :
    144 * (W + 1) + 1 + 512 * (W + 1) +
      4096 * (B + 1) * (W + 2) + 3 * (B + B + 1) +
      12800 * (W + 2) + 20 ≤ cacheUnit B W := by
  dsimp [cacheUnit]
  nlinarith [Nat.zero_le B, Nat.zero_le W, Nat.zero_le (B * W)]

theorem eqBits_work (xs ys : Bits) (B : ℕ) (hx : xs.length ≤ B) (hy : ys.length ≤ B) :
    work (eqBitsD xs ys) ≤ 3 * (B + B + 1) := by
  have h := eqBitsD_steps xs ys
  simp only [work, eqBitsD_allocations, Nat.add_zero]
  omega

theorem lookupD_work (heap : Heap) (a : ℕ) (cs : WireCache) (q : WireKey) (fuel B W : ℕ)
    (hh : WellFormed heap) (hr : TreeBudgetChargedCache.CacheRep heap a cs)
    (hf : a < fuel) (hW : 1 ≤ W) (hfw : fuel.size ≤ W)
    (hw : (heap.size + 4).size ≤ W)
    (hcs : ∀ e ∈ cs, (encodeKey e.1).length ≤ B) (hq : (encodeKey q).length ≤ B) :
    work (lookupD fuel heap a (encodeKey q)) ≤ cacheUnit B W * (lookupCount cs q + 1) := by
  induction hr generalizing fuel with
  | nil a header =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha := TreeBudgetChargedCache.cacheRep_address_lt (.nil a header)
      have hhead := headRead_work heap a W ((Nat.size_le_size (by omega)).trans hw)
      have hcursor := cursor_work (fuel + 1) W hfw hW
      have hunit := cache_unit_envelope B W
      rw [lookupD, work_then_some _ _ _ (cursorStep_succ fuel),
        work_then_some _ _ _ (headRead_nil _ _ hh header)]
      simp only [work_ret, lookupCount, Nat.zero_add, Nat.mul_one]
      omega
  | cons a k v t key ans cs header hk hv ht hl ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha : a < heap.size := by have hb := header.1; dsimp at hb; omega
      have hhead := headRead_work heap a W ((Nat.size_le_size (by omega)).trans hw)
      have hcursor := cursor_work (fuel + 1) W hfw hW
      have hkey := hcs (key, ans) (by simp)
      change (encodeKey key).length ≤ B at hkey
      have hblob := blobRead_work heap k (encodeKey key) W hh hk hW
        ((Nat.size_le_size (by omega)).trans hw)
      have hblob' := Nat.mul_le_mul_right (W + 2) (Nat.mul_le_mul_left 4096 (Nat.add_le_add_right hkey 1))
      have heq := eqBits_work (encodeKey key) (encodeKey q) B hkey hq
      have hunit := cache_unit_envelope B W
      have htail := ih fuel (by omega) ((Nat.size_le_size (Nat.le_succ fuel)).trans hfw)
        (fun e he => hcs e (by simp [he]))
      rw [lookupD, work_then_some _ _ _ (cursorStep_succ fuel),
        work_then_some _ _ _ (headRead_cons _ _ _ _ _ hh header),
        work_then_some _ _ _ (blobRead_correct _ _ _ hh hk)]
      simp only [work_bind, eqBitsD_value, encodeKey_injective.eq_iff]
      by_cases he : key = q
      · rw [he] at heq
        simp only [he, decide_true, ↓reduceIte, work_ret, lookupCount]
        omega
      · have hrec := work_then_le (lookupD fuel heap t (encodeKey q))
          (fun out => ret (out.1, out.2 + 1)) 1 (by intro out ho; rfl)
        simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte, lookupCount, if_neg he]
        nlinarith only [hhead, hcursor, hblob, hblob', heq, hunit, htail, hrec]

theorem filterD_work (heap : Heap) (a : ℕ) (cs : WireCache) (q : WireKey) (fuel B W : ℕ)
    (hh : WellFormed heap) (hr : TreeBudgetChargedCache.CacheRep heap a cs)
    (hf : a < fuel) (hW : 1 ≤ W) (hfw : fuel.size ≤ W)
    (hw : (heap.size + 4 * cs.length + 4).size ≤ W)
    (hcs : ∀ e ∈ cs, (encodeKey e.1).length ≤ B) (hq : (encodeKey q).length ≤ B) :
    work (filterD fuel heap a (encodeKey q)) ≤ cacheUnit B W * (cs.length + 1) := by
  induction hr generalizing fuel with
  | nil a header =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha := TreeBudgetChargedCache.cacheRep_address_lt (.nil a header)
      have hhead := headRead_work heap a W ((Nat.size_le_size (by simp at hw; omega)).trans hw)
      have hcursor := cursor_work (fuel + 1) W hfw hW
      have hunit := cache_unit_envelope B W
      rw [filterD, work_then_some _ _ _ (cursorStep_succ fuel),
        work_then_some _ _ _ (headRead_nil _ _ hh header)]
      simp only [work_ret, List.length_nil, Nat.zero_add, Nat.mul_one]
      omega
  | cons a k v t key ans cs header hk hv ht hl ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha : a < heap.size := by have hb := header.1; dsimp at hb; omega
      have hwide : (heap.size + 4).size ≤ W := (Nat.size_le_size (by omega)).trans hw
      have hhead := headRead_work heap a W ((Nat.size_le_size (by omega)).trans hwide)
      have hcursor := cursor_work (fuel + 1) W hfw hW
      have hkey := hcs (key, ans) (by simp)
      change (encodeKey key).length ≤ B at hkey
      have hblob := blobRead_work heap k (encodeKey key) W hh hk hW
        ((Nat.size_le_size (by omega)).trans hwide)
      have hblob' := Nat.mul_le_mul_right (W + 2) (Nat.mul_le_mul_left 4096 (Nat.add_le_add_right hkey 1))
      have heq := eqBits_work (encodeKey key) (encodeKey q) B hkey hq
      have hunit := cache_unit_envelope B W
      have htail := ih fuel (by omega) ((Nat.size_le_size (Nat.le_succ fuel)).trans hfw)
        ((Nat.size_le_size (by simp only [List.length_cons]; omega)).trans hw)
        (fun e he => hcs e (by simp [he]))
      obtain ⟨root, after, hvalue, hrep, hwf, hext, hsize⟩ :=
        filterD_correct heap t cs hh ht q fuel (by omega)
      have hkeep : (keep cs q).length ≤ cs.length := List.length_filter_le ..
      have halloc := alloc_work after [.bit true, .ref k, .ref v, .ref root] W
        ((Nat.size_le_size (by simp only [List.length_cons, List.length_nil] at *; omega)).trans hw)
      rw [filterD, work_then_some _ _ _ (cursorStep_succ fuel),
        work_then_some _ _ _ (headRead_cons _ _ _ _ _ hh header),
        work_then_some _ _ _ (blobRead_correct _ _ _ hh hk)]
      simp only [work_bind, eqBitsD_value, encodeKey_injective.eq_iff, work_charge]
      rw [work_then_some _ _ _ hvalue]
      by_cases he : key = q
      · rw [he] at heq
        simp only [he, decide_true, ↓reduceIte, work_ret, List.length_cons]
        nlinarith only [hhead, hcursor, hblob, hblob', heq, hunit, htail]
      · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte, work_bind, work_ret, List.length_cons]
        simp only [List.length_cons, List.length_nil] at halloc
        norm_num only at halloc
        nlinarith only [hhead, hcursor, hblob, hblob', heq, hunit, htail, halloc]

theorem insertD_work (heap : Heap) (a key answer : ℕ) (cs : WireCache) (q : WireKey)
    (ans : WireAnswer) (B W : ℕ) (hh : WellFormed heap)
    (hc : TreeBudgetChargedCache.CacheRep heap a cs) (hk : KeyRep heap key q)
    (hv : SharedAnswerRep heap answer ans) (hW : 1 ≤ W)
    (hw : (heap.size + 4 * cs.length + 4).size ≤ W)
    (hcs : ∀ e ∈ cs, (encodeKey e.1).length ≤ B) (hq : (encodeKey q).length ≤ B) :
    work (insertD heap a key answer) ≤ cacheUnit B W * (cs.length + 2) := by
  have hfuel : (heap.size + 1).size ≤ W := (Nat.size_le_size (by omega)).trans hw
  have hblob := blobRead_work heap key (encodeKey q) W hh hk hW hfuel
  have hblob' := Nat.mul_le_mul_right (W + 2) (Nat.mul_le_mul_left 4096 (Nat.add_le_add_right hq 1))
  have hinit := (arithmetic_work heap.size 1 W
    ((Nat.size_le_size (by omega)).trans hw) (by simpa using hW)).2.2
  have hfilter := filterD_work heap a cs q (heap.size + 1) B W hh hc
    (by have := TreeBudgetChargedCache.cacheRep_address_lt hc; omega) hW hfuel hw hcs hq
  obtain ⟨root, after, ho, hr, hh', he, hs⟩ := filterD_correct heap a cs hh hc q
    (heap.size + 1) (by have := TreeBudgetChargedCache.cacheRep_address_lt hc; omega)
  have hkeep : (keep cs q).length ≤ cs.length := List.length_filter_le ..
  have halloc := alloc_work after [.bit true, .ref key, .ref answer, .ref root] W
    ((Nat.size_le_size (by simp only [List.length_cons, List.length_nil]; omega)).trans hw)
  have hunit := cache_unit_envelope B W
  unfold insertD
  rw [work_then_some _ _ _ (blobRead_correct _ _ _ hh hk), work_bind, addNatD_value,
    work_then_some _ _ _ ho]
  simp only [work_bind, work_ret]
  simp only [List.length_cons, List.length_nil] at halloc
  norm_num only at halloc
  nlinarith only [hblob, hblob', hinit, hfilter, halloc, hunit]

end UAVProof.TreeBudgetStoredCacheWork
