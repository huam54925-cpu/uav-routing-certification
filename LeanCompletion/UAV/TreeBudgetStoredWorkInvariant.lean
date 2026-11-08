import LeanCompletion.UAV.TreeBudgetStoredPayloadWork
import LeanCompletion.UAV.TreeBudgetStoredCacheWork
import LeanCompletion.UAV.TreeBudgetStoredHeapGrowth

namespace UAVProof.TreeBudgetStoredWorkInvariant
open TreeBudgetBitMachine TreeBudgetCostedCandidates TreeBudgetAllocationBounds TreeBudgetTypedStore
open TreeBudgetSearchStore TreeBudgetSharedAnswerStore TreeBudgetChargedCache TreeBudgetStoredSearch
open TreeBudgetStoredAllocation TreeBudgetStoredWork TreeBudgetCostedSearchBounds
open TreeBudgetVectorMemoState TreeBudgetSearchStats TreeBudgetBinaryCodec

structure PayloadBounds {n : ℕ} (K : ℕ) (H : Vector ℕ n) (B : ℕ) : Prop where
  positive : 1 ≤ B
  dimension : n ≤ B
  depth : K.size ≤ B
  coordinates : ∀ i : Fin n, H[i].size ≤ B
  rows : ∀ v, VecSmall H v → rowSlots v ≤ B
  keys : ∀ k v, k ≤ K → VecSmall H v → keySlots k v ≤ B

def capacity (B : ℕ) (heap : Heap) : ℕ := 8 * (heap.size + B + 1)
def addressWidth (B : ℕ) (heap : Heap) : ℕ := (capacity B heap).size
def unitWork (B : ℕ) (heap : Heap) : ℕ :=
  1048576 * (B + 1) ^ 3 * (addressWidth B heap + 2)

theorem addressWidth_positive (B : ℕ) (heap : Heap) : 1 ≤ addressWidth B heap := by
  have h : 1 ≤ capacity B heap := by dsimp [capacity]; omega
  have hs := Nat.size_le_size h
  simpa [addressWidth] using hs

theorem addressWidth_bound (B : ℕ) (heap : Heap) (a : ℕ) (ha : a ≤ capacity B heap) :
    a.size ≤ addressWidth B heap := Nat.size_le_size ha

theorem unitWork_mono (B : ℕ) (before after : Heap) (he : before.size ≤ after.size) :
    unitWork B before ≤ unitWork B after := by
  have hc : capacity B before ≤ capacity B after := by dsimp [capacity]; omega
  have hw := Nat.size_le_size hc
  dsimp [unitWork, addressWidth]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hw 2)

theorem cacheLength_le_address (heap : Heap) (a : ℕ) (cs : WireCache)
    (hr : TreeBudgetChargedCache.CacheRep heap a cs) : cs.length ≤ a := by
  induction hr with
  | nil a header => simp
  | cons a k v t q ans cs header hk hv ht hl ih => simp only [List.length_cons]; omega

theorem cacheLength_le_heap (heap : Heap) (a : ℕ) (cs : WireCache)
    (hr : TreeBudgetChargedCache.CacheRep heap a cs) : cs.length ≤ heap.size :=
  (cacheLength_le_address heap a cs hr).trans (TreeBudgetChargedCache.cacheRep_address_lt hr).le

theorem rows_bytes {n : ℕ} {K B : ℕ} {H v : Vector ℕ n}
    (hb : PayloadBounds K H B) (hv : VecSmall H v) : (encodeNats v.toList).length ≤ B := by
  have h := hb.rows v hv
  dsimp [rowSlots] at h
  omega

theorem keys_bytes {n : ℕ} {K B k : ℕ} {H v : Vector ℕ n}
    (hb : PayloadBounds K H B) (hk : k ≤ K) (hv : VecSmall H v) :
    (encodeKey (k, v.toList)).length ≤ B := by
  have h := hb.keys k v hk hv
  dsimp [keySlots] at h
  omega

theorem cache_keys_bytes {n : ℕ} {K B : ℕ} {H : Vector ℕ n} (hb : PayloadBounds K H B)
    (cs : CacheV n) (hc : CacheSmall K H cs) :
    ∀ e ∈ wireCache cs, (encodeKey e.1).length ≤ B := by
  intro e he
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp he
  have hs := hc entry hentry
  exact keys_bytes hb hs.1 hs.2

/-- The recorded work and the semantic observation are properties of the same
run. The final heap supplies the capacity used in this intermediate bound. -/
def WorkRep (extra B : ℕ) (before : Heap) (out : Costed (Option Result))
    (answer : WireAnswer) (cache : WireCache) (events : Counts) : Prop :=
  ∃ result, out.value = some result ∧ SharedAnswerRep result.heap result.answer answer ∧
    TreeBudgetChargedCache.CacheRep result.heap result.cache cache ∧
    WellFormed result.heap ∧ Extends before result.heap ∧ result.events = events ∧
    work out ≤ unitWork B result.heap * (extra + eventWeight events)

theorem workRep_forget {extra B : ℕ} {before : Heap} {out : Costed (Option Result)}
    {answer : WireAnswer} {cache : WireCache} {events : Counts}
    (h : WorkRep extra B before out answer cache events) : ResultRep before out answer cache events := by
  obtain ⟨r, hv, ha, hc, hh, he, hev, hw⟩ := h
  exact ⟨r, hv, ha, hc, hh, he, hev⟩

end UAVProof.TreeBudgetStoredWorkInvariant
