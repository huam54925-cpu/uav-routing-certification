import LeanCompletion.UAV.TreeBudgetParameterizedBounds

/-! Bounds for every successful cache entry, including intermediate caches.
CacheValid alone constrains only lookup-visible answers. KeysNodup is essential
when passing from membership to validity. No search or cache operation changes. -/
namespace UAVProof.TreeBudgetCacheEntryBounds
open TreeFlowExistence TreeBudgetPatterns TreeBudgetCertificate TreeBudgetResidualSearch
open TreeBudgetMemoState TreeBudgetMemoSearch TreeBudgetMemoReachability TreeBudgetMemoBounds
open TreeBudgetStateParameters TreeBudgetParameterizedBounds TreeBudgetSearchStats
variable {n : ℕ}

/-- Without duplicate keys every list member is the answer visible to lookup. -/
theorem lookup_eq_some_of_mem (cache : Cache n) (q : Key n) (answer : Answer n)
    (hn : KeysNodup cache) (hm : (q, answer) ∈ cache) :
    lookup cache q = some answer := by
  induction cache with
  | nil => simp at hm
  | cons e cache ih =>
    have hn' : e.1 ∉ cache.map Prod.fst ∧ KeysNodup cache := by
      simpa only [KeysNodup, List.map_cons, List.nodup_cons] using hn
    rcases List.mem_cons.mp hm with he | hm
    · subst e
      simp [lookup]
    · have hne : e.1 ≠ q := by
        intro he
        apply hn'.1
        rw [he]
        exact List.mem_map.mpr ⟨(q, answer), hm, rfl⟩
      simpa only [lookup, if_neg hne] using ih hn'.2 hm

theorem reachable_count_le_initial (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) {k : ℕ} {r : Fin n → ℕ}
    (hr : ReachableResidual R H s T k r) : k ≤ rootCount R H := by
  rw [(reachable_invariants R H s T hr).1]
  exact Finset.sum_le_sum (fun v _ => (reachable_invariants R H s T hr).2 v)

/-- The three invariants needed for bounds on all stored answers, not only hits. -/
structure CacheReady (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (cache : Cache n) : Prop where
  valid : CacheValid R H s T cache
  nodup : KeysNodup cache
  reachable : AllKeysReachable R H s T cache

theorem cacheReady_empty (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) : CacheReady R H s T emptyCache :=
  ⟨cacheValid_empty R H s T, keysNodup_empty, allKeysReachable_empty R H s T⟩

/-- These bounds concern every member, regardless of its lookup position. -/
structure SuccessEntryBounds (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (k : ℕ) (r : Fin n → ℕ) (rows : Rows n) : Prop where
  length_eq : rows.length = k
  count_le_initial : k ≤ rootCount R H
  initial_le_total : rootCount R H ≤ totalMultiplicity R H
  row_root : ∀ p ∈ rows, p R.root = 0
  row_le : ∀ p ∈ rows, p ≤ H

theorem cache_success_entry_bounds (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (cache : Cache n)
    (hc : CacheReady R H s T cache) (k : ℕ) (r : Fin n → ℕ) (rows : Rows n)
    (hm : ((k, r), some rows) ∈ cache) : SuccessEntryBounds R H k r rows := by
  have hw : ResidualWitness R H s T k r rows :=
    hc.valid (k, r) (some rows) (lookup_eq_some_of_mem cache _ _ hc.nodup hm)
  refine ⟨hw.1, reachable_count_le_initial R H s T (hc.reachable _ hm),
    rootCount_le_totalMultiplicity R H, ?_, ?_⟩
  · intro p hp
    exact (hw.2.1 p hp).1
  · intro p hp v
    by_cases hv : v = R.root
    · simpa only [hv, (hw.2.1 p hp).1] using Nat.zero_le (H R.root)
    · exact (hw.2.1 p hp).2.1 v hv

theorem cache_success_length_le_totalMultiplicity
    (R : RootedTree (Fin n)) (H : Fin n → ℕ) (s : Fin n → ℚ) (T : ℚ)
    (cache : Cache n) (hc : CacheReady R H s T cache) (k : ℕ)
    (r : Fin n → ℕ) (rows : Rows n) (hm : ((k, r), some rows) ∈ cache) :
    rows.length ≤ totalMultiplicity R H := by
  have hb := cache_success_entry_bounds R H s T cache hc k r rows hm
  rw [hb.length_eq]
  exact hb.count_le_initial.trans hb.initial_le_total

/-- Each child result and each completed state remains ready for the next step. -/
theorem memoRows_cacheReady (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ)
    (hr : ReachableResidual R H s T k r) (cache : Cache n)
    (hc : CacheReady R H s T cache) :
    CacheReady R H s T (memoRows R H s T k r cache).2 :=
  ⟨(memoRows_spec R H s T k r cache hc.valid).1,
    memoRows_nodup R H s T k r cache hc.nodup,
    memoRows_reachable R H s T k r hr cache hc.reachable⟩

/-- A suffix is independent of the complete candidate list reused by children.
In particular this covers the cache after failure followed by further scanning. -/
theorem scanCandidates_cacheReady (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ)
    (hr : ReachableResidual R H s T (k + 1) r)
    (tail : List (Fin n → ℕ)) (hp : ∀ p ∈ tail, RowValid R H s T p)
    (cache : Cache n) (hc : CacheReady R H s T cache) :
    CacheReady R H s T (scanCandidates (memoRows R H s T k) r tail cache).2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (scanCandidates_spec R H s T k (memoRows R H s T k)
      (fun r cs hv => memoRows_spec R H s T k r cs hv) r tail hp cache hc.valid).1
  · exact scanCandidates_preserves KeysNodup (memoRows R H s T k)
      (fun r cs hn => memoRows_nodup R H s T k r cs hn) r tail cache hc.nodup
  · exact scanCandidates_reachable R H s T k (memoRows R H s T k)
      (fun r cs hr hc => memoRows_reachable R H s T k r hr cs hc)
      r hr tail hp cache hc.reachable

theorem memoRows_success_entry_bounds (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ)
    (hr : ReachableResidual R H s T k r) (cache : Cache n)
    (hc : CacheReady R H s T cache) (j : ℕ) (q : Fin n → ℕ) (rows : Rows n)
    (hm : ((j, q), some rows) ∈ (memoRows R H s T k r cache).2) :
    SuccessEntryBounds R H j q rows :=
  cache_success_entry_bounds R H s T _ (memoRows_cacheReady R H s T k r hr cache hc)
    j q rows hm

theorem initial_success_entry_bounds (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (j : ℕ) (q : Fin n → ℕ) (rows : Rows n)
    (hm : ((j, q), some rows) ∈ (memoRows R H s T (rootCount R H) H emptyCache).2) :
    SuccessEntryBounds R H j q rows :=
  memoRows_success_entry_bounds R H s T _ _ .initial _ (cacheReady_empty R H s T)
    j q rows hm

theorem initial_stat_success_entry_bounds (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (j : ℕ) (q : Fin n → ℕ) (rows : Rows n)
    (hm : ((j, q), some rows) ∈
      (memoRowsStat R H s T (rootCount R H) H emptyCache).1.2) :
    SuccessEntryBounds R H j q rows := by
  rw [memoRowsStat_erase] at hm
  exact initial_success_entry_bounds R H s T j q rows hm

end UAVProof.TreeBudgetCacheEntryBounds

#print axioms UAVProof.TreeBudgetCacheEntryBounds.lookup_eq_some_of_mem
#print axioms UAVProof.TreeBudgetCacheEntryBounds.reachable_count_le_initial
#print axioms UAVProof.TreeBudgetCacheEntryBounds.cacheReady_empty
#print axioms UAVProof.TreeBudgetCacheEntryBounds.cache_success_entry_bounds
#print axioms UAVProof.TreeBudgetCacheEntryBounds.cache_success_length_le_totalMultiplicity
#print axioms UAVProof.TreeBudgetCacheEntryBounds.memoRows_cacheReady
#print axioms UAVProof.TreeBudgetCacheEntryBounds.scanCandidates_cacheReady
#print axioms UAVProof.TreeBudgetCacheEntryBounds.memoRows_success_entry_bounds
#print axioms UAVProof.TreeBudgetCacheEntryBounds.initial_success_entry_bounds
#print axioms UAVProof.TreeBudgetCacheEntryBounds.initial_stat_success_entry_bounds
