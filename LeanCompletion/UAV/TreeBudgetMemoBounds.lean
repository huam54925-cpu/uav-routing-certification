import LeanCompletion.UAV.TreeBudgetMemoReachability
import LeanCompletion.UAV.TreeBudgetMemoSearch

/-! Finite state and cache-entry bounds. These are combinatorial bounds, not a
polynomial running-time claim for binary-encoded inputs or association lists. -/
namespace UAVProof.TreeBudgetMemoBounds
open TreeFlowExistence TreeBudgetPatterns TreeBudgetRow TreeBudgetMemoState
open TreeBudgetMemoSearch TreeBudgetMemoReachability TreeBudgetCertificate
variable {n : ℕ}

abbrev ReachableKey (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) :=
  {q : Key n // ReachableResidual R H s T q.1 q.2}

/-- The root coordinate has a fixed value and contributes one possibility. -/
def stateBound (R : RootedTree (Fin n)) (H : Fin n → ℕ) : ℕ :=
  ∏ v ∈ Finset.univ.filter (fun v => v ≠ R.root), (H v + 1)

theorem boundedRow_card (R : RootedTree (Fin n)) (H : Fin n → ℕ) :
    Fintype.card (BoundedRow R H) = stateBound R H := by
  simp only [BoundedRow, Fintype.card_pi, Fintype.card_fin, stateBound, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro v _
  by_cases hv : v = R.root <;> simp [bound, hv]

/-- A counting-only encoding: the executable cache still compares the full
key. On reachable keys, the count and root coordinate are recoverable. -/
def encodeReachable (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (q : ReachableKey R H s T) : BoundedRow R H :=
  packRow R H q.val.2 (fun v _ => (reachable_invariants R H s T q.property).2 v)

theorem encodeReachable_injective (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Function.Injective (encodeReachable R H s T) := by
  intro a b hab
  have hr : a.val.2 = b.val.2 := by
    funext v
    by_cases hv : v = R.root
    · subst v
      exact (reachable_root R H s T a.property).trans
        (reachable_root R H s T b.property).symm
    · have he := congrArg (fun p : BoundedRow R H => values p v) hab
      simpa [encodeReachable, values_packRow, TreeBudgetPatterns.normalize, hv] using he
  apply Subtype.ext
  apply Prod.ext
  · exact (reachable_invariants R H s T a.property).1.trans
      ((congrArg (rootCount R) hr).trans (reachable_invariants R H s T b.property).1.symm)
  · exact hr

noncomputable instance reachableKeyFintype (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Fintype (ReachableKey R H s T) :=
  Fintype.ofInjective (encodeReachable R H s T) (encodeReachable_injective R H s T)

theorem reachableKey_card_le (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    Fintype.card (ReachableKey R H s T) ≤ stateBound R H := by
  rw [← boundedRow_card]
  exact Fintype.card_le_of_injective _ (encodeReachable_injective R H s T)

/-- Both reachability and no duplicate keys are needed to bound cache entries. -/
theorem cache_length_le (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (cache : Cache n)
    (hc : AllKeysReachable R H s T cache) (hn : KeysNodup cache) :
    cache.length ≤ stateBound R H := by
  let qs : List (ReachableKey R H s T) :=
    cache.attach.map (fun e => ⟨e.val.1, hc e.val e.property⟩)
  have he : qs.map Subtype.val = cache.map Prod.fst := by
    simp only [qs, List.map_map]
    change cache.attach.map (Prod.fst ∘ Subtype.val) = cache.map Prod.fst
    rw [← List.map_map, List.attach_map_subtype_val]
  have hq : qs.Nodup := List.Nodup.of_map Subtype.val (he.symm ▸ hn)
  have hl : qs.length = cache.length := by simp [qs]
  rw [← hl]
  exact (List.Nodup.length_le_card hq).trans (reachableKey_card_le R H s T)

theorem scanCandidates_reachable (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ)
    (solve : (Fin n → ℕ) → Cache n → Answer n × Cache n)
    (hsolve : ∀ r cache, ReachableResidual R H s T k r →
      AllKeysReachable R H s T cache → AllKeysReachable R H s T (solve r cache).2)
    (r : Fin n → ℕ) (hr : ReachableResidual R H s T (k + 1) r)
    (ps : List (Fin n → ℕ)) (hp : ∀ p ∈ ps, RowValid R H s T p)
    (cache : Cache n) (hc : AllKeysReachable R H s T cache) :
    AllKeysReachable R H s T (scanCandidates solve r ps cache).2 := by
  induction ps generalizing cache with
  | nil => exact hc
  | cons p ps ih =>
    have ht : ∀ q ∈ ps, RowValid R H s T q := fun q hq => hp q (by simp [hq])
    by_cases hle : ∀ v, p v ≤ r v
    · have hs := hsolve (r - p) cache (.step hr (hp p (by simp)) hle) hc
      cases he : (solve (r - p) cache).1 with
      | none => simpa only [scanCandidates, if_pos hle, he] using ih ht _ hs
      | some rows => simpa only [scanCandidates, if_pos hle, he] using hs
    · simpa only [scanCandidates, if_neg hle] using ih ht cache hc

theorem memoRowsWith_reachable (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (ps : List (Fin n → ℕ))
    (hp : ∀ p ∈ ps, RowValid R H s T p) (k : ℕ) (r : Fin n → ℕ)
    (hr : ReachableResidual R H s T k r) (cache : Cache n)
    (hc : AllKeysReachable R H s T cache) :
    AllKeysReachable R H s T (memoRowsWith ps k r cache).2 := by
  induction k generalizing r cache with
  | zero =>
    cases he : lookup cache (0, r) with
    | none =>
      simp only [memoRowsWith, he]
      exact allKeysReachable_insert R H s T cache (0, r) _ hc hr
    | some answer => simpa only [memoRowsWith, he] using hc
  | succ k ih =>
    cases he : lookup cache (k + 1, r) with
    | none =>
      simp only [memoRowsWith, he]
      exact allKeysReachable_insert R H s T _ (k + 1, r) _
        (scanCandidates_reachable R H s T k (memoRowsWith ps k)
          (fun r cache hr hc => ih r hr cache hc) r hr ps hp cache hc) hr
    | some answer => simpa only [memoRowsWith, he] using hc

theorem memoRows_reachable (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ)
    (hr : ReachableResidual R H s T k r) (cache : Cache n)
    (hc : AllKeysReachable R H s T cache) :
    AllKeysReachable R H s T (memoRows R H s T k r cache).2 :=
  memoRowsWith_reachable R H s T _
    (fun _ hp => (TreeBudgetFiniteSearch.mem_candidates ..).mp hp) k r hr cache hc

/-- This bounds the actual returned cache, not merely the abstract state space. -/
theorem memoRows_cache_length_le (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (k : ℕ) (r : Fin n → ℕ)
    (hr : ReachableResidual R H s T k r) (cache : Cache n)
    (hc : AllKeysReachable R H s T cache) (hn : KeysNodup cache) :
    (memoRows R H s T k r cache).2.length ≤ stateBound R H :=
  cache_length_le R H s T _ (memoRows_reachable R H s T k r hr cache hc)
    (memoRows_nodup R H s T k r cache hn)

theorem initial_cache_length_le (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    (memoRows R H s T (rootCount R H) H emptyCache).2.length ≤ stateBound R H :=
  memoRows_cache_length_le R H s T _ _ .initial _
    (allKeysReachable_empty R H s T) keysNodup_empty

end UAVProof.TreeBudgetMemoBounds

#print axioms UAVProof.TreeBudgetMemoBounds.boundedRow_card
#print axioms UAVProof.TreeBudgetMemoBounds.encodeReachable_injective
#print axioms UAVProof.TreeBudgetMemoBounds.reachableKey_card_le
#print axioms UAVProof.TreeBudgetMemoBounds.cache_length_le
#print axioms UAVProof.TreeBudgetMemoBounds.memoRows_reachable
#print axioms UAVProof.TreeBudgetMemoBounds.memoRows_cache_length_le
#print axioms UAVProof.TreeBudgetMemoBounds.initial_cache_length_le
