import LeanCompletion.UAV.TreeBudgetCostedSearchBounds
import LeanCompletion.UAV.TreeBudgetBitPrimitives

/-! Instantiate the ordered search with actual digit-recursive primitives.
This establishes intrinsic bit-cell work of the search phase. Parsing,
preprocessing, candidate generation, heap-address simulation and serialization
are separate obligations for a total binary-input time theorem. -/
namespace UAVProof.TreeBudgetBinarySearch
open TreeBudgetBitPrimitives TreeBudgetCostedSearch TreeBudgetCostedSearchBounds
open TreeBudgetVectorMemoState TreeBudgetVectorSearchStats TreeBudgetVectorMemoIntegration
open TreeBudgetVector TreeFlowExistence TreeBudgetPatterns TreeBudgetMemoBounds
open TreeBudgetStateParameters
variable {n : ℕ}

def backend (n : ℕ) : Backend n where
  keyEq p q := ((keyEqV p q).value, (keyEqV p q).steps)
  guard p q := ((guardV p q).value, (guardV p q).steps)
  subtract p q := ((subV p q).value, (subV p q).steps)
  zero p := ((zeroV p).value, (zeroV p).steps)
  keyEqAlloc p q := (keyEqV p q).allocations
  guardAlloc p q := (guardV p q).allocations
  subtractAlloc p q := (subV p q).allocations
  zeroAlloc p := (zeroV p).allocations
  keyEq_value p q := keyEqV_value p q
  guard_value p q := guardV_value p q
  subtract_value p q := subV_value p q
  zero_value p := zeroV_value p

def search (ps : List (Vector ℕ n)) (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) :=
  memoCost (backend n) ps k r cs

/-- Exact concrete result, ordered cache, and all six counters for arbitrary
candidate lists and raw caches, including duplicate keys. -/
theorem search_refines (ps : List (Vector ℕ n)) (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) :
    decodeMeasured (observe (search ps k r cs)) =
      TreeBudgetSearchStats.memoStat (ps.map decode) k (decode r) (decodeCache cs) := by
  rw [search, memoCost_observe, memoStatV_refines]

theorem backend_bounded (K : ℕ) (H : Vector ℕ n) (β : ℕ)
    (hk : K.size ≤ β) (hH : ∀ i : Fin n, H[i].size ≤ β) :
    BackendBounded (backend n) K H (256 * (n + 1) * (β + 1)) := by
  have hsmall : ∀ p, VecSmall H p → ∀ i : Fin n, p[i].size ≤ β :=
    fun p hp i => (Nat.size_le_size (hp i)).trans (hH i)
  constructor
  · intro p q hp hq
    exact keyEqV_steps p q β ((Nat.size_le_size hp.1).trans hk)
      ((Nat.size_le_size hq.1).trans hk) (hsmall p.2 hp.2) (hsmall q.2 hq.2)
  · intro p q hp hq
    have h := guardV_steps p q β (hsmall p hp) (hsmall q hq)
    change (guardV p q).steps ≤ _
    nlinarith
  · intro p q hp hq
    have h := subV_steps p q β (hsmall p hp) (hsmall q hq)
    change (subV p q).steps ≤ _
    nlinarith
  · intro p hp
    have h := zeroV_steps p β (hsmall p hp)
    change (zeroV p).steps ≤ _
    nlinarith

theorem search_work (ps : List (Vector ℕ n)) (K k β : ℕ) (H r : Vector ℕ n)
    (cs : CacheV n) (hK : K.size ≤ β) (hH : ∀ i : Fin n, H[i].size ≤ β)
    (hp : ∀ p ∈ ps, VecSmall H p) (hk : k ≤ K) (hr : VecSmall H r)
    (hc : CacheSmall K H cs) :
    (search ps k r cs).work ≤
      (1024 * (n + 1) * (β + 1) + 8) * eventWeight (search ps k r cs).events := by
  have h := memoCost_work (backend n) K H _ (backend_bounded K H β hK hH)
    ps k r cs hp hk hr hc
  simpa only [search, ← Nat.mul_assoc] using h

theorem initial_search_work (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (β : ℕ)
    (hk : (rootCount R (decode (TreeBudgetVector.normalize R H))).size ≤ β)
    (hH : ∀ i : Fin n, (TreeBudgetVector.normalize R H)[i].size ≤ β) :
    (initialCost (backend n) R H A AT).work ≤
      (1024 * (n + 1) * (β + 1) + 8) * 7 *
        (stateBound R (TreeBudgetPatterns.normalize R (decode H)) + 1) ^ 3 := by
  have h := initialCost_work (backend n) R H A AT s T D hD hA hAT _
    (backend_bounded _ _ β hk hH)
  simpa only [← Nat.mul_assoc] using h

end UAVProof.TreeBudgetBinarySearch
