import LeanCompletion.UAV.TreeBudgetBinarySearch
import LeanCompletion.UAV.TreeBudgetSearchAllocations
import LeanCompletion.UAV.TreeBudgetAllocationBounds

/-! Concrete search allocation counts, followed by address-width bounds.
The slot counter is part of the executable recursion. The address theorem
applies to a sequential allocator using that counter; it is not a proof that
Lean's allocator or a compiled RAM execution has the same heap layout. -/
namespace UAVProof.TreeBudgetBinarySearchStorage
open TreeBudgetBitPrimitives TreeBudgetBinarySearch TreeBudgetSearchAllocations
open TreeBudgetCostedSearch TreeBudgetCostedSearchBounds TreeBudgetAllocationBounds
open TreeBudgetVectorMemoState TreeFlowExistence TreeBudgetVector TreeBudgetPatterns
open TreeBudgetMemoBounds
variable {n : ℕ}

theorem backend_allocationBound (n : ℕ) : BackendAllocationBound (backend n) := by
  constructor
  · exact keyEqV_allocations_le_steps
  · intro p q; exact (vector_allocations_le_steps p q).1
  · intro p q; exact (vector_allocations_le_steps p q).2.2.1
  · intro p; exact (vector_allocations_le_steps p p).2.2.2

theorem search_allocations (ps : List (Vector ℕ n)) (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) :
    (search ps k r cs).allocations ≤ 8 * (search ps k r cs).work :=
  memoCost_allocations (backend n) (backend_allocationBound n) ps k r cs

theorem initial_allocations (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) :
    (initialCost (backend n) R H A AT).allocations ≤
      8 * (initialCost (backend n) R H A AT).work := by
  unfold initialCost
  exact memoCost_allocations (backend n) (backend_allocationBound n) _ _ _ _

theorem initial_slots (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (β : ℕ)
    (hk : (rootCount R (decode (TreeBudgetVector.normalize R H))).size ≤ β)
    (hH : ∀ i : Fin n, (TreeBudgetVector.normalize R H)[i].size ≤ β) :
    (initialCost (backend n) R H A AT).allocations ≤
      searchSlotBound (stateBound R (TreeBudgetPatterns.normalize R (decode H))) n β := by
  exact (initial_allocations R H A AT).trans
    (Nat.mul_le_mul_left 8 (initial_search_work R H A AT s T D hD hA hAT β hk hH))

theorem initial_address_width (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (β ell initial address : ℕ)
    (hk : (rootCount R (decode (TreeBudgetVector.normalize R H))).size ≤ β)
    (hH : ∀ i : Fin n, (TreeBudgetVector.normalize R H)[i].size ≤ β)
    (hS : (stateBound R (TreeBudgetPatterns.normalize R (decode H))).size ≤ 3 * ell + 1)
    (hn : n ≤ ell) (hβ : β ≤ 6 * ell + 4) (hi : initial.size ≤ ell + 8)
    (ha : address < initial + (initialCost (backend n) R H A AT).allocations) :
    address.size ≤ 17 * ell + 49 := by
  apply search_address_width _ address initial _ n β ell ha
  · exact Nat.add_le_add_left (initial_slots R H A AT s T D hD hA hAT β hk hH) initial
  · exact hi
  · exact hS
  · exact hn
  · exact hβ

end UAVProof.TreeBudgetBinarySearchStorage
