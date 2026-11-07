import LeanCompletion.UAV.TreeBudgetCostedSearch

/-! Cumulative fresh-slot accounting for the ordered recursion. Keys, vectors,
cache entry payloads and answer tails are borrowed by reference. A tagged cons
uses three slots, a pair two, a tagged option two, and each control activation
one. The counter includes all allocated frames and never subtracts freed slots.
Primitive allocations are observed from the same backend execution as work.
This counter is independent of address widths. A heap representation simulation
is still needed to identify it with allocations of a compiled RAM program. -/
namespace UAVProof.TreeBudgetSearchAllocations
open TreeBudgetCostedSearch TreeBudgetVectorMemoState
variable {n : ℕ}

structure BackendAllocationBound (B : Backend n) : Prop where
  keyEq : ∀ p q, B.keyEqAlloc p q ≤ (B.keyEq p q).2
  guard : ∀ p q, B.guardAlloc p q ≤ (B.guard p q).2
  subtract : ∀ p q, B.subtractAlloc p q ≤ (B.subtract p q).2
  zero : ∀ p, B.zeroAlloc p ≤ (B.zero p).2

theorem lookupCost_allocations (B : Backend n) (hb : BackendAllocationBound B)
    (cs : CacheV n) (q : KeyV n) :
    (lookupCost B cs q).allocations ≤ 8 * (lookupCost B cs q).work := by
  induction cs with
  | nil => simp [lookupCost]
  | cons e cs ih =>
    have h := hb.keyEq e.1 q
    simp only [lookupCost]
    split <;> simp_all [addWork, addEvents] <;> omega

theorem filterCost_allocations (B : Backend n) (hb : BackendAllocationBound B)
    (cs : CacheV n) (q : KeyV n) :
    (filterCost B cs q).allocations ≤ 8 * (filterCost B cs q).work := by
  induction cs with
  | nil => simp [filterCost]
  | cons e cs ih =>
    have h := hb.keyEq e.1 q
    simp only [filterCost]
    split <;> omega

theorem insertCost_allocations (B : Backend n) (hb : BackendAllocationBound B)
    (cs : CacheV n) (q : KeyV n) (a : AnswerV n) :
    (insertCost B cs q a).allocations ≤ 8 * (insertCost B cs q a).work := by
  have h := filterCost_allocations B hb cs q
  simp only [insertCost]
  omega

theorem scanCost_allocations (B : Backend n) (hb : BackendAllocationBound B)
    (solve : Vector ℕ n → CacheV n → Run (AnswerV n × CacheV n))
    (hsolve : ∀ r cs, (solve r cs).allocations ≤ 8 * (solve r cs).work)
    (r : Vector ℕ n) (ps : List (Vector ℕ n)) (cs : CacheV n) :
    (scanCost B solve r ps cs).allocations ≤ 8 * (scanCost B solve r ps cs).work := by
  induction ps generalizing cs with
  | nil => simp [scanCost]
  | cons p ps ih =>
    have hg := hb.guard p r
    have hd := hb.subtract r p
    have ho := hsolve (B.subtract r p).1 cs
    have ht := ih (solve (B.subtract r p).1 cs).value.2
    have ht' := ih cs
    simp only [scanCost]
    split
    · cases hs : (solve (B.subtract r p).1 cs).value.1 <;>
        simp [addWork, addEvents] <;> omega
    · simp only [addWork, addEvents]
      omega

theorem memoCost_allocations (B : Backend n) (hb : BackendAllocationBound B)
    (ps : List (Vector ℕ n)) (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) :
    (memoCost B ps k r cs).allocations ≤ 8 * (memoCost B ps k r cs).work := by
  induction k generalizing r cs with
  | zero =>
    have hl := lookupCost_allocations B hb cs (0, r)
    have hz := hb.zero r
    have hi := insertCost_allocations B hb cs (0, r)
      (if (B.zero r).1 then some [] else none)
    simp only [memoCost]
    split
    · simp_all
      omega
    · split_ifs <;> simp_all <;> omega
  | succ k ih =>
    have hl := lookupCost_allocations B hb cs (k + 1, r)
    have hs := scanCost_allocations B hb (memoCost B ps k) ih r ps cs
    have hi := insertCost_allocations B hb
      (scanCost B (memoCost B ps k) r ps cs).value.2 (k + 1, r)
      (scanCost B (memoCost B ps k) r ps cs).value.1
    simp only [memoCost]
    split <;> simp_all <;> omega

end UAVProof.TreeBudgetSearchAllocations

#print axioms UAVProof.TreeBudgetSearchAllocations.BackendAllocationBound
#print axioms UAVProof.TreeBudgetSearchAllocations.lookupCost_allocations
#print axioms UAVProof.TreeBudgetSearchAllocations.filterCost_allocations
#print axioms UAVProof.TreeBudgetSearchAllocations.insertCost_allocations
#print axioms UAVProof.TreeBudgetSearchAllocations.scanCost_allocations
#print axioms UAVProof.TreeBudgetSearchAllocations.memoCost_allocations
