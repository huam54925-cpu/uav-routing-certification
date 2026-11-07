import LeanCompletion.UAV.TreeBudgetBitLength

/-! Append-only reference-memory primitives and noncircular address bounds.
Slot counts are cardinalities of actual heap states. The search-to-heap
simulation and its allocation bound must be supplied separately before these
lemmas imply a bound for a search execution. No runtime heap claim is made. -/
namespace UAVProof.TreeBudgetAllocationBounds
open TreeBudgetBitLength

inductive Slot where
  | bit (value : Bool)
  | ref (address : ℕ)
  deriving DecidableEq

abbrev Heap := Array Slot

def allocate (heap : Heap) (slot : Slot) : ℕ × Heap := (heap.size, heap.push slot)

def read (heap : Heap) (address : ℕ) : Option Slot := heap[address]?

theorem allocate_size (heap : Heap) (slot : Slot) :
    (allocate heap slot).2.size = heap.size + 1 := by simp [allocate]

theorem read_allocate_new (heap : Heap) (slot : Slot) :
    read (allocate heap slot).2 (allocate heap slot).1 = some slot := by
  simp [read, allocate]

theorem read_allocate_old (heap : Heap) (slot : Slot) (address : ℕ)
    (h : address < heap.size) : read (allocate heap slot).2 address = read heap address := by
  simp [read, allocate, Array.getElem?_push, Nat.ne_of_lt h]

/-- Blocks are allocated by repeated single-slot allocation, with no deletion. -/
def allocateBlock (heap : Heap) : List Slot → Heap
  | [] => heap
  | slot :: tail => allocateBlock (allocate heap slot).2 tail

theorem allocateBlock_size (heap : Heap) (slots : List Slot) :
    (allocateBlock heap slots).size = heap.size + slots.length := by
  induction slots generalizing heap with
  | nil => simp [allocateBlock]
  | cons slot slots ih =>
    simp only [allocateBlock, ih, allocate_size, List.length_cons]
    omega

theorem read_allocateBlock_old (heap : Heap) (slots : List Slot) (address : ℕ)
    (h : address < heap.size) : read (allocateBlock heap slots) address = read heap address := by
  induction slots generalizing heap with
  | nil => rfl
  | cons slot slots ih =>
    rw [allocateBlock, ih _ (by simpa [allocate_size] using Nat.lt_succ_of_lt h)]
    exact read_allocate_old heap slot address h

/-- A reference always points to an earlier allocated slot, allowing immutable
sharing without cycles or dangling references. -/
def WellFormed (heap : Heap) : Prop :=
  ∀ i a, read heap i = some (.ref a) → a < i

theorem wellFormed_allocate (heap : Heap) (slot : Slot) (hheap : WellFormed heap)
    (hslot : ∀ a, slot = .ref a → a < heap.size) : WellFormed (allocate heap slot).2 := by
  intro i a hi
  by_cases he : i = heap.size
  · subst i
    have hs : slot = .ref a := by simpa [read, allocate] using hi
    exact hslot a hs
  · have hold : read heap i = some (.ref a) := by
      simpa [read, allocate, Array.getElem?_push, he] using hi
    exact hheap i a hold

theorem address_size_le_heap (heap : Heap) (address : ℕ) (h : address < heap.size) :
    Nat.size address ≤ Nat.size heap.size := Nat.size_le_size h.le

theorem size_pow_le (a k : ℕ) : Nat.size (a ^ k) ≤ k * Nat.size a + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h := size_mul_le (a ^ k) a
    simp only [Nat.succ_mul]
    omega

theorem size_le_self (a : ℕ) : Nat.size a ≤ a := Nat.size_le.mpr a.lt_two_pow_self

/-- This is an address lemma, with an explicit slot-count premise. It does
not supply that premise or identify an uninstantiated cost with machine time. -/
theorem address_width_of_slot_bound (N address K S M n B ell : ℕ)
    (ha : address < N)
    (hN : N ≤ K * S ^ 3 * (M + 1) * (n + 1) ^ 2 * (B + 1) ^ 2)
    (hS : Nat.size S ≤ 3 * ell + 1) (hM : Nat.size M ≤ 2 * ell)
    (hn : n ≤ ell) (hB : B ≤ 3 * ell + 4) :
    Nat.size address ≤ Nat.size K + 19 * ell + 26 := by
  have h₁ := size_mul_le K (S ^ 3)
  have h₂ := size_mul_le (K * S ^ 3) (M + 1)
  have h₃ := size_mul_le (K * S ^ 3 * (M + 1)) ((n + 1) ^ 2)
  have h₄ := size_mul_le (K * S ^ 3 * (M + 1) * (n + 1) ^ 2) ((B + 1) ^ 2)
  have hS' := size_pow_le S 3
  have hM' := size_add_le M 1
  have hn' := size_pow_le (n + 1) 2
  have hB' := size_pow_le (B + 1) 2
  have hn'' := size_le_self (n + 1)
  have hB'' := size_le_self (B + 1)
  have hfinal := Nat.size_le_size (ha.le.trans hN)
  norm_num at hM'
  omega

/-- Substituting the search's intrinsic-work estimate into eight slots per
intrinsic step gives this allocation envelope. It contains no address width. -/
def searchSlotBound (S n β : ℕ) : ℕ :=
  8 * ((1024 * (n + 1) * (β + 1) + 8) * 7 * (S + 1) ^ 3)

theorem searchSlotBound_le (S n β : ℕ) :
    searchSlotBound S n β ≤ 65536 * (n + 1) * (β + 1) * (S + 1) ^ 3 := by
  have hp : 0 < (n + 1) * (β + 1) := by positivity
  have hc : 8 * ((1024 * (n + 1) * (β + 1) + 8) * 7) ≤
      65536 * (n + 1) * (β + 1) := by nlinarith
  simpa only [searchSlotBound, ← Nat.mul_assoc] using
    Nat.mul_le_mul_right ((S + 1) ^ 3) hc

theorem size_searchSlotBound (S n β ell : ℕ)
    (hS : Nat.size S ≤ 3 * ell + 1) (hn : n ≤ ell) (hβ : β ≤ 6 * ell + 4) :
    Nat.size (searchSlotBound S n β) ≤ 16 * ell + 40 := by
  have h₁ := size_mul_le 65536 (n + 1)
  have h₂ := size_mul_le (65536 * (n + 1)) (β + 1)
  have h₃ := size_mul_le (65536 * (n + 1) * (β + 1)) ((S + 1) ^ 3)
  have h₄ := size_pow_le (S + 1) 3
  have h₅ := size_add_le S 1
  have h₆ := size_le_self (n + 1)
  have h₇ := size_le_self (β + 1)
  have hfinal := Nat.size_le_size (searchSlotBound_le S n β)
  have hconstant : Nat.size 65536 = 17 := by decide +kernel
  rw [hconstant] at h₁
  norm_num at h₅
  omega

/-- Allocation accounting is used first, and address charging only afterwards;
there is no assumption about the execution's final time in this lemma. -/
theorem search_address_width (N address initial S n β ell : ℕ)
    (ha : address < N) (hN : N ≤ initial + searchSlotBound S n β)
    (hi : Nat.size initial ≤ ell + 8) (hS : Nat.size S ≤ 3 * ell + 1)
    (hn : n ≤ ell) (hβ : β ≤ 6 * ell + 4) :
    Nat.size address ≤ 17 * ell + 49 := by
  have hs := size_searchSlotBound S n β ell hS hn hβ
  have hsum := size_add_le initial (searchSlotBound S n β)
  have hf := Nat.size_le_size (ha.le.trans hN)
  omega

end UAVProof.TreeBudgetAllocationBounds

#print axioms UAVProof.TreeBudgetAllocationBounds.Slot
#print axioms UAVProof.TreeBudgetAllocationBounds.Heap
#print axioms UAVProof.TreeBudgetAllocationBounds.allocate
#print axioms UAVProof.TreeBudgetAllocationBounds.read
#print axioms UAVProof.TreeBudgetAllocationBounds.allocate_size
#print axioms UAVProof.TreeBudgetAllocationBounds.read_allocate_new
#print axioms UAVProof.TreeBudgetAllocationBounds.read_allocate_old
#print axioms UAVProof.TreeBudgetAllocationBounds.allocateBlock
#print axioms UAVProof.TreeBudgetAllocationBounds.allocateBlock_size
#print axioms UAVProof.TreeBudgetAllocationBounds.read_allocateBlock_old
#print axioms UAVProof.TreeBudgetAllocationBounds.WellFormed
#print axioms UAVProof.TreeBudgetAllocationBounds.wellFormed_allocate
#print axioms UAVProof.TreeBudgetAllocationBounds.address_size_le_heap
#print axioms UAVProof.TreeBudgetAllocationBounds.size_pow_le
#print axioms UAVProof.TreeBudgetAllocationBounds.size_le_self
#print axioms UAVProof.TreeBudgetAllocationBounds.address_width_of_slot_bound
#print axioms UAVProof.TreeBudgetAllocationBounds.searchSlotBound
#print axioms UAVProof.TreeBudgetAllocationBounds.searchSlotBound_le
#print axioms UAVProof.TreeBudgetAllocationBounds.size_searchSlotBound
#print axioms UAVProof.TreeBudgetAllocationBounds.search_address_width
