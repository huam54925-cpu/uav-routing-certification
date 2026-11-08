import LeanCompletion.UAV.TreeBudgetStoredAllocation

/-! Bounds for the costs recorded by the addressed allocator and accessors.
The width parameter bounds measured addresses/endpoints, not a global machine
capacity assumption. The execution-level derivation is a separate theorem. -/
namespace UAVProof.TreeBudgetStoredPrimitiveBounds
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec
open TreeBudgetAllocationBounds TreeBudgetAddressedBlocks TreeBudgetSharedAnswerStore
open TreeBudgetChargedCache TreeBudgetStoredAllocation

theorem load_steps (heap : Heap) (address : ℕ) :
    (load heap address).steps ≤ 9 * address.size + 10 := by
  have h := readCellD_steps address.size heap address
  simp only [load, (widthNat_spec address).1, (widthNat_spec address).2.1]
  omega

theorem load_allocations (heap : Heap) (address : ℕ) :
    (load heap address).allocations = address.size := by
  simp [load, (widthNat_spec address).2.2]

theorem load_allocations_le_steps (heap : Heap) (address : ℕ) :
    (load heap address).allocations ≤ (load heap address).steps := by
  rw [load_allocations]
  simp only [load, (widthNat_spec address).2.1]
  omega

theorem alloc_steps (heap : Heap) (slots : List Slot) (W : ℕ)
    (hw : (heap.size + slots.length).size ≤ W) :
    (alloc heap slots).steps ≤ 256 * (slots.length + 1) ^ 2 * (W + 2) := by
  have hh := (Nat.size_le_size (Nat.le_add_right heap.size slots.length)).trans hw
  have hl := (Nat.size_le_size (Nat.le_add_left slots.length heap.size)).trans hw
  have hlen := lengthD_steps slots
  have htop := (dynamic_steps heap.size slots.length W hh hl).2.2.2
  have hnode := nodeD_steps (heap.size + slots.length).size heap slots
  have hsq : slots.length + 1 ≤ (slots.length + 1) ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul hsq (show (heap.size + slots.length).size + 2 ≤ W + 2 by omega)
  simp only [alloc, lengthD_value, addNatD_value, (widthNat_spec _).1, (widthNat_spec _).2.1]
  nlinarith

theorem alloc_allocations_le_steps (heap : Heap) (slots : List Slot) :
    (alloc heap slots).allocations ≤ (alloc heap slots).steps := by
  have hl := lengthD_allocations_le_steps slots
  have ht := (dynamic_allocations_le_steps heap.size (lengthD slots).value).2.2.2
  have hn := allocateSlotsD_allocations_le_steps
    (widthNat (addNatD heap.size (lengthD slots).value).value).value heap slots
  have hw : (widthNat (addNatD heap.size (lengthD slots).value).value).allocations ≤
      (widthNat (addNatD heap.size (lengthD slots).value).value).steps := by
    rw [(widthNat_spec _).2.1, (widthNat_spec _).2.2]
    omega
  simp only [alloc, nodeD]
  omega

end UAVProof.TreeBudgetStoredPrimitiveBounds
