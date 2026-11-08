import LeanCompletion.UAV.TreeBudgetStoredPrimitiveBounds
import LeanCompletion.UAV.TreeBudgetCostedCandidates

/-! Composition rules for the actual recorded steps plus all allocation cells.
This quantity bounds steps and auxiliary workspace separately; it is not the
physical heap footprint. No abstract-search work field is used here. -/
namespace UAVProof.TreeBudgetStoredWork
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetCostedCandidates TreeBudgetAllocationBounds TreeBudgetAddressedBlocks
open TreeBudgetSharedAnswerStore TreeBudgetChargedCache TreeBudgetStoredCursor
open TreeBudgetStoredPrimitiveBounds TreeBudgetBinaryCodec TreeBudgetSearchStore

@[simp] theorem work_bind {α β : Type} (out : Costed α) (f : α → Costed β) :
    work (TreeBudgetBitMachine.bind out f) = work out + work (f out.value) := by
  simp [work, TreeBudgetBitMachine.bind]; omega

@[simp] theorem work_charge {α : Type} (s a : ℕ) (out : Costed α) :
    work (charge s a out) = s + a + work out := by simp [work, charge]; omega

@[simp] theorem work_ret {α : Type} (a : α) : work (ret a) = 1 := rfl
@[simp] theorem work_bad {α : Type} : work (bad : Costed (Option α)) = 1 := rfl

theorem work_then_some {α β : Type} (out : Costed (Option α)) (f : α → Costed (Option β))
    (x : α) (hx : out.value = some x) :
    work (thenD out f) = work out + work (f x) + 1 := by
  simp [thenD, hx, work]; omega

theorem work_then_le {α β : Type} (out : Costed (Option α)) (f : α → Costed (Option β))
    (B : ℕ) (hb : ∀ x, out.value = some x → work (f x) ≤ B) :
    work (thenD out f) ≤ work out + B + 1 := by
  cases hv : out.value with
  | none => simp [thenD, hv, work]; omega
  | some x => rw [work_then_some out f x hv]; exact Nat.add_le_add_right (Nat.add_le_add_left (hb x hv) _) 1

theorem work_then_uniform {α β : Type} (out : Costed (Option α))
    (f : α → Costed (Option β)) (A B : ℕ)
    (ha : work out ≤ A) (hb : ∀ x, work (f x) ≤ B) :
    work (thenD out f) ≤ A + B + 1 := by
  exact (work_then_le out f B (fun x _ => hb x)).trans (by omega)

theorem arithmetic_work (a b W : ℕ) (ha : a.size ≤ W) (hb : b.size ≤ W) :
    work (eqNatD a b) ≤ 72 * (W + 1) ∧
    work (subNatD a b) ≤ 72 * (W + 1) ∧ work (addNatD a b) ≤ 72 * (W + 1) := by
  have hs := dynamic_steps a b W ha hb
  have hw := dynamic_allocations a b W ha hb
  unfold work
  omega

theorem cursor_work (fuel W : ℕ) (hf : fuel.size ≤ W) (hw : 1 ≤ W) :
    work (cursorStep fuel) ≤ 144 * (W + 1) + 1 := by
  have hs := cursorStep_steps fuel W hf hw
  have ha := cursorStep_allocations fuel W hf hw
  unfold work
  omega

theorem load_work (heap : Heap) (address W : ℕ) (ha : address.size ≤ W) :
    work (load heap address) ≤ 10 * (W + 1) := by
  have hs := load_steps heap address
  rw [work, load_allocations]
  omega

theorem loadOffset_work (heap : Heap) (address offset W : ℕ)
    (ha : (address + offset).size ≤ W) :
    work (loadOffset heap address offset) ≤ 82 * (W + 1) := by
  have hh := (Nat.size_le_size (Nat.le_add_right address offset)).trans ha
  have ho := (Nat.size_le_size (Nat.le_add_left offset address)).trans ha
  have hsum := (arithmetic_work address offset W hh ho).2.2
  have hl := load_work heap (address + offset) W ha
  simp only [loadOffset, work_bind, addNatD_value]
  omega

theorem loadRef_work (heap : Heap) (address offset W : ℕ)
    (ha : (address + offset).size ≤ W) :
    work (loadRef heap address offset) ≤ 84 * (W + 1) := by
  have h := work_then_le (loadOffset heap address offset)
    (fun slot => match slot with | .ref r => ret r | .bit _ => bad) 1 (by
      intro slot hs; cases slot <;> simp)
  have hl := loadOffset_work heap address offset W ha
  change work (loadRef heap address offset) ≤ _ at h
  omega

theorem alloc_work (heap : Heap) (slots : List Slot) (W : ℕ)
    (hw : (heap.size + slots.length).size ≤ W) :
    work (alloc heap slots) ≤ 512 * (slots.length + 1) ^ 2 * (W + 2) := by
  have hs := alloc_steps heap slots W hw
  have ha := alloc_allocations_le_steps heap slots
  unfold work
  nlinarith only [hs, ha]

end UAVProof.TreeBudgetStoredWork
