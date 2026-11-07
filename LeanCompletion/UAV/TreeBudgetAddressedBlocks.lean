import LeanCompletion.UAV.TreeBudgetTypedStore
import LeanCompletion.UAV.TreeBudgetBitPrimitives

/-! Addressed immutable blocks. A reference slot contains an address word;
loading or writing that payload traverses its bits. The decoded access address
selects the actual array slot. Heap sizes count typed slots, not payload bits.
This module supplies concrete block operations, not an evaluator simulation. -/
namespace UAVProof.TreeBudgetAddressedBlocks
open TreeBudgetAllocationBounds TreeBudgetTypedStore TreeBudgetBitMachine TreeBudgetBitPrimitives

/-- Transfer each payload bit into a word buffer: read, advance, and write.
The buffer is part of the selected typed slot/control register; it does not
allocate a separate heap slot for every bit of a reference word. -/
def transferAddress : ℕ → ℕ → Costed ℕ
  | 0, _ => ⟨0, 1, 0⟩
  | width + 1, address =>
    let out := transferAddress width (address / 2)
    ⟨address % 2 + 2 * out.value, out.steps + 3, 0⟩

theorem transferAddress_value (width address : ℕ) (h : address < 2 ^ width) :
    (transferAddress width address).value = address := by
  induction width generalizing address with
  | zero => simp [transferAddress]; omega
  | succ width ih =>
    have ht : address / 2 < 2 ^ width := by rw [pow_succ] at h; omega
    simp only [transferAddress, ih _ ht]
    exact Nat.mod_add_div address 2

@[simp] theorem transferAddress_steps (width address : ℕ) :
    (transferAddress width address).steps = 3 * width + 1 := by
  induction width generalizing address with
  | zero => rfl
  | succ width ih => simp [transferAddress, ih]; omega

def copySlotD (width : ℕ) : Slot → Costed Slot
  | .bit bit => ⟨.bit bit, 1, 0⟩
  | .ref address =>
    let out := transferAddress width address
    ⟨.ref out.value, out.steps + 1, 0⟩

theorem copySlotD_value (width : ℕ) (slot : Slot)
    (h : ∀ a, slot = .ref a → a < 2 ^ width) : (copySlotD width slot).value = slot := by
  cases slot with
  | bit b => rfl
  | ref a => simp [copySlotD, transferAddress_value width a (h a rfl)]

theorem copySlotD_steps (width : ℕ) (slot : Slot) :
    (copySlotD width slot).steps ≤ 3 * width + 2 := by
  cases slot <;> simp [copySlotD]

@[simp] theorem copySlotD_allocations (width : ℕ) (slot : Slot) :
    (copySlotD width slot).allocations = 0 := by cases slot <;> rfl

def readCellD (width : ℕ) (heap : Heap) (address : ℕ) : Costed (Option Slot) :=
  let selected := readCell width heap address
  match selected.value with
  | none => ⟨none, selected.steps + 1, 0⟩
  | some slot =>
    let out := copySlotD width slot
    ⟨some out.value, selected.steps + out.steps + 1, 0⟩

theorem readCellD_value (width : ℕ) (heap : Heap) (address : ℕ)
    (hh : WellFormed heap) (ha : address < 2 ^ width) :
    (readCellD width heap address).value = read heap address := by
  simp only [readCellD, readCell_value width heap address ha]
  cases hs : read heap address with
  | none => rfl
  | some slot =>
    have hf : ∀ a, slot = .ref a → a < 2 ^ width := by
      intro a he
      subst slot
      exact (hh address a hs).trans ha
    simp [copySlotD_value width slot hf]

theorem readCellD_steps (width : ℕ) (heap : Heap) (address : ℕ) :
    (readCellD width heap address).steps ≤ 6 * width + 8 := by
  have hs := readCell_steps width heap address
  simp only [readCellD]
  cases h : (readCell width heap address).value with
  | none => dsimp only; omega
  | some slot =>
    have hp := copySlotD_steps width slot
    dsimp only
    omega

@[simp] theorem readCellD_allocations (width : ℕ) (heap : Heap) (address : ℕ) :
    (readCellD width heap address).allocations = 0 := by
  simp only [readCellD]
  cases (readCell width heap address).value <;> rfl

theorem size_le_width_succ (width a : ℕ) (h : a ≤ 2 ^ width) : a.size ≤ width + 1 := by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hp : 0 < 2 ^ width := by positivity
  omega

def readBlockD (width : ℕ) (heap : Heap) (base count : ℕ) : Costed (Option (List Slot)) :=
  let test := zeroNatD count
  if hzero : test.value then ⟨some [], test.steps + 1, test.allocations⟩ else
    let head := readCellD width heap base
    match head.value with
    | none => ⟨none, test.steps + head.steps + 2, test.allocations⟩
    | some slot =>
      let next := addNatD base 1
      let dec := subNatD count 1
      let tail := readBlockD width heap next.value dec.value
      ⟨tail.value.map (slot :: ·), test.steps + head.steps + next.steps + dec.steps + tail.steps + 4,
        test.allocations + next.allocations + dec.allocations + tail.allocations + 1⟩
termination_by count
decreasing_by
  simp_wf
  have hz : count ≠ 0 := by simpa only [test, zeroNatD_value, decide_eq_true_eq] using hzero
  omega

theorem readBlockD_zero (width : ℕ) (heap : Heap) (base : ℕ) :
    readBlockD width heap base 0 =
      ⟨some [], (zeroNatD 0).steps + 1, (zeroNatD 0).allocations⟩ := by
  rw [readBlockD]
  simp only [zeroNatD_value]
  rfl

theorem readBlockD_succ (width : ℕ) (heap : Heap) (base count : ℕ) :
    readBlockD width heap base (count + 1) =
      match (readCellD width heap base).value with
      | none => ⟨none, (zeroNatD (count + 1)).steps + (readCellD width heap base).steps + 2,
          (zeroNatD (count + 1)).allocations⟩
      | some slot =>
        ⟨(readBlockD width heap (base + 1) count).value.map (slot :: ·),
          (zeroNatD (count + 1)).steps + (readCellD width heap base).steps +
            (addNatD base 1).steps + (subNatD (count + 1) 1).steps +
            (readBlockD width heap (base + 1) count).steps + 4,
          (zeroNatD (count + 1)).allocations + (addNatD base 1).allocations +
            (subNatD (count + 1) 1).allocations +
            (readBlockD width heap (base + 1) count).allocations + 1⟩ := by
  rw [readBlockD]
  simp only [zeroNatD_value, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, decide_false,
    Bool.false_eq_true, ↓reduceDIte, addNatD_value, subNatD_value, Nat.add_sub_cancel]

theorem readBlockD_value (width : ℕ) (heap : Heap) (base count : ℕ)
    (hh : WellFormed heap) (hfit : base + count ≤ 2 ^ width) :
    (readBlockD width heap base count).value = readSlots heap base count := by
  induction count generalizing base with
  | zero => rw [readBlockD_zero]; rfl
  | succ count ih =>
    have ha : base < 2 ^ width := by omega
    have ht : base + 1 + count ≤ 2 ^ width := by omega
    rw [readBlockD_succ, readCellD_value width heap base hh ha]
    cases hs : read heap base with
    | none => simp [readSlots, hs]
    | some slot =>
      simp only [ih _ ht, readSlots, hs, Bind.bind, Option.bind_some]
      cases readSlots heap (base + 1) count <;> rfl

theorem readBlockD_steps (width : ℕ) (heap : Heap) (base count : ℕ)
    (hfit : base + count ≤ 2 ^ width) :
    (readBlockD width heap base count).steps ≤ 256 * (count + 1) * (width + 2) := by
  induction count generalizing base with
  | zero =>
    have hz := (dynamic_steps 0 0 (width + 1) (by simp) (by simp)).1
    change (zeroNatD 0).steps ≤ _ at hz
    rw [readBlockD_zero]
    dsimp only
    nlinarith
  | succ count ih =>
    have hb := size_le_width_succ width base (by omega)
    have hc := size_le_width_succ width (count + 1) (by omega)
    have hz := (dynamic_steps (count + 1) 0 (width + 1) hc (by simp)).1
    change (zeroNatD (count + 1)).steps ≤ _ at hz
    have hn := (dynamic_steps base 1 (width + 1) hb (by simp)).2.2.2
    have hd := (dynamic_steps (count + 1) 1 (width + 1) hc (by simp)).2.2.1
    have hh := readCellD_steps width heap base
    have ht := ih (base + 1) (by omega)
    rw [readBlockD_succ]
    cases (readCellD width heap base).value <;> dsimp only <;> nlinarith

theorem readBlockD_allocations_le_steps (width : ℕ) (heap : Heap) (base count : ℕ) :
    (readBlockD width heap base count).allocations ≤ (readBlockD width heap base count).steps := by
  induction count generalizing base with
  | zero =>
    have hz := (dynamic_allocations_le_steps 0 0).1
    change (zeroNatD 0).allocations ≤ (zeroNatD 0).steps at hz
    rw [readBlockD_zero]
    dsimp only
    omega
  | succ count ih =>
    have hz := (dynamic_allocations_le_steps (count + 1) 0).1
    change (zeroNatD (count + 1)).allocations ≤ (zeroNatD (count + 1)).steps at hz
    have hn := (dynamic_allocations_le_steps base 1).2.2.2
    have hd := (dynamic_allocations_le_steps (count + 1) 1).2.2.1
    have ht := ih (base + 1)
    rw [readBlockD_succ]
    cases (readCellD width heap base).value <;> dsimp only <;> omega

/-- Reserve an appended slot, then write at the address obtained by the actual
address scan. Under the fit premise this is exactly append-only allocation. -/
def allocateCellD (width : ℕ) (heap : Heap) (slot : Slot) : Costed (ℕ × Heap) :=
  let address := readAddress width heap.size
  let payload := copySlotD width slot
  ⟨(address.value, (heap.push (.bit false)).setIfInBounds address.value payload.value),
    address.steps + payload.steps + 2, 1⟩

theorem allocateCellD_value (width : ℕ) (heap : Heap) (slot : Slot)
    (ha : heap.size < 2 ^ width) (hs : ∀ a, slot = .ref a → a < 2 ^ width) :
    (allocateCellD width heap slot).value = allocate heap slot := by
  simp only [allocateCellD, readAddress_value width heap.size ha, copySlotD_value width slot hs]
  simp [allocate, Array.setIfInBounds_def, Array.set_push]

theorem allocateCellD_steps (width : ℕ) (heap : Heap) (slot : Slot) :
    (allocateCellD width heap slot).steps ≤ 6 * width + 8 := by
  have hp := copySlotD_steps width slot
  simp only [allocateCellD, readAddress_steps]
  omega

@[simp] theorem allocateCellD_allocations (width : ℕ) (heap : Heap) (slot : Slot) :
    (allocateCellD width heap slot).allocations = 1 := rfl

def allocateSlotsD (width : ℕ) (heap : Heap) : List Slot → Costed Heap
  | [] => ⟨heap, 1, 0⟩
  | slot :: slots =>
    let cell := allocateCellD width heap slot
    let tail := allocateSlotsD width cell.value.2 slots
    ⟨tail.value, cell.steps + tail.steps + 1, cell.allocations + tail.allocations⟩

theorem allocateSlotsD_value (width : ℕ) (heap : Heap) (slots : List Slot)
    (hfit : heap.size + slots.length ≤ 2 ^ width)
    (hs : ∀ a, Slot.ref a ∈ slots → a < 2 ^ width) :
    (allocateSlotsD width heap slots).value = allocateBlock heap slots := by
  induction slots generalizing heap with
  | nil => rfl
  | cons slot slots ih =>
    have ha : heap.size < 2 ^ width := by simp only [List.length_cons] at hfit; omega
    have hc : ∀ a, slot = .ref a → a < 2 ^ width := by
      intro a he
      exact hs a (by simp [he])
    have ht : (allocate heap slot).2.size + slots.length ≤ 2 ^ width := by
      simp only [allocate_size, List.length_cons] at *
      omega
    simp only [allocateSlotsD, allocateCellD_value width heap slot ha hc]
    exact ih _ ht (fun a h => hs a (by simp [h]))

theorem allocateSlotsD_steps (width : ℕ) (heap : Heap) (slots : List Slot) :
    (allocateSlotsD width heap slots).steps ≤ (slots.length + 1) * (6 * width + 10) := by
  induction slots generalizing heap with
  | nil => simp [allocateSlotsD]
  | cons slot slots ih =>
    have hc := allocateCellD_steps width heap slot
    have ht := ih (allocateCellD width heap slot).value.2
    simp only [allocateSlotsD, List.length_cons]
    nlinarith

@[simp] theorem allocateSlotsD_allocations (width : ℕ) (heap : Heap) (slots : List Slot) :
    (allocateSlotsD width heap slots).allocations = slots.length := by
  induction slots generalizing heap with
  | nil => rfl
  | cons slot slots ih => simp [allocateSlotsD, ih, Nat.add_comm]

theorem allocateSlotsD_allocations_le_steps (width : ℕ) (heap : Heap) (slots : List Slot) :
    (allocateSlotsD width heap slots).allocations ≤ (allocateSlotsD width heap slots).steps := by
  induction slots generalizing heap with
  | nil => simp [allocateSlotsD]
  | cons slot slots ih =>
    have ht := ih (allocateCellD width heap slot).value.2
    simp only [allocateSlotsD, allocateCellD_allocations]
    omega

def decodeWordD : List Slot → Costed (Option (List Bool))
  | [] => ⟨some [], 1, 0⟩
  | .ref _ :: _ => ⟨none, 1, 0⟩
  | .bit bit :: slots =>
    let out := decodeWordD slots
    ⟨out.value.map (bit :: ·), out.steps + 2, out.allocations + 1⟩

def decodeRefsD : List Slot → Costed (Option (List ℕ))
  | [] => ⟨some [], 1, 0⟩
  | .bit _ :: _ => ⟨none, 1, 0⟩
  | .ref address :: slots =>
    let out := decodeRefsD slots
    ⟨out.value.map (address :: ·), out.steps + 2, out.allocations + 1⟩

@[simp] theorem decodeWordD_value (slots : List Slot) :
    (decodeWordD slots).value = decodeWord slots := by
  induction slots with
  | nil => rfl
  | cons slot slots ih => cases slot <;> simp [decodeWordD, decodeWord, ih]

@[simp] theorem decodeRefsD_value (slots : List Slot) :
    (decodeRefsD slots).value = decodeRefs slots := by
  induction slots with
  | nil => rfl
  | cons slot slots ih => cases slot <;> simp [decodeRefsD, decodeRefs, ih]

theorem decodeWordD_steps (slots : List Slot) :
    (decodeWordD slots).steps ≤ 3 * (slots.length + 1) := by
  induction slots with
  | nil => simp [decodeWordD]
  | cons slot slots ih => cases slot <;> simp only [decodeWordD, List.length_cons] <;> omega

theorem decodeRefsD_steps (slots : List Slot) :
    (decodeRefsD slots).steps ≤ 3 * (slots.length + 1) := by
  induction slots with
  | nil => simp [decodeRefsD]
  | cons slot slots ih => cases slot <;> simp only [decodeRefsD, List.length_cons] <;> omega

theorem decodeWordD_allocations_le_steps (slots : List Slot) :
    (decodeWordD slots).allocations ≤ (decodeWordD slots).steps := by
  induction slots with
  | nil => simp [decodeWordD]
  | cons slot slots ih => cases slot <;> simp only [decodeWordD] <;> omega

theorem decodeRefsD_allocations_le_steps (slots : List Slot) :
    (decodeRefsD slots).allocations ≤ (decodeRefsD slots).steps := by
  induction slots with
  | nil => simp [decodeRefsD]
  | cons slot slots ih => cases slot <;> simp only [decodeRefsD] <;> omega

def readWordD (width : ℕ) (heap : Heap) (b : Block) : Costed (Option (List Bool)) :=
  let slots := readBlockD width heap b.base b.length
  match slots.value with
  | none => ⟨none, slots.steps + 1, slots.allocations⟩
  | some values =>
    let out := decodeWordD values
    ⟨out.value, slots.steps + out.steps + 1, slots.allocations + out.allocations⟩

def readRefsD (width : ℕ) (heap : Heap) (b : Block) : Costed (Option (List ℕ)) :=
  let slots := readBlockD width heap b.base b.length
  match slots.value with
  | none => ⟨none, slots.steps + 1, slots.allocations⟩
  | some values =>
    let out := decodeRefsD values
    ⟨out.value, slots.steps + out.steps + 1, slots.allocations + out.allocations⟩

theorem readBlockD_correct (width : ℕ) (heap : Heap) (b : Block) (slots : List Slot)
    (hh : WellFormed heap) (hsize : heap.size ≤ 2 ^ width) (hr : Represents heap b slots) :
    (readBlockD width heap b.base b.length).value = some slots := by
  rw [readBlockD_value width heap b.base b.length hh (hr.1.trans hsize), hr.2.1]
  exact readSlots_correct heap b.base slots hr.2.2

theorem readWordD_correct (width : ℕ) (heap : Heap) (b : Block) (bits : List Bool)
    (hh : WellFormed heap) (hsize : heap.size ≤ 2 ^ width) (hr : WordRep heap b bits) :
    (readWordD width heap b).value = some bits := by
  simp only [readWordD, readBlockD_correct width heap b _ hh hsize hr]
  simp

theorem readRefsD_correct (width : ℕ) (heap : Heap) (b : Block) (refs : List ℕ)
    (hh : WellFormed heap) (hsize : heap.size ≤ 2 ^ width) (hr : RefArrayRep heap b refs) :
    (readRefsD width heap b).value = some refs := by
  simp only [readRefsD, readBlockD_correct width heap b _ hh hsize hr]
  simp

theorem readWordD_steps (width : ℕ) (heap : Heap) (b : Block) (bits : List Bool)
    (hh : WellFormed heap) (hsize : heap.size ≤ 2 ^ width) (hr : WordRep heap b bits) :
    (readWordD width heap b).steps ≤ 512 * (b.length + 1) * (width + 2) := by
  have hb := readBlockD_steps width heap b.base b.length (hr.1.trans hsize)
  have hd := decodeWordD_steps (bits.map Slot.bit)
  have hl : b.length = bits.length := by simpa using hr.2.1
  simp only [List.length_map] at hd
  simp only [readWordD, readBlockD_correct width heap b _ hh hsize hr]
  nlinarith

theorem readRefsD_steps (width : ℕ) (heap : Heap) (b : Block) (refs : List ℕ)
    (hh : WellFormed heap) (hsize : heap.size ≤ 2 ^ width) (hr : RefArrayRep heap b refs) :
    (readRefsD width heap b).steps ≤ 512 * (b.length + 1) * (width + 2) := by
  have hb := readBlockD_steps width heap b.base b.length (hr.1.trans hsize)
  have hd := decodeRefsD_steps (refs.map Slot.ref)
  have hl : b.length = refs.length := by simpa using hr.2.1
  simp only [List.length_map] at hd
  simp only [readRefsD, readBlockD_correct width heap b _ hh hsize hr]
  nlinarith

theorem readWordD_allocations_le_steps (width : ℕ) (heap : Heap) (b : Block) :
    (readWordD width heap b).allocations ≤ (readWordD width heap b).steps := by
  have hb := readBlockD_allocations_le_steps width heap b.base b.length
  simp only [readWordD]
  cases (readBlockD width heap b.base b.length).value with
  | none => dsimp only; omega
  | some slots =>
    have hd := decodeWordD_allocations_le_steps slots
    dsimp only
    omega

theorem readRefsD_allocations_le_steps (width : ℕ) (heap : Heap) (b : Block) :
    (readRefsD width heap b).allocations ≤ (readRefsD width heap b).steps := by
  have hb := readBlockD_allocations_le_steps width heap b.base b.length
  simp only [readRefsD]
  cases (readBlockD width heap b.base b.length).value with
  | none => dsimp only; omega
  | some slots =>
    have hd := decodeRefsD_allocations_le_steps slots
    dsimp only
    omega

def copyBlockD (width : ℕ) (heap : Heap) (b : Block) : Costed (Option (Block × Heap)) :=
  let slots := readBlockD width heap b.base b.length
  match slots.value with
  | none => ⟨none, slots.steps + 1, slots.allocations⟩
  | some values =>
    let base := readAddress width heap.size
    let len := addNatD b.length 0
    let out := allocateSlotsD width heap values
    ⟨some (⟨base.value, len.value⟩, out.value),
      slots.steps + base.steps + len.steps + out.steps + 3,
      slots.allocations + len.allocations + out.allocations + 2⟩

theorem copyBlockD_value (width : ℕ) (heap : Heap) (b : Block) (slots : List Slot)
    (hh : WellFormed heap) (hr : Represents heap b slots)
    (hroom : heap.size + b.length < 2 ^ width) :
    (copyBlockD width heap b).value = some (allocateTyped heap slots) := by
  have hsize : heap.size ≤ 2 ^ width := by omega
  have ha : heap.size < 2 ^ width := by omega
  have hfit : heap.size + slots.length ≤ 2 ^ width := by rw [← hr.2.1]; omega
  have hs : ∀ a, Slot.ref a ∈ slots → a < 2 ^ width := by
    intro a hm
    exact (represented_refs_valid heap b slots hh hr a hm).trans ha
  simp only [copyBlockD, readBlockD_correct width heap b slots hh hsize hr,
    readAddress_value width heap.size ha, addNatD_value, Nat.add_zero,
    allocateSlotsD_value width heap slots hfit hs]
  rw [hr.2.1]
  rfl

theorem copyBlockD_steps (width : ℕ) (heap : Heap) (b : Block) (slots : List Slot)
    (hh : WellFormed heap) (hr : Represents heap b slots)
    (hroom : heap.size + b.length < 2 ^ width) :
    (copyBlockD width heap b).steps ≤ 1024 * (b.length + 1) * (width + 2) := by
  have hsize : heap.size ≤ 2 ^ width := by omega
  have hb := readBlockD_steps width heap b.base b.length (hr.1.trans hsize)
  have hl := (dynamic_steps b.length 0 (width + 1)
    (size_le_width_succ width b.length (by omega)) (by simp)).2.2.2
  have ha := allocateSlotsD_steps width heap slots
  rw [← hr.2.1] at ha
  simp only [copyBlockD, readBlockD_correct width heap b slots hh hsize hr, readAddress_steps]
  nlinarith

theorem copyBlockD_allocations_le_steps (width : ℕ) (heap : Heap) (b : Block) :
    (copyBlockD width heap b).allocations ≤ (copyBlockD width heap b).steps := by
  have hb := readBlockD_allocations_le_steps width heap b.base b.length
  simp only [copyBlockD]
  cases h : (readBlockD width heap b.base b.length).value with
  | none => dsimp only; omega
  | some slots =>
    have hl := (dynamic_allocations_le_steps b.length 0).2.2.2
    have ha := allocateSlotsD_allocations_le_steps width heap slots
    dsimp only
    omega

theorem copyBlockD_correct (width : ℕ) (heap : Heap) (b : Block) (slots : List Slot)
    (hh : WellFormed heap) (hr : Represents heap b slots)
    (hroom : heap.size + b.length < 2 ^ width) :
    (copyBlockD width heap b).value = some (allocateTyped heap slots) ∧
      Represents (allocateTyped heap slots).2 (allocateTyped heap slots).1 slots ∧
      Represents (allocateTyped heap slots).2 b slots ∧
      WellFormed (allocateTyped heap slots).2 ∧
      Extends heap (allocateTyped heap slots).2 := by
  refine ⟨copyBlockD_value width heap b slots hh hr hroom, allocateTyped_represents heap slots,
    represents_persist heap b slots slots hr, ?_, allocateBlock_extends heap slots⟩
  exact wellFormed_allocateBlock heap slots hh (represented_refs_valid heap b slots hh hr)

theorem copyBlockD_preserves (width : ℕ) (heap : Heap) (b old : Block)
    (slots oldSlots : List Slot) (hh : WellFormed heap) (hr : Represents heap b slots)
    (hold : Represents heap old oldSlots) (hroom : heap.size + b.length < 2 ^ width) :
    ∃ fresh after, (copyBlockD width heap b).value = some (fresh, after) ∧
      Represents after fresh slots ∧ Represents after old oldSlots ∧
      after.size = heap.size + b.length := by
  refine ⟨(allocateTyped heap slots).1, (allocateTyped heap slots).2,
    copyBlockD_value width heap b slots hh hr hroom, allocateTyped_represents heap slots,
    represents_persist heap old oldSlots slots hold, ?_⟩
  simpa [hr.2.1] using allocateTyped_size heap slots

end UAVProof.TreeBudgetAddressedBlocks
