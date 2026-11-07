import LeanCompletion.UAV.TreeBudgetAllocationBounds
import LeanCompletion.UAV.TreeBudgetBitMachine

/-! Concrete immutable blocks in an append-only store. Bit words and reference
arrays have distinct decoding relations. Reads and copies below actually use
the store; prior representations persist after allocation. The addressed cell
reader traverses its own address. This is a storage layer, not yet a simulation
of the full search, and no whole-program machine-time conclusion is claimed. -/
namespace UAVProof.TreeBudgetTypedStore
open TreeBudgetAllocationBounds TreeBudgetBitMachine

structure Block where
  base : ℕ
  length : ℕ
  deriving DecidableEq

def Represents (heap : Heap) (b : Block) (slots : List Slot) : Prop :=
  b.base + b.length ≤ heap.size ∧ b.length = slots.length ∧
    ∀ i (hi : i < slots.length), read heap (b.base + i) = some slots[i]

def WordRep (heap : Heap) (b : Block) (bits : List Bool) : Prop :=
  Represents heap b (bits.map Slot.bit)

def RefArrayRep (heap : Heap) (b : Block) (addresses : List ℕ) : Prop :=
  Represents heap b (addresses.map Slot.ref)

def allocateTyped (heap : Heap) (slots : List Slot) : Block × Heap :=
  (⟨heap.size, slots.length⟩, allocateBlock heap slots)

theorem allocateBlock_toList (heap : Heap) (slots : List Slot) :
    (allocateBlock heap slots).toList = heap.toList ++ slots := by
  induction slots generalizing heap with
  | nil => simp [allocateBlock]
  | cons slot slots ih => simp [allocateBlock, ih, allocate, List.append_assoc]

theorem read_allocateBlock_new (heap : Heap) (slots : List Slot) (i : ℕ)
    (hi : i < slots.length) :
    read (allocateBlock heap slots) (heap.size + i) = some slots[i] := by
  unfold TreeBudgetAllocationBounds.read
  rw [← Array.getElem?_toList, allocateBlock_toList,
    List.getElem?_append_right (by simp)]
  simp [hi]

theorem allocateTyped_represents (heap : Heap) (slots : List Slot) :
    Represents (allocateTyped heap slots).2 (allocateTyped heap slots).1 slots := by
  refine ⟨?_, rfl, ?_⟩
  · simp [allocateTyped, allocateBlock_size]
  · exact read_allocateBlock_new heap slots

theorem represents_persist (heap : Heap) (b : Block) (slots extra : List Slot)
    (h : Represents heap b slots) : Represents (allocateBlock heap extra) b slots := by
  refine ⟨h.1.trans ?_, h.2.1, ?_⟩
  · simp [allocateBlock_size]
  · intro i hi
    have hb := h.1
    have hl := h.2.1
    rw [read_allocateBlock_old heap extra (b.base + i) (by omega)]
    exact h.2.2 i hi

theorem wellFormed_allocateBlock (heap : Heap) (slots : List Slot)
    (hh : WellFormed heap) (hs : ∀ a, Slot.ref a ∈ slots → a < heap.size) :
    WellFormed (allocateBlock heap slots) := by
  induction slots generalizing heap with
  | nil => exact hh
  | cons slot slots ih =>
    apply ih
    · apply wellFormed_allocate heap slot hh
      intro a ha
      exact hs a (by simp [← ha])
    · intro a ha
      have h := hs a (by simp [ha])
      rw [allocate_size]
      omega

def readSlots (heap : Heap) : ℕ → ℕ → Option (List Slot)
  | _, 0 => some []
  | base, count + 1 => do
      let slot ← read heap base
      let tail ← readSlots heap (base + 1) count
      pure (slot :: tail)

theorem readSlots_correct (heap : Heap) (base : ℕ) (slots : List Slot)
    (h : ∀ i (hi : i < slots.length), read heap (base + i) = some slots[i]) :
    readSlots heap base slots.length = some slots := by
  induction slots generalizing base with
  | nil => rfl
  | cons slot slots ih =>
    have hh : read heap base = some slot := by simpa using h 0 (by simp)
    have ht : ∀ i (hi : i < slots.length),
        read heap ((base + 1) + i) = some slots[i] := by
      intro i hi
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        h (i + 1) (by simpa using hi)
    simp [readSlots, hh, ih _ ht]

def decodeWord : List Slot → Option (List Bool)
  | [] => some []
  | .bit bit :: slots => (decodeWord slots).map (bit :: ·)
  | .ref _ :: _ => none

def decodeRefs : List Slot → Option (List ℕ)
  | [] => some []
  | .ref address :: slots => (decodeRefs slots).map (address :: ·)
  | .bit _ :: _ => none

@[simp] theorem decodeWord_map (bits : List Bool) :
    decodeWord (bits.map Slot.bit) = some bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [decodeWord, ih]

@[simp] theorem decodeRefs_map (addresses : List ℕ) :
    decodeRefs (addresses.map Slot.ref) = some addresses := by
  induction addresses with
  | nil => rfl
  | cons a addresses ih => simp [decodeRefs, ih]

def readWord (heap : Heap) (b : Block) : Option (List Bool) :=
  (readSlots heap b.base b.length).bind decodeWord

def readRefArray (heap : Heap) (b : Block) : Option (List ℕ) :=
  (readSlots heap b.base b.length).bind decodeRefs

theorem readWord_correct (heap : Heap) (b : Block) (bits : List Bool)
    (h : WordRep heap b bits) : readWord heap b = some bits := by
  rw [readWord, h.2.1, readSlots_correct heap b.base _ h.2.2]
  simp

theorem readRefArray_correct (heap : Heap) (b : Block) (addresses : List ℕ)
    (h : RefArrayRep heap b addresses) : readRefArray heap b = some addresses := by
  rw [readRefArray, h.2.1, readSlots_correct heap b.base _ h.2.2]
  simp

theorem refArray_valid_addresses (heap : Heap) (b : Block) (addresses : List ℕ)
    (hh : WellFormed heap) (hr : RefArrayRep heap b addresses) :
    ∀ a ∈ addresses, a < heap.size := by
  intro a ha
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
  have hread := hr.2.2 i (by simpa using hi)
  simp only [List.getElem_map, he] at hread
  have haddr := hh (b.base + i) a hread
  have hlen := hr.2.1
  have hbound := hr.1
  simp only [List.length_map] at hlen
  omega

def allocateWord (heap : Heap) (bits : List Bool) : Block × Heap :=
  allocateTyped heap (bits.map Slot.bit)

def allocateRefs (heap : Heap) (addresses : List ℕ) : Block × Heap :=
  allocateTyped heap (addresses.map Slot.ref)

theorem allocateWord_correct (heap : Heap) (bits : List Bool) :
    WordRep (allocateWord heap bits).2 (allocateWord heap bits).1 bits :=
  allocateTyped_represents heap (bits.map Slot.bit)

theorem allocateRefs_correct (heap : Heap) (addresses : List ℕ) :
    RefArrayRep (allocateRefs heap addresses).2 (allocateRefs heap addresses).1 addresses :=
  allocateTyped_represents heap (addresses.map Slot.ref)

theorem allocateWord_wellFormed (heap : Heap) (bits : List Bool) (hh : WellFormed heap) :
    WellFormed (allocateWord heap bits).2 := by
  apply wellFormed_allocateBlock heap _ hh
  intro a ha
  simp at ha

theorem allocateRefs_wellFormed (heap : Heap) (addresses : List ℕ)
    (hh : WellFormed heap) (ha : ∀ a ∈ addresses, a < heap.size) :
    WellFormed (allocateRefs heap addresses).2 := by
  apply wellFormed_allocateBlock heap _ hh
  intro a h
  exact ha a (by simpa using h)

/-- Copying first reads each old slot, then appends freshly allocated cells. -/
def copyBlock (heap : Heap) (b : Block) : Option (Block × Heap) := do
  let slots ← readSlots heap b.base b.length
  pure (allocateTyped heap slots)

theorem copyBlock_correct (heap : Heap) (b : Block) (slots : List Slot)
    (h : Represents heap b slots) :
    copyBlock heap b = some (allocateTyped heap slots) ∧
      Represents (allocateTyped heap slots).2 (allocateTyped heap slots).1 slots ∧
      Represents (allocateTyped heap slots).2 b slots := by
  refine ⟨?_, allocateTyped_represents heap slots, represents_persist heap b slots slots h⟩
  rw [copyBlock, h.2.1, readSlots_correct heap b.base slots h.2.2]
  rfl

theorem represented_refs_valid (heap : Heap) (b : Block) (slots : List Slot)
    (hh : WellFormed heap) (hr : Represents heap b slots) :
    ∀ a, Slot.ref a ∈ slots → a < heap.size := by
  intro a ha
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
  have hread := hr.2.2 i hi
  rw [he] at hread
  have ht := hh (b.base + i) a hread
  have hb := hr.1
  have hl := hr.2.1
  omega

theorem copyBlock_wellFormed (heap : Heap) (b : Block) (slots : List Slot)
    (hh : WellFormed heap) (hr : Represents heap b slots) :
    WellFormed (allocateTyped heap slots).2 :=
  wellFormed_allocateBlock heap slots hh (represented_refs_valid heap b slots hh hr)

theorem allocateTyped_size (heap : Heap) (slots : List Slot) :
    (allocateTyped heap slots).2.size = heap.size + slots.length :=
  allocateBlock_size heap slots

/-- The address traversal is invoked at this actual slot lookup. A reference
slot holds an address word; loading that payload bit by bit is a separate
operation. The fit premise here concerns the selected slot's own address. -/
def readCell (width : ℕ) (heap : Heap) (address : ℕ) : Costed (Option Slot) :=
  let decoded := readAddress width address
  ⟨read heap decoded.value, decoded.steps + 1, 0⟩

theorem readCell_value (width : ℕ) (heap : Heap) (address : ℕ)
    (h : address < 2 ^ width) : (readCell width heap address).value = read heap address := by
  simp [readCell, readAddress_value width address h]

theorem readCell_steps (width : ℕ) (heap : Heap) (address : ℕ) :
    (readCell width heap address).steps = 2 * width + 2 := by simp [readCell]

/-- Semantic heap growth: existing slots retain their exact contents. -/
structure Extends (before after : Heap) : Prop where
  size_le : before.size ≤ after.size
  read_old : ∀ address, address < before.size → read after address = read before address

theorem extends_refl (heap : Heap) : Extends heap heap := ⟨le_rfl, fun _ _ => rfl⟩

theorem extends_trans {a b c : Heap} (hab : Extends a b) (hbc : Extends b c) : Extends a c := by
  refine ⟨hab.size_le.trans hbc.size_le, ?_⟩
  intro address ha
  exact (hbc.read_old address (ha.trans_le hab.size_le)).trans (hab.read_old address ha)

theorem allocateBlock_extends (heap : Heap) (slots : List Slot) :
    Extends heap (allocateBlock heap slots) := by
  refine ⟨?_, fun address h => read_allocateBlock_old heap slots address h⟩
  simp [allocateBlock_size]

theorem represents_of_extends {before after : Heap} (he : Extends before after)
    (b : Block) (slots : List Slot) (hr : Represents before b slots) :
    Represents after b slots := by
  refine ⟨hr.1.trans he.size_le, hr.2.1, ?_⟩
  intro i hi
  have hb := hr.1
  have hl := hr.2.1
  rw [he.read_old (b.base + i) (by omega)]
  exact hr.2.2 i hi

end UAVProof.TreeBudgetTypedStore

#print axioms UAVProof.TreeBudgetTypedStore.Block
#print axioms UAVProof.TreeBudgetTypedStore.Represents
#print axioms UAVProof.TreeBudgetTypedStore.WordRep
#print axioms UAVProof.TreeBudgetTypedStore.RefArrayRep
#print axioms UAVProof.TreeBudgetTypedStore.allocateTyped
#print axioms UAVProof.TreeBudgetTypedStore.allocateBlock_toList
#print axioms UAVProof.TreeBudgetTypedStore.read_allocateBlock_new
#print axioms UAVProof.TreeBudgetTypedStore.allocateTyped_represents
#print axioms UAVProof.TreeBudgetTypedStore.represents_persist
#print axioms UAVProof.TreeBudgetTypedStore.wellFormed_allocateBlock
#print axioms UAVProof.TreeBudgetTypedStore.readSlots
#print axioms UAVProof.TreeBudgetTypedStore.readSlots_correct
#print axioms UAVProof.TreeBudgetTypedStore.decodeWord
#print axioms UAVProof.TreeBudgetTypedStore.decodeRefs
#print axioms UAVProof.TreeBudgetTypedStore.decodeWord_map
#print axioms UAVProof.TreeBudgetTypedStore.decodeRefs_map
#print axioms UAVProof.TreeBudgetTypedStore.readWord
#print axioms UAVProof.TreeBudgetTypedStore.readRefArray
#print axioms UAVProof.TreeBudgetTypedStore.readWord_correct
#print axioms UAVProof.TreeBudgetTypedStore.readRefArray_correct
#print axioms UAVProof.TreeBudgetTypedStore.refArray_valid_addresses
#print axioms UAVProof.TreeBudgetTypedStore.allocateWord
#print axioms UAVProof.TreeBudgetTypedStore.allocateRefs
#print axioms UAVProof.TreeBudgetTypedStore.allocateWord_correct
#print axioms UAVProof.TreeBudgetTypedStore.allocateRefs_correct
#print axioms UAVProof.TreeBudgetTypedStore.allocateWord_wellFormed
#print axioms UAVProof.TreeBudgetTypedStore.allocateRefs_wellFormed
#print axioms UAVProof.TreeBudgetTypedStore.copyBlock
#print axioms UAVProof.TreeBudgetTypedStore.copyBlock_correct
#print axioms UAVProof.TreeBudgetTypedStore.represented_refs_valid
#print axioms UAVProof.TreeBudgetTypedStore.copyBlock_wellFormed
#print axioms UAVProof.TreeBudgetTypedStore.allocateTyped_size
#print axioms UAVProof.TreeBudgetTypedStore.readCell
#print axioms UAVProof.TreeBudgetTypedStore.readCell_value
#print axioms UAVProof.TreeBudgetTypedStore.readCell_steps
#print axioms UAVProof.TreeBudgetTypedStore.Extends
#print axioms UAVProof.TreeBudgetTypedStore.extends_refl
#print axioms UAVProof.TreeBudgetTypedStore.extends_trans
#print axioms UAVProof.TreeBudgetTypedStore.allocateBlock_extends
#print axioms UAVProof.TreeBudgetTypedStore.represents_of_extends
