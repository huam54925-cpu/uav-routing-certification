import LeanCompletion.UAV.TreeBudgetSearchStore
import LeanCompletion.UAV.TreeBudgetAddressedBlocks

/-! Shared immutable answers. Rows are borrowed encoded vectors; a cons allocates
three slots, irrespective of its tail. Failure and successful empty answers
have different outer tags. Addressed allocation has an explicit capacity
contract; removing that contract belongs to the whole-execution budget proof. -/
namespace UAVProof.TreeBudgetSharedAnswerStore
open TreeBudgetAllocationBounds TreeBudgetTypedStore TreeBudgetBitMachine
open TreeBudgetAddressedBlocks TreeBudgetSearchStore TreeBudgetBinaryCodec

abbrev RowRep (heap : Heap) (a : ℕ) (row : List ℕ) := BlobRep heap a (encodeNats row)

inductive RowsRep (heap : Heap) : ℕ → Matrix → Prop
  | nil (a : ℕ) (header : Represents heap ⟨a, 1⟩ [.bit false]) : RowsRep heap a []
  | cons (a rowRef tailRef : ℕ) (row : List ℕ) (rows : Matrix)
      (header : Represents heap ⟨a, 3⟩ [.bit true, .ref rowRef, .ref tailRef])
      (row_rep : RowRep heap rowRef row) (tail_rep : RowsRep heap tailRef rows)
      (row_lt : rowRef < a) (tail_lt : tailRef < a) : RowsRep heap a (row :: rows)

inductive SharedAnswerRep (heap : Heap) : ℕ → WireAnswer → Prop
  | failure (a : ℕ) (header : Represents heap ⟨a, 1⟩ [.bit false]) :
      SharedAnswerRep heap a none
  | success (a rowsRef : ℕ) (rows : Matrix)
      (header : Represents heap ⟨a, 2⟩ [.bit true, .ref rowsRef])
      (rows_rep : RowsRep heap rowsRef rows) (rows_lt : rowsRef < a) :
      SharedAnswerRep heap a (some rows)

theorem rowsRep_persist {before after : Heap} (he : Extends before after)
    (a : ℕ) (rows : Matrix) (h : RowsRep before a rows) : RowsRep after a rows := by
  induction h with
  | nil a hh => exact .nil a (represents_of_extends he _ _ hh)
  | cons a y t row rows hh hy ht hyl htl ih =>
    exact .cons a y t row rows (represents_of_extends he _ _ hh)
      (blobRep_persist he _ _ hy) ih hyl htl

theorem answerRep_persist {before after : Heap} (he : Extends before after)
    (a : ℕ) (ans : WireAnswer) (h : SharedAnswerRep before a ans) :
    SharedAnswerRep after a ans := by
  cases h with
  | failure hh => exact .failure a (represents_of_extends he _ _ hh)
  | success r rows hh hr hl =>
    exact .success a r rows (represents_of_extends he _ _ hh) (rowsRep_persist he _ _ hr) hl

theorem rowsRep_address_lt {heap : Heap} {a : ℕ} {rows : Matrix}
    (h : RowsRep heap a rows) : a < heap.size := by
  cases h with
  | nil a hh => have hb := hh.1; dsimp at hb; omega
  | cons a y t row rows hh hy ht hyl htl => have hb := hh.1; dsimp at hb; omega

theorem answerRep_address_lt {heap : Heap} {a : ℕ} {ans : WireAnswer}
    (h : SharedAnswerRep heap a ans) : a < heap.size := by
  cases h with
  | failure hh => have hb := hh.1; dsimp at hb; omega
  | success r rows hh hr hl => have hb := hh.1; dsimp at hb; omega

theorem failure_ne_success {heap : Heap} {a b : ℕ} {rows : Matrix}
    (hf : SharedAnswerRep heap a none) (hs : SharedAnswerRep heap b (some rows)) :
    a ≠ b := by
  intro hab; subst b
  cases hf with
  | failure hh =>
    cases hs with
    | success r rows hh' hr hl =>
      have h₀ := hh.2.2 0 (by simp)
      have h₁ := hh'.2.2 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h₀ h₁
      rw [h₀] at h₁
      cases h₁

def emptyRows (heap : Heap) : ℕ × Heap := (heap.size, allocateBlock heap [.bit false])
def failure (heap : Heap) : ℕ × Heap := (heap.size, allocateBlock heap [.bit false])
def success (heap : Heap) (rows : ℕ) : ℕ × Heap :=
  (heap.size, allocateBlock heap [.bit true, .ref rows])
def prependRows (heap : Heap) (rowRef tailRef : ℕ) : ℕ × Heap :=
  (heap.size, allocateBlock heap [.bit true, .ref rowRef, .ref tailRef])

theorem emptyRows_correct (heap : Heap) : RowsRep (emptyRows heap).2 (emptyRows heap).1 [] := by
  apply RowsRep.nil
  exact allocateTyped_represents heap [.bit false]

theorem failure_correct (heap : Heap) : SharedAnswerRep (failure heap).2 (failure heap).1 none := by
  apply SharedAnswerRep.failure
  exact allocateTyped_represents heap [.bit false]

theorem success_correct (heap : Heap) (r : ℕ) (rows : Matrix) (hr : RowsRep heap r rows) :
    SharedAnswerRep (success heap r).2 (success heap r).1 (some rows) := by
  exact .success heap.size r rows (allocateTyped_represents heap [.bit true, .ref r])
    (rowsRep_persist (allocateBlock_extends ..) _ _ hr) (rowsRep_address_lt hr)

theorem prependRows_correct (heap : Heap) (y t : ℕ) (row : List ℕ) (rows : Matrix)
    (hy : RowRep heap y row) (ht : RowsRep heap t rows) :
    RowsRep (prependRows heap y t).2 (prependRows heap y t).1 (row :: rows) := by
  exact .cons heap.size y t row rows (allocateTyped_represents heap _)
    (blobRep_persist (allocateBlock_extends ..) _ _ hy)
    (rowsRep_persist (allocateBlock_extends ..) _ _ ht)
    (blobRep_address_lt _ _ _ hy) (rowsRep_address_lt ht)

theorem prependRows_size (heap : Heap) (y t : ℕ) :
    (prependRows heap y t).2.size = heap.size + 3 := by
  simp [prependRows, allocateBlock_size]

theorem prependRows_shares (heap : Heap) (y t : ℕ) :
    read (prependRows heap y t).2 (heap.size + 1) = some (.ref y) ∧
    read (prependRows heap y t).2 (heap.size + 2) = some (.ref t) := by
  exact ⟨read_allocateBlock_new heap _ 1 (by simp),
    read_allocateBlock_new heap _ 2 (by simp)⟩

theorem prependRows_wellFormed (heap : Heap) (y t : ℕ) (hh : WellFormed heap)
    (hy : y < heap.size) (ht : t < heap.size) : WellFormed (prependRows heap y t).2 := by
  apply wellFormed_allocateBlock heap _ hh
  intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption

theorem failure_wellFormed (heap : Heap) (hh : WellFormed heap) :
    WellFormed (failure heap).2 := by
  apply wellFormed_allocateBlock heap _ hh
  simp

theorem success_wellFormed (heap : Heap) (r : ℕ) (hh : WellFormed heap)
    (hr : r < heap.size) : WellFormed (success heap r).2 := by
  apply wellFormed_allocateBlock heap _ hh
  simpa using hr

/-- A common addressed allocator; the returned base is also traversed. -/
def nodeD (width : ℕ) (heap : Heap) (slots : List Slot) : Costed (ℕ × Heap) :=
  let base := readAddress width heap.size
  let out := allocateSlotsD width heap slots
  ⟨(base.value, out.value), base.steps + out.steps + 1, out.allocations⟩

theorem nodeD_value (width : ℕ) (heap : Heap) (slots : List Slot)
    (hroom : heap.size + slots.length < 2 ^ width)
    (href : ∀ a, Slot.ref a ∈ slots → a < heap.size) :
    (nodeD width heap slots).value = (heap.size, allocateBlock heap slots) := by
  have hb : heap.size < 2 ^ width := by omega
  simp [nodeD, readAddress_value width heap.size hb,
    allocateSlotsD_value width heap slots hroom.le (fun a ha => (href a ha).trans hb)]

@[simp] theorem nodeD_allocations (width : ℕ) (heap : Heap) (slots : List Slot) :
    (nodeD width heap slots).allocations = slots.length := by simp [nodeD]

theorem nodeD_steps (width : ℕ) (heap : Heap) (slots : List Slot) :
    (nodeD width heap slots).steps ≤ (8 * slots.length + 8) * (width + 2) := by
  have hs := allocateSlotsD_steps width heap slots
  simp only [nodeD, readAddress_steps]
  nlinarith

def prependRowsD (w : ℕ) (heap : Heap) (y t : ℕ) := nodeD w heap [.bit true, .ref y, .ref t]
def emptyRowsD (w : ℕ) (heap : Heap) := nodeD w heap [.bit false]
def failureD (w : ℕ) (heap : Heap) := nodeD w heap [.bit false]
def successD (w : ℕ) (heap : Heap) (r : ℕ) := nodeD w heap [.bit true, .ref r]

theorem prependRowsD_value (w : ℕ) (heap : Heap) (y t : ℕ)
    (hroom : heap.size + 3 < 2 ^ w) (hy : y < heap.size) (ht : t < heap.size) :
    (prependRowsD w heap y t).value = prependRows heap y t := by
  apply nodeD_value
  · simpa using hroom
  · intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption

@[simp] theorem prependRowsD_allocations (w : ℕ) (heap : Heap) (y t : ℕ) :
    (prependRowsD w heap y t).allocations = 3 := by simp [prependRowsD]

theorem shell_sizes (heap : Heap) (r : ℕ) :
    (emptyRows heap).2.size = heap.size + 1 ∧
    (failure heap).2.size = heap.size + 1 ∧
    (success heap r).2.size = heap.size + 2 := by
  simp [emptyRows, failure, success, allocateBlock_size]

theorem prepend_success_size (heap : Heap) (row tail : ℕ) :
    (success (prependRows heap row tail).2 heap.size).2.size = heap.size + 5 := by
  simp [success, prependRows, allocateBlock_size, Nat.add_assoc]

end UAVProof.TreeBudgetSharedAnswerStore
