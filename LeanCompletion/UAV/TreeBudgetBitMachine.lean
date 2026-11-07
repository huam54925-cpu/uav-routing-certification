import Mathlib

/-! A reference binary-word cost semantics. Naturals below `2^w` are semantic
views of little-endian words of exactly `w` cells. Reading the low digit and
advancing the word cursor are one-cell operations; constructing `d + 2*x`
prepends one cell and does not invoke a machine integer multiplication.
Costs below describe this reference semantics, not Lean's runtime arithmetic. -/
namespace UAVProof.TreeBudgetBitMachine

structure Costed (α : Type) where
  value : α
  steps : ℕ
  allocations : ℕ

def pure {α : Type} (a : α) : Costed α := ⟨a, 0, 0⟩

def bind {α β : Type} (a : Costed α) (f : α → Costed β) : Costed β :=
  let b := f a.value
  ⟨b.value, a.steps + b.steps, a.allocations + b.allocations⟩

def charge {α : Type} (steps allocations : ℕ) (a : Costed α) : Costed α :=
  ⟨a.value, steps + a.steps, allocations + a.allocations⟩

/-- Scan all address digits, including leading zeros. Each step reads one
address cell and advances its cursor. The value is the decoded address. -/
def readAddress : ℕ → ℕ → Costed ℕ
  | 0, _ => ⟨0, 1, 0⟩
  | w + 1, a =>
    let out := readAddress w (a / 2)
    ⟨a % 2 + 2 * out.value, out.steps + 2, out.allocations⟩

theorem readAddress_value (w a : ℕ) (ha : a < 2 ^ w) :
    (readAddress w a).value = a := by
  induction w generalizing a with
  | zero => simp [readAddress]; omega
  | succ w ih =>
    have ht : a / 2 < 2 ^ w := by
      rw [pow_succ] at ha
      omega
    simp only [readAddress, ih _ ht]
    exact Nat.mod_add_div a 2

@[simp] theorem readAddress_steps (w a : ℕ) :
    (readAddress w a).steps = 2 * w + 1 := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih => simp [readAddress, ih]; omega

@[simp] theorem readAddress_allocations (w a : ℕ) :
    (readAddress w a).allocations = 0 := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih => exact ih _

/-- A standalone repeated address-scan profile. It does not access a heap or
execute the primitive whose step count is supplied, and therefore does not
establish a storage simulation for that primitive. Actual addressed reads and
writes are defined separately in `TreeBudgetAddressedBlocks`. -/
def accessLoop (width address : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (readAddress width address).steps + accessLoop width address k

theorem accessLoop_eq (width address k : ℕ) :
    accessLoop width address k = (2 * width + 1) * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [accessLoop, ih]; ring

/-- Rescale a work observation; this wrapper is not a machine execution. -/
def addressed {α : Type} (width address : ℕ) (op : Costed α) : Costed α :=
  ⟨op.value, accessLoop width address op.steps,
    op.allocations⟩

theorem addressed_steps {α : Type} (width address : ℕ) (op : Costed α) :
    (addressed width address op).steps = (2 * width + 1) * op.steps := by
  simp [addressed, accessLoop_eq]

end UAVProof.TreeBudgetBitMachine
