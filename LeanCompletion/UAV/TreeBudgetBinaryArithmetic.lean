import LeanCompletion.UAV.TreeBudgetBitMachine

/-! Binary ripple arithmetic with costs computed by the actual digit loops.
The width is storage capacity, not a running-time label. Every recursive
iteration consumes one input digit and emits one result digit. -/
namespace UAVProof.TreeBudgetBinaryArithmetic
open TreeBudgetBitMachine

/-- Ripple addition; the carry is a single bit on well-formed calls. -/
def addCarry : ℕ → ℕ → ℕ → ℕ → Costed ℕ
  | 0, _, _, c => ⟨c, 1, 1⟩
  | w + 1, a, b, c =>
    let digit := a % 2 + b % 2 + c
    let out := addCarry w (a / 2) (b / 2) (digit / 2)
    ⟨digit % 2 + 2 * out.value, out.steps + 12, out.allocations + 1⟩

theorem addCarry_value (w a b c : ℕ) (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (addCarry w a b c).value = a + b + c := by
  induction w generalizing a b c with
  | zero => simp [addCarry]; omega
  | succ w ih =>
    have ha' : a / 2 < 2 ^ w := by rw [pow_succ] at ha; omega
    have hb' : b / 2 < 2 ^ w := by rw [pow_succ] at hb; omega
    simp only [addCarry, ih _ _ _ ha' hb']
    have h1 := Nat.mod_add_div a 2
    have h2 := Nat.mod_add_div b 2
    have h3 := Nat.mod_add_div (a % 2 + b % 2 + c) 2
    omega

@[simp] theorem addCarry_steps (w a b c : ℕ) :
    (addCarry w a b c).steps = 12 * w + 1 := by
  induction w generalizing a b c with
  | zero => rfl
  | succ w ih => simp [addCarry, ih]; omega

@[simp] theorem addCarry_allocations (w a b c : ℕ) :
    (addCarry w a b c).allocations = w + 1 := by
  induction w generalizing a b c with
  | zero => rfl
  | succ w ih => simp [addCarry, ih]

def addNat (w a b : ℕ) := addCarry w a b 0

theorem addCarry_small (a b c : ℕ) (hc : c ≤ 1) :
    a % 2 + b % 2 + c ≤ 3 ∧ (a % 2 + b % 2 + c) / 2 ≤ 1 := by
  have ha := Nat.mod_lt a (by omega : 0 < 2)
  have hb := Nat.mod_lt b (by omega : 0 < 2)
  omega

@[simp] theorem addNat_value (w a b : ℕ) (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (addNat w a b).value = a + b := by simp [addNat, addCarry_value w a b 0 ha hb]

/-- Borrow subtraction retains the final borrow and the w-bit modular result.
Every branch computes only on two digits and one borrow bit. -/
def subBorrow : ℕ → ℕ → ℕ → Bool → Costed (ℕ × Bool)
  | 0, _, _, c => ⟨(0, c), 1, 0⟩
  | w + 1, a, b, c =>
    let borrow := decide (a % 2 < b % 2 + c.toNat)
    let digit := a % 2 + 2 * borrow.toNat - (b % 2 + c.toNat)
    let out := subBorrow w (a / 2) (b / 2) borrow
    ⟨(digit + 2 * out.value.1, out.value.2), out.steps + 12, out.allocations + 1⟩

theorem subBorrow_spec (w a b : ℕ) (c : Bool)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (subBorrow w a b c).value.1 < 2 ^ w ∧
    (subBorrow w a b c).value.1 + b + c.toNat =
      a + 2 ^ w * (subBorrow w a b c).value.2.toNat := by
  induction w generalizing a b c with
  | zero => simp [subBorrow] at *; omega
  | succ w ih =>
    have ha' : a / 2 < 2 ^ w := by rw [pow_succ] at ha; omega
    have hb' : b / 2 < 2 ^ w := by rw [pow_succ] at hb; omega
    have hi := ih (a / 2) (b / 2) (decide (a % 2 < b % 2 + c.toNat)) ha' hb'
    have ham := Nat.mod_lt a (by omega : 0 < 2)
    have hbm := Nat.mod_lt b (by omega : 0 < 2)
    have had := Nat.mod_add_div a 2
    have hbd := Nat.mod_add_div b 2
    let borrow := decide (a % 2 < b % 2 + c.toNat)
    let digit := a % 2 + 2 * borrow.toNat - (b % 2 + c.toNat)
    have hc : c.toNat ≤ 1 := by cases c <;> decide
    have hd : digit < 2 ∧ digit + b % 2 + c.toNat = a % 2 + 2 * borrow.toNat := by
      dsimp [digit, borrow]
      by_cases hl : a % 2 < b % 2 + c.toNat <;> simp [hl] <;> omega
    change digit + 2 * (subBorrow w (a / 2) (b / 2) borrow).value.1 < 2 ^ (w + 1) ∧
      digit + 2 * (subBorrow w (a / 2) (b / 2) borrow).value.1 + b + c.toNat =
        a + 2 ^ (w + 1) * (subBorrow w (a / 2) (b / 2) borrow).value.2.toNat
    change (subBorrow w (a / 2) (b / 2) borrow).value.1 < 2 ^ w ∧
      (subBorrow w (a / 2) (b / 2) borrow).value.1 + b / 2 + borrow.toNat =
        a / 2 + 2 ^ w * (subBorrow w (a / 2) (b / 2) borrow).value.2.toNat at hi
    rw [pow_succ]
    constructor <;> nlinarith [hd.1, hd.2, hi.1, hi.2]

@[simp] theorem subBorrow_steps (w a b : ℕ) (c : Bool) :
    (subBorrow w a b c).steps = 12 * w + 1 := by
  induction w generalizing a b c with
  | zero => rfl
  | succ w ih => simp [subBorrow, ih]; omega

@[simp] theorem subBorrow_allocations (w a b : ℕ) (c : Bool) :
    (subBorrow w a b c).allocations = w := by
  induction w generalizing a b c with
  | zero => rfl
  | succ w ih => simp [subBorrow, ih]

def subNat (w a b : ℕ) : Costed ℕ :=
  let out := subBorrow w a b false
  ⟨if out.value.2 then 0 else out.value.1, out.steps + 1, out.allocations⟩

theorem subNat_value (w a b : ℕ) (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (subNat w a b).value = a - b := by
  have h := subBorrow_spec w a b false ha hb
  simp only [Bool.toNat_false, Nat.add_zero] at h
  simp only [subNat]
  cases he : (subBorrow w a b false).value.2 <;> simp_all <;> omega

def leNat (w a b : ℕ) : Costed Bool :=
  let out := subBorrow w b a false
  ⟨!out.value.2, out.steps + 1, out.allocations⟩

theorem leNat_value (w a b : ℕ) (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (leNat w a b).value = decide (a ≤ b) := by
  have h := subBorrow_spec w b a false hb ha
  simp only [Bool.toNat_false, Nat.add_zero] at h
  simp only [leNat]
  cases he : (subBorrow w b a false).value.2 <;> simp_all <;> omega

def eqNat (w a b : ℕ) : Costed Bool :=
  let ab := leNat w a b
  let ba := leNat w b a
  ⟨ab.value && ba.value, ab.steps + ba.steps + 1, ab.allocations + ba.allocations⟩

theorem eqNat_value (w a b : ℕ) (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (eqNat w a b).value = decide (a = b) := by
  simp [eqNat, leNat_value w a b ha hb, leNat_value w b a hb ha, Nat.le_antisymm_iff]

def zeroNat (w a : ℕ) := eqNat w a 0

theorem zeroNat_value (w a : ℕ) (ha : a < 2 ^ w) :
    (zeroNat w a).value = decide (a = 0) :=
  eqNat_value w a 0 ha (by positivity)

theorem primitive_steps (w a b : ℕ) :
    (addNat w a b).steps = 12 * w + 1 ∧
    (subNat w a b).steps = 12 * w + 2 ∧
    (leNat w a b).steps = 12 * w + 2 ∧
    (eqNat w a b).steps = 24 * w + 5 := by
  simp [addNat, subNat, leNat, eqNat]; omega

/-- Schoolbook multiplication: shift a recursive partial product by one cell;
an odd multiplier digit invokes the verified ripple adder. -/
def mulLoop (capacity : ℕ) : ℕ → ℕ → ℕ → Costed ℕ
  | 0, _, _ => ⟨0, 1, 1⟩
  | w + 1, a, b =>
    let tail := mulLoop capacity w a (b / 2)
    if b % 2 = 0 then
      ⟨2 * tail.value, tail.steps + 4, tail.allocations + 1⟩
    else
      let out := addNat (capacity + w + 1) (2 * tail.value) a
      ⟨out.value, tail.steps + out.steps + 4, tail.allocations + out.allocations + 1⟩

theorem mulLoop_value (capacity w a b : ℕ)
    (ha : a < 2 ^ capacity) (hb : b < 2 ^ w) :
    (mulLoop capacity w a b).value = a * b := by
  induction w generalizing b with
  | zero => simp [mulLoop]; omega
  | succ w ih =>
    have hb' : b / 2 < 2 ^ w := by rw [pow_succ] at hb; omega
    have ht := ih (b / 2) hb'
    have hm : a * (b / 2) < 2 ^ (capacity + w) := by
      rw [pow_add]
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt ha))
        (Nat.mul_lt_mul_of_pos_left hb' (by positivity))
    have ht' : 2 * (mulLoop capacity w a (b / 2)).value < 2 ^ (capacity + w + 1) := by
      rw [ht, pow_succ]; omega
    have ha' : a < 2 ^ (capacity + w + 1) :=
      lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))
    simp only [mulLoop]
    split_ifs with he
    · rw [ht]
      have hd := Nat.mod_add_div b 2
      rw [he] at hd
      nlinarith
    · rw [addNat_value _ _ _ ht' ha', ht]
      have hd := Nat.mod_add_div b 2
      have hbmod := Nat.mod_lt b (by omega : 0 < 2)
      have hb1 : b % 2 = 1 := by omega
      rw [hb1] at hd
      nlinarith

theorem mulLoop_steps_le (capacity w a b : ℕ) :
    (mulLoop capacity w a b).steps ≤ 20 * (w + 1) * (capacity + w + 1) := by
  induction w generalizing b with
  | zero => simp [mulLoop]; omega
  | succ w ih =>
    have ht := ih (b / 2)
    simp only [mulLoop]
    split_ifs <;> simp only [addNat, addCarry_steps] <;> nlinarith

theorem mulLoop_allocations_le (capacity w a b : ℕ) :
    (mulLoop capacity w a b).allocations ≤ 4 * (w + 1) * (capacity + w + 1) := by
  induction w generalizing b with
  | zero => simp [mulLoop]; omega
  | succ w ih =>
    have ht := ih (b / 2)
    simp only [mulLoop]
    split_ifs <;> simp only [addNat, addCarry_allocations] <;> nlinarith

def mulNat (w a b : ℕ) := mulLoop w w a b

theorem mulNat_value (w a b : ℕ) (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (mulNat w a b).value = a * b := mulLoop_value w w a b ha hb

theorem mulNat_steps_le (w a b : ℕ) :
    (mulNat w a b).steps ≤ 40 * (w + 1) ^ 2 := by
  have h := mulLoop_steps_le w w a b
  unfold mulNat
  nlinarith

theorem mulNat_allocations_le (w a b : ℕ) :
    (mulNat w a b).allocations ≤ 8 * (w + 1) ^ 2 := by
  have h := mulLoop_allocations_le w w a b
  unfold mulNat
  nlinarith

theorem mulLoop_allocations_le_steps (capacity w a b : ℕ) :
    (mulLoop capacity w a b).allocations ≤ (mulLoop capacity w a b).steps := by
  induction w generalizing b with
  | zero => simp [mulLoop]
  | succ w ih =>
    have h := ih (b / 2)
    simp only [mulLoop]
    split_ifs <;> simp only [addNat, addCarry_allocations, addCarry_steps] <;> omega

end UAVProof.TreeBudgetBinaryArithmetic
