import LeanCompletion.UAV.TreeBudgetPatterns

/-! Exact integer scaling of the existing rational row cost. All fees and
budgets are signed. Raw fractions may be unreduced; only denominator positivity
is required. This module proves semantics, not bit-operation costs. -/
namespace UAVProof.TreeBudgetIntegerCost
open TreeFlowExistence TreeBudgetPatterns
variable {n : ℕ}

def intCost (R : RootedTree (Fin n)) (A : Fin n → ℤ) (p : Fin n → ℕ) : ℤ :=
  ∑ v, if v = R.root then 0 else
    (A v + if R.parent v = R.root then 0 else A (R.parent v)) * (p v : ℤ)

/-- The algebraic interpretation needs no positivity or bound on the row. -/
theorem intCost_cast (R : RootedTree (Fin n)) (A : Fin n → ℤ)
    (s : Fin n → ℚ) (p : Fin n → ℕ) (D : ℚ)
    (hA : ∀ v, (A v : ℚ) = D * s v) :
    (intCost R A p : ℚ) = D * cost R p s := by
  simp only [intCost, cost, Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = R.root
  · simp [hv]
  · by_cases hp : R.parent v = R.root
    · simp [hv, hp, hA, mul_assoc]
    · simp only [if_neg hv, if_neg hp, Int.cast_mul, Int.cast_add, Int.cast_natCast, hA]
      ring

/-- A positive scale preserves the budget comparison, including negative fees
and negative budgets. -/
theorem intCost_le_iff (R : RootedTree (Fin n)) (A : Fin n → ℤ)
    (s : Fin n → ℚ) (p : Fin n → ℕ) (AT : ℤ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v, (A v : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) :
    intCost R A p ≤ AT ↔ cost R p s ≤ T := by
  have hcast : intCost R A p ≤ AT ↔ (intCost R A p : ℚ) ≤ (AT : ℚ) := by
    exact_mod_cast (Iff.rfl : intCost R A p ≤ AT ↔ intCost R A p ≤ AT)
  rw [hcast, intCost_cast R A s p D hA, hAT]
  exact mul_le_mul_iff_right₀ hD

/-- Product construction for raw (possibly unreduced) input denominators. -/
def commonDenominator (b : Fin n → ℕ) (bT : ℕ) : ℕ := bT * ∏ v, b v

def scaledNumerator (D : ℕ) (a : ℤ) (b : ℕ) : ℤ := a * (D / b : ℕ)

theorem commonDenominator_pos (b : Fin n → ℕ) (bT : ℕ)
    (hb : ∀ v, 0 < b v) (hbT : 0 < bT) : 0 < commonDenominator b bT := by
  exact Nat.mul_pos hbT (Finset.prod_pos (fun v _ => hb v))

theorem denominator_dvd_commonDenominator (b : Fin n → ℕ) (bT : ℕ) (v : Fin n) :
    b v ∣ commonDenominator b bT := by
  exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem b (Finset.mem_univ v)) bT

theorem budget_denominator_dvd_commonDenominator (b : Fin n → ℕ) (bT : ℕ) :
    bT ∣ commonDenominator b bT := by
  exact dvd_mul_right bT _

theorem scaledNumerator_cast (D : ℕ) (a : ℤ) (b : ℕ) (hd : b ∣ D) :
    (scaledNumerator D a b : ℚ) = (D : ℚ) * ((a : ℚ) / (b : ℚ)) := by
  simp only [scaledNumerator, Int.cast_mul, Int.cast_natCast]
  rw [Nat.cast_div_charZero hd]
  ring

/-- Full instantiation for raw signed numerators and positive denominators.
No coprimality or canonical rational representation is assumed. -/
theorem raw_intCost_le_iff (R : RootedTree (Fin n)) (a : Fin n → ℤ)
    (b : Fin n → ℕ) (aT : ℤ) (bT : ℕ) (p : Fin n → ℕ)
    (hb : ∀ v, 0 < b v) (hbT : 0 < bT) :
    intCost R (fun v => scaledNumerator (commonDenominator b bT) (a v) (b v)) p ≤
        scaledNumerator (commonDenominator b bT) aT bT ↔
      cost R p (fun v => (a v : ℚ) / (b v : ℚ)) ≤ (aT : ℚ) / (bT : ℚ) := by
  apply intCost_le_iff R _ _ p _ _ (commonDenominator b bT : ℚ)
  · exact_mod_cast commonDenominator_pos b bT hb hbT
  · intro v
    exact scaledNumerator_cast _ _ _ (denominator_dvd_commonDenominator b bT v)
  · exact scaledNumerator_cast _ _ _ (budget_denominator_dvd_commonDenominator b bT)

end UAVProof.TreeBudgetIntegerCost

#print axioms UAVProof.TreeBudgetIntegerCost.intCost_cast
#print axioms UAVProof.TreeBudgetIntegerCost.intCost_le_iff
#print axioms UAVProof.TreeBudgetIntegerCost.commonDenominator_pos
#print axioms UAVProof.TreeBudgetIntegerCost.denominator_dvd_commonDenominator
#print axioms UAVProof.TreeBudgetIntegerCost.budget_denominator_dvd_commonDenominator
#print axioms UAVProof.TreeBudgetIntegerCost.scaledNumerator_cast
#print axioms UAVProof.TreeBudgetIntegerCost.raw_intCost_le_iff
