import LeanCompletion.UAV.TreeBudgetVector
import LeanCompletion.UAV.TreeBudgetIntegerCost
import LeanCompletion.UAV.TreeBudgetCertificate

/-! Boolean row checking on materialized vectors. Structural tests traverse a
finite index list and read array-backed vectors. The budget test uses signed
integer arithmetic. This is a semantic bridge, not a bit-cost theorem or a
candidate-list/search simulation. -/
namespace UAVProof.TreeBudgetVectorChecker
open TreeFlowExistence TreeBudgetPatterns TreeBudgetRow TreeBudgetCertificate
open TreeBudgetVector TreeBudgetIntegerCost
variable {n : ℕ}

/-- Structural tests traverse the fixed finite index list and may stop early;
coordinates are read from materialized arrays. -/
def rowValidB (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (p : Vector ℕ n) : Bool :=
  decide (decode p R.root = 0) &&
    ((List.finRange n).all fun v => decide (v ≠ R.root → decode p v ≤ decode H v)) &&
    decide (rootCount R (decode p) = 1) &&
    ((List.finRange n).all fun v => decide
      (v ≠ R.root → 0 < decode p v → R.parent v ≠ R.root → 0 < decode p (R.parent v))) &&
    decide (intCost R (fun v => A[v]) (decode p) ≤ AT)

/-- Positive scaling preserves the budget comparison, including negative fees
and a negative budget. The other tests are exactly the existing row predicate. -/
theorem rowValidB_eq_true_iff (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (p : Vector ℕ n) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, ((A[v] : ℤ) : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) :
    rowValidB R H A AT p = true ↔ RowValid R (decode H) s T (decode p) := by
  simp only [rowValidB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_const]
  rw [intCost_le_iff R (fun v => A[v]) s (decode p) AT T D hD hA hAT]
  simp only [RowValid, AncestorClosed, and_assoc]

/-- Materialize the scaled signed fees once, for reuse by all row checks. -/
def scaleFees (a : Vector ℤ n) (b : Vector ℕ n) (bT : ℕ) : Vector ℤ n :=
  let D := commonDenominator (decode b) bT
  Vector.ofFn fun v => scaledNumerator D a[v] b[v]

def scaleBudget (b : Vector ℕ n) (aT : ℤ) (bT : ℕ) : ℤ :=
  scaledNumerator (commonDenominator (decode b) bT) aT bT

/-- Raw positive denominators need not be reduced or pairwise coprime. -/
theorem rowValidB_scaled_eq_true_iff (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (a : Vector ℤ n) (b : Vector ℕ n) (aT : ℤ) (bT : ℕ) (p : Vector ℕ n)
    (hb : ∀ v : Fin n, 0 < b[v]) (hbT : 0 < bT) :
    rowValidB R H (scaleFees a b bT) (scaleBudget b aT bT) p = true ↔
      RowValid R (decode H) (fun v => (a[v] : ℚ) / (b[v] : ℚ))
        ((aT : ℚ) / (bT : ℚ)) (decode p) := by
  apply rowValidB_eq_true_iff R H (scaleFees a b bT) (scaleBudget b aT bT) p
    _ _ (commonDenominator (decode b) bT : ℚ)
  · exact_mod_cast commonDenominator_pos (decode b) bT hb hbT
  · intro v
    simpa [scaleFees, decode] using
      scaledNumerator_cast (commonDenominator (decode b) bT) a[v] b[v]
        (denominator_dvd_commonDenominator (decode b) bT v)
  · exact scaledNumerator_cast _ _ _ (budget_denominator_dvd_commonDenominator (decode b) bT)

end UAVProof.TreeBudgetVectorChecker

#print axioms UAVProof.TreeBudgetVectorChecker.rowValidB_eq_true_iff
#print axioms UAVProof.TreeBudgetVectorChecker.rowValidB_scaled_eq_true_iff
