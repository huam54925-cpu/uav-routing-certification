import LeanCompletion.UAV.TreeBudgetFiniteSearch
import LeanCompletion.UAV.TreeBudgetCriterion

/-! Computable integer tree recursion and a complete service-budget checker.
The public solver accepts a numbered rooted tree and returns a pattern certificate.
The mathematical interface still describes existence of actual legal routes. -/
namespace UAVProof.TreeBudgetChecker

open TreeFlowExistence TreeBudgetPatterns TreeBudgetCertificate TreeBudgetFiniteSearch
open TreeBudgetMatrix TreeBudgetCriterion
variable {V : Type*} [Fintype V] [DecidableEq V]

def requirementExec (R : RootedTree V) (d : V → ℕ) (v : V) : ℤ :=
  (d v : ℤ) - ∑ w : children R v, requirementExec R d w
termination_by R.rank v
decreasing_by
  apply R.child_rank
  rw [← children_eq]
  exact w.property

theorem requirementExec_eq (R : RootedTree V) (d : V → ℕ) (v : V) :
    requirementExec R d v = requirement R d v := by
  rw [requirementExec, requirement_eq, Finset.sum_coe_sort]
  congr 1
  rw [← children_eq]
  apply Finset.sum_congr rfl
  intro w hw
  exact requirementExec_eq R d w
termination_by R.rank v
decreasing_by
  apply R.child_rank
  rw [← children_eq]
  exact hw

def compatible (R : RootedTree V) (d : V → ℕ) (m : ℕ) : Bool :=
  decide ((∀ v, v ≠ R.root → 0 ≤ requirementExec R d v) ∧
    (m : ℤ) = ∑ w ∈ children R R.root, requirementExec R d w)

@[simp] theorem compatible_eq_true_iff (R : RootedTree V) (d : V → ℕ) (m : ℕ) :
    compatible R d m = true ↔ FlowCompatible R d m := by
  simp [compatible, FlowCompatible, requirementExec_eq, children_eq]

def multiplicities (R : RootedTree V) (d : V → ℕ) (v : V) : ℕ :=
  (requirementExec R d v).toNat

theorem multiplicities_eq (R : RootedTree V) (d : V → ℕ) :
    multiplicities R d = fun v => (requirement R d v).toNat := by
  funext v
  simp [multiplicities, requirementExec_eq]

variable {n : ℕ}

/-- Integer compatibility is checked before natural multiplicities are searched. -/
def solve (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Option (Certificate (Fin n)) :=
  if compatible R d m then search R (multiplicities R d) m s T else none

def checkTreeBudget (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) : Bool := (solve R d m s T).isSome

theorem check_eq_true_iff (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    checkTreeBudget R d m s T = true ↔ BudgetRoutes R d m s T := by
  rw [budget_routes_iff]
  by_cases hc : compatible R d m = true
  · have hcomp := (compatible_eq_true_iff R d m).mp hc
    simp [checkTreeBudget, solve, hc, search_correct, multiplicities_eq, hcomp]
  · have hcomp : ¬ FlowCompatible R d m := by simpa using hc
    simp [checkTreeBudget, solve, hc, hcomp]

theorem solve_sound (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) (c : Certificate (Fin n))
    (hc : solve R d m s T = some c) :
    FlowCompatible R d m ∧ checkCertificate R (multiplicities R d) m s T c = true ∧
      BudgetRoutes R d m s T := by
  have ht : compatible R d m = true := by
    by_contra hn
    simp [solve, hn] at hc
  have hs : search R (multiplicities R d) m s T = some c := by
    simpa [solve, ht] using hc
  refine ⟨(compatible_eq_true_iff ..).mp ht, search_sound _ _ _ _ _ c hs, ?_⟩
  apply (check_eq_true_iff ..).mp
  simp [checkTreeBudget, hc]

theorem solve_none_iff (R : RootedTree (Fin n)) (d : Fin n → ℕ) (m : ℕ)
    (s : Fin n → ℚ) (T : ℚ) :
    solve R d m s T = none ↔ ¬ BudgetRoutes R d m s T := by
  rw [← check_eq_true_iff]
  unfold checkTreeBudget
  cases solve R d m s T <;> simp

end UAVProof.TreeBudgetChecker

#print axioms UAVProof.TreeBudgetChecker.requirementExec_eq
#print axioms UAVProof.TreeBudgetChecker.check_eq_true_iff
#print axioms UAVProof.TreeBudgetChecker.solve_sound
#print axioms UAVProof.TreeBudgetChecker.solve_none_iff
