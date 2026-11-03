import LeanCompletion.UAV.TreeBudgetResidualSearch
import LeanCompletion.UAV.TreeBudgetCheckerExamples

/-! Two reachable states of one fixed search input have identical scalar/support
summaries but opposite feasibility. All finite computations are kernel checked. -/
namespace UAVProof.TreeBudgetStateSeparationExamples
open TreeBudgetPatterns TreeBudgetCertificate TreeBudgetResidualSearch
open TreeBudgetCheckerExamples

def H : Fin 5 → ℕ := ![0, 4, 2, 3, 2]
def fees : Fin 5 → ℚ := ![999, 0, 3, 4, 5]
def good : Fin 5 → ℕ := ![0, 2, 2, 1, 2]
def bad : Fin 5 → ℕ := ![0, 2, 1, 3, 1]
def takeA : Fin 5 → ℕ := ![0, 1, 1, 0, 0]
def takeB : Fin 5 → ℕ := ![0, 1, 0, 1, 0]
def takeC : Fin 5 → ℕ := ![0, 1, 0, 0, 1]

/-- The actual guarded transitions of the residual search, with the same H. -/
theorem reachable_prefixes :
    RowValid hubTree H fees 10 takeA ∧ RowValid hubTree H fees 10 takeB ∧
    RowValid hubTree H fees 10 takeC ∧
    (∀ v, takeB v ≤ H v) ∧ (∀ v, takeB v ≤ (H - takeB) v) ∧ H - takeB - takeB = good ∧
    (∀ v, takeA v ≤ H v) ∧ (∀ v, takeC v ≤ (H - takeA) v) ∧ H - takeA - takeC = bad ∧
    rootCount hubTree H = 4 ∧ rootCount hubTree good = 2 ∧
    rootCount hubTree bad = 2 := by decide +kernel

def visits (r : Fin 5 → ℕ) (v : Fin 5) : ℕ :=
  if v = hubTree.root then 0 else r v + ∑ w ∈ children hubTree v, r w

/-- Includes both satellite-only and all nondepot visit counts. -/
def summary (k : ℕ) (r : Fin 5 → ℕ) :=
  (k, cost hubTree r fees, r 2 + r 3 + r 4,
    ∑ v, visits r v, Finset.univ.filter (fun v => 0 < r v))

theorem same_summary : summary 2 good = summary 2 bad := by decide +kernel

theorem summary_values : cost hubTree good fees = 20 ∧
    good 2 + good 3 + good 4 = 5 ∧ (∑ v, visits good v) = 12 ∧
    Finset.univ.filter (fun v => 0 < good v) = {1, 2, 3, 4} := by decide +kernel

theorem good_search : (searchRows hubTree H fees 10 2 good).isSome = true := by
  decide +kernel

theorem bad_search : searchRows hubTree H fees 10 2 bad = none := by
  decide +kernel

theorem good_feasible : ResidualFeasible hubTree H fees 10 2 good :=
  (searchRows_correct ..).mp good_search

theorem bad_infeasible : ¬ ResidualFeasible hubTree H fees 10 2 bad := by
  intro h
  have hs := (searchRows_correct ..).mpr h
  rw [bad_search] at hs
  contradiction

/-- No decision function of this summary can be correct even on these two
states reached by legal prefixes of the same original input. -/
theorem no_summary_decider :
    ¬ ∃ f : (ℕ × ℚ × ℕ × ℕ × Finset (Fin 5)) → Prop,
      (f (summary 2 good) ↔ ResidualFeasible hubTree H fees 10 2 good) ∧
      (f (summary 2 bad) ↔ ResidualFeasible hubTree H fees 10 2 bad) := by
  rintro ⟨f, hg, hb⟩
  have h := hg.mpr good_feasible
  rw [same_summary] at h
  exact bad_infeasible (hb.mp h)

end UAVProof.TreeBudgetStateSeparationExamples

#print axioms UAVProof.TreeBudgetStateSeparationExamples.reachable_prefixes
#print axioms UAVProof.TreeBudgetStateSeparationExamples.same_summary
#print axioms UAVProof.TreeBudgetStateSeparationExamples.good_feasible
#print axioms UAVProof.TreeBudgetStateSeparationExamples.bad_infeasible
#print axioms UAVProof.TreeBudgetStateSeparationExamples.no_summary_decider
