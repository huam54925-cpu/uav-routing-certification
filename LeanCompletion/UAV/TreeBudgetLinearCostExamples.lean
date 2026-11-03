import LeanCompletion.UAV.TreeBudgetLinearCost
import LeanCompletion.UAV.TreeBudgetResidualSearch
import LeanCompletion.UAV.TreeBudgetExamples

/-! Exact arithmetic regressions for the physical-to-virtual cost bridge. -/
namespace UAVProof.TreeBudgetLinearCostExamples
open TreeBudgetLinearCost TreeBudgetPatterns TreeBudgetCertificate TreeFlowExamples

/-- Use the first three vertices of pathFour; the last edge has zero multiplicity. -/
def p : Fin 4 → ℕ := ![99, 1, 1, 0]
def c (u v : Fin 4) : ℚ :=
  if u = 0 ∧ v = 1 then 4 else if u = 1 ∧ v = 0 then 6 else
  if u = 1 ∧ v = 2 then 1 / 2 else if u = 2 ∧ v = 1 then 3 / 2 else 0
def s : Fin 4 → ℚ := ![999, 0, 0, 0]
def w := combinedWeight pathFour s c
def sigma := virtualService pathFour w

theorem asymmetric_weights : w 1 = 10 ∧ w 2 = 2 := by decide +kernel
theorem negative_virtual_fee : sigma 0 = 0 ∧ sigma 1 = 10 ∧ sigma 2 = -8 := by
  decide +kernel
theorem exact_twelve : cost pathFour p sigma = 12 ∧
    flowTravel (TreeFlowExistence.edgeFlow pathFour p) c = 12 := by decide +kernel
theorem ignored_depot_fee :
    (∀ v, v ≠ pathFour.root → combinedWeight pathFour s c v =
      combinedWeight pathFour (fun _ => 0) c v) ∧
    cost pathFour p sigma = cost pathFour (normalize pathFour p) sigma := by decide +kernel

def cert : Certificate (Fin 4) := ⟨1, fun _ => normalize pathFour p, fun _ => 1⟩

theorem exact_budget_accepted : checkCertificate pathFour p 1 sigma 12 cert = true := by
  decide +kernel
theorem below_budget_rejected : checkCertificate pathFour p 1 sigma 11 cert = false := by
  decide +kernel
theorem search_checked :
    (TreeBudgetResidualSearch.search pathFour p 1 sigma 12).map
      (checkCertificate pathFour p 1 sigma 12) = some true := by decide +kernel
theorem search_rejects_eleven :
    (TreeBudgetResidualSearch.search pathFour p 1 sigma 11).isSome = false := by
  decide +kernel

end UAVProof.TreeBudgetLinearCostExamples

#print axioms UAVProof.TreeBudgetLinearCostExamples.negative_virtual_fee
#print axioms UAVProof.TreeBudgetLinearCostExamples.exact_twelve
#print axioms UAVProof.TreeBudgetLinearCostExamples.ignored_depot_fee
#print axioms UAVProof.TreeBudgetLinearCostExamples.exact_budget_accepted
#print axioms UAVProof.TreeBudgetLinearCostExamples.below_budget_rejected
#print axioms UAVProof.TreeBudgetLinearCostExamples.search_checked
#print axioms UAVProof.TreeBudgetLinearCostExamples.search_rejects_eleven
