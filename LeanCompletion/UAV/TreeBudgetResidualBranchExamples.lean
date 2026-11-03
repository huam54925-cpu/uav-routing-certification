import LeanCompletion.UAV.TreeBudgetResidualBranchSearch
import LeanCompletion.UAV.TreeBudgetResidualExamples

/-! Regressions for residual search through the root decomposition and demand APIs. -/
namespace UAVProof.TreeBudgetResidualBranchExamples
open TreeBudgetPatterns TreeBudgetCertificate TreeBudgetResidualBranchSearch TreeBudgetChecker
open TreeBudgetExamples TreeFlowExamples TreeBudgetBranchExamples TreeBudgetResidualExamples

theorem repeat_branch_checked :
    (searchByRoot centerThree ![2, 99, 0] 2 (fun _ => 0) 0).map
      (checkCertificate centerThree ![2, 99, 0] 2 (fun _ => 0) 0) = some true := by
  decide +kernel

theorem backtrack_branch_checked :
    (searchByRoot pathFour backtrackH 2 backtrackFees 2).map
      (checkCertificate pathFour backtrackH 2 backtrackFees 2) = some true := by decide +kernel

theorem multiple_branches_checked :
    (searchByRoot centerThree directCounts 5 directFees 10).map
      (checkCertificate centerThree directCounts 5 directFees 10) = some true := by decide +kernel

theorem depot_only_negative_budget_checked :
    (searchByRoot depotOnly (fun _ => 999) 0 (fun _ => 999) (-1)).map
      (checkCertificate depotOnly (fun _ => 999) 0 (fun _ => 999) (-1)) = some true := by
  decide +kernel

theorem zero_branch_deep_positive_reject :
    (searchByRoot pathFour ![7, 0, 1, 0] 0 (fun _ => 0) 100).isSome = false := by decide +kernel

theorem wrong_fleet_reject :
    (searchByRoot centerThree directCounts 4 directFees 10).isSome = false := by decide +kernel

theorem other_branch_negative_cannot_rescue :
    (searchByRoot centerThree ![1, 99, 1] 2 ![11, 999, -100] 10).isSome = false := by decide +kernel

theorem same_branch_signed_cancellation_checked :
    (searchByRoot pathFour ![7, 1, 1, 1] 1 ![999, 0, 6, -8] 4).map
      (checkCertificate pathFour ![7, 1, 1, 1] 1 ![999, 0, 6, -8] 4) = some true := by
  decide +kernel

theorem negative_integer_requirement_reject :
    checkTreeBudgetByRoot pathFour ![0, 0, 0, 1] 1 (fun _ => 0) 100 = false := by decide +kernel

theorem compatible_but_disconnected_reject :
    compatible pathFour ![0, 1, 1, 0] 0 = true ∧
      checkTreeBudgetByRoot pathFour ![0, 1, 1, 0] 0 (fun _ => 0) 100 = false := by decide +kernel

theorem demand_signed_checked :
    (solveByRoot pathFour ![999, 2, 2, 1] 1 ![999, 0, 6, -8] 4).map
      (checkCertificate pathFour (multiplicities pathFour ![999, 2, 2, 1])
        1 ![999, 0, 6, -8] 4) = some true := by decide +kernel

theorem old_root_flags_agree :
    (searchByRoot centerThree directCounts 5 directFees 10).isSome =
      (TreeBudgetBranchSearch.searchByRoot centerThree directCounts 5 directFees 10).isSome := by
  decide +kernel

end UAVProof.TreeBudgetResidualBranchExamples

#print axioms UAVProof.TreeBudgetResidualBranchExamples.repeat_branch_checked
#print axioms UAVProof.TreeBudgetResidualBranchExamples.backtrack_branch_checked
#print axioms UAVProof.TreeBudgetResidualBranchExamples.multiple_branches_checked
#print axioms UAVProof.TreeBudgetResidualBranchExamples.zero_branch_deep_positive_reject
#print axioms UAVProof.TreeBudgetResidualBranchExamples.demand_signed_checked
