import LeanCompletion.UAV.TreeBudgetResidualSearch
import LeanCompletion.UAV.TreeBudgetBranchExamples

/-! Kernel-evaluated regressions for residual witnesses and certificate output. -/
namespace UAVProof.TreeBudgetResidualExamples
open TreeBudgetPatterns TreeBudgetCertificate TreeBudgetResidualSearch
open TreeBudgetExamples TreeFlowExamples TreeBudgetBranchExamples

def repeatH : Fin 3 → ℕ := ![2, 0, 0]
def repeatRow : Fin 3 → ℕ := ![1, 0, 0]

theorem repeat_only_candidate :
    TreeBudgetFiniteSearch.candidates centerThree repeatH (fun _ => 0) 0 = [repeatRow] := by
  decide +kernel

theorem repeat_same_row_twice :
    searchRows centerThree repeatH (fun _ => 0) 0 2 repeatH =
      some [repeatRow, repeatRow] := by decide +kernel

theorem repeat_output_checked :
    (search centerThree ![2, 99, 0] 2 (fun _ => 0) 0).map
      (checkCertificate centerThree ![2, 99, 0] 2 (fun _ => 0) 0) = some true := by
  decide +kernel

def backtrackH : Fin 4 → ℕ := ![0, 2, 2, 1]
def backtrackFees : Fin 4 → ℚ := ![0, 0, 1, 0]
def deadFirst : Fin 4 → ℕ := ![0, 1, 0, 0]
def goodFirst : Fin 4 → ℕ := ![0, 1, 1, 0]
def goodLast : Fin 4 → ℕ := ![0, 1, 1, 1]

/-- The actual fixed enumeration starts with an eligible row whose continuation fails. -/
theorem backtrack_first_eligible :
    (TreeBudgetFiniteSearch.candidates pathFour backtrackH backtrackFees 2).head? =
      some deadFirst ∧ (∀ v, deadFirst v ≤ backtrackH v) := by decide +kernel

theorem backtrack_first_fails :
    searchRows pathFour backtrackH backtrackFees 2 1 (backtrackH - deadFirst) = none := by
  decide +kernel

theorem backtrack_later_succeeds :
    searchRows pathFour backtrackH backtrackFees 2 2 backtrackH =
      some [goodFirst, goodLast] := by decide +kernel

theorem backtrack_output_checked :
    (search pathFour backtrackH 2 backtrackFees 2).map
      (checkCertificate pathFour backtrackH 2 backtrackFees 2) = some true := by decide +kernel

theorem zero_steps_deep_residual_reject :
    searchRows pathFour ![0, 1, 1, 0] (fun _ => 0) 100 0 ![0, 0, 1, 0] = none := by
  decide +kernel

theorem zero_residual_positive_steps_reject :
    searchRows centerThree repeatH (fun _ => 0) 0 1 0 = none := by decide +kernel

/-- Without the guard, truncated subtraction would accept this single oversized row. -/
theorem oversized_transition_reject :
    searchRowsWith [![0, 1, 2, 0]] 1 ![0, 1, 1, 0] = none := by decide +kernel

theorem root_nonzero_input_checked :
    (search centerThree directCounts 5 directFees 10).map
      (checkCertificate centerThree directCounts 5 directFees 10) = some true := by decide +kernel

theorem empty_negative_budget_checked :
    (search depotOnly (fun _ => 99) 0 (fun _ => 999) (-1)).map
      (checkCertificate depotOnly (fun _ => 99) 0 (fun _ => 999) (-1)) = some true := by
  decide +kernel

theorem zero_demand_empty_fleet :
    (search pathFour (fun _ => 0) 0 (fun _ => 0) (-1)).isSome = true := by decide +kernel

theorem no_valid_patterns_reject :
    (search centerThree ![1, 99, 0] 1 (fun _ => 0) (-1)).isSome = false := by decide +kernel

theorem wrong_fleet_reject :
    (search centerThree directCounts 4 directFees 10).isSome = false := by decide +kernel

theorem same_branch_negative_cancellation :
    (search pathFour ![7, 1, 1, 1] 1 ![999, 0, 6, -8] 4).map
      (checkCertificate pathFour ![7, 1, 1, 1] 1 ![999, 0, 6, -8] 4) = some true := by
  decide +kernel

theorem other_branch_negative_cannot_rescue :
    (search centerThree ![1, 99, 1] 2 ![11, 999, -100] 10).isSome = false := by decide +kernel

theorem reference_flags_agree :
    (search pathFour backtrackH 2 backtrackFees 2).isSome =
      (TreeBudgetFiniteSearch.search pathFour backtrackH 2 backtrackFees 2).isSome := by
  decide +kernel

end UAVProof.TreeBudgetResidualExamples

#print axioms UAVProof.TreeBudgetResidualExamples.repeat_same_row_twice
#print axioms UAVProof.TreeBudgetResidualExamples.backtrack_first_fails
#print axioms UAVProof.TreeBudgetResidualExamples.backtrack_later_succeeds
#print axioms UAVProof.TreeBudgetResidualExamples.oversized_transition_reject
#print axioms UAVProof.TreeBudgetResidualExamples.root_nonzero_input_checked
#print axioms UAVProof.TreeBudgetResidualExamples.same_branch_negative_cancellation
