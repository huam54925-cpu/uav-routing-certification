import LeanCompletion.UAV.TreeBudgetMemoIntegration
import LeanCompletion.UAV.TreeBudgetResidualExamples
import LeanCompletion.UAV.TreeBudgetLinearCostExamples

/-! Kernel-evaluated regressions for actual memoized execution, including the
cache returned by failed subcalls. Warm calls check both answer and cache.
The diamond test uses a complete, explicitly ordered list of legal rows. -/
namespace UAVProof.TreeBudgetMemoExamples
open TreeBudgetMemoState TreeBudgetMemoSearch TreeBudgetMemoIntegration
open TreeBudgetPatterns TreeBudgetCertificate TreeBudgetChecker TreeBudgetRow
open TreeBudgetExamples TreeFlowExamples TreeBudgetBranchExamples TreeBudgetResidualExamples

def zeroOut := memoRows centerThree repeatH (fun _ => 0) 0 0 0 emptyCache

theorem zero_steps_zero_residual :
    zeroOut.1 = some [] ∧ lookup zeroOut.2 (0, 0) = some (some []) := by decide +kernel

theorem zero_steps_deep_residual :
    (memoRows pathFour ![0, 1, 1, 0] (fun _ => 0) 100 0 ![0, 0, 1, 0] emptyCache).1 =
      none := by decide +kernel

/-- The raw residual API checks even the root coordinate; only the initial
certificate wrapper normalizes an input. -/
theorem zero_steps_root_residual :
    (memoRows centerThree repeatH (fun _ => 0) 0 0 ![0, 1, 0] emptyCache).1 = none := by
  decide +kernel

def oneZeroOut := memoRows centerThree repeatH (fun _ => 0) 0 1 0 zeroOut.2

theorem same_residual_distinct_steps :
    oneZeroOut.1 = none ∧ lookup oneZeroOut.2 (0, 0) = some (some []) ∧
      lookup oneZeroOut.2 (1, 0) = some none := by decide +kernel

theorem empty_success_warm_hit :
    memoRows centerThree repeatH (fun _ => 0) 0 0 0 zeroOut.2 = zeroOut := by decide +kernel

theorem failure_warm_hit :
    memoRows centerThree repeatH (fun _ => 0) 0 1 0 oneZeroOut.2 = oneZeroOut := by decide +kernel

def repeatOut := memoRows centerThree repeatH (fun _ => 0) 0 2 repeatH emptyCache

theorem repeated_pattern_success : repeatOut.1 = some [repeatRow, repeatRow] := by decide +kernel

theorem repeated_pattern_cached_states :
    lookup repeatOut.2 (2, repeatH) = some (some [repeatRow, repeatRow]) ∧
      lookup repeatOut.2 (1, repeatRow) = some (some [repeatRow]) ∧
      lookup repeatOut.2 (0, 0) = some (some []) ∧ repeatOut.2.length = 3 := by decide +kernel

theorem nonempty_success_warm_hit :
    memoRows centerThree repeatH (fun _ => 0) 0 2 repeatH repeatOut.2 = repeatOut := by
  decide +kernel

def backtrackOut := memoRows pathFour backtrackH backtrackFees 2 2 backtrackH emptyCache

/-- The first eligible candidate fails, but its learned failure survives the
successful later candidate. In particular, the parent is not cached as failed. -/
theorem backtrack_failure_retained_and_parent_succeeds :
    backtrackOut.1 = some [goodFirst, goodLast] ∧
      lookup backtrackOut.2 (1, backtrackH - deadFirst) = some none ∧
      lookup backtrackOut.2 (2, backtrackH) = some (some [goodFirst, goodLast]) := by
  decide +kernel

theorem backtrack_success_warm_hit :
    memoRows pathFour backtrackH backtrackFees 2 2 backtrackH backtrackOut.2 = backtrackOut := by
  decide +kernel

def diamondA : Fin 3 → ℕ := ![1, 0, 0]
def diamondB : Fin 3 → ℕ := ![0, 0, 1]
def diamondH : Fin 3 → ℕ := ![1, 0, 1]
def diamondPs := [diamondA, diamondB]
def diamondLeft := memoRowsWith diamondPs 2 (diamondH - diamondA) emptyCache
def diamondRight := memoRowsWith diamondPs 2 (diamondH - diamondB) diamondLeft.2
def diamondOut := memoRowsWith diamondPs 3 diamondH emptyCache

theorem diamond_candidates_complete :
    (TreeBudgetFiniteSearch.candidates centerThree diamondH (fun _ => 0) 0).Perm diamondPs := by
  decide +kernel

/-- Both choice orders lead to exactly the same full key, (1,0).
The left subtree supplies that failure to the right subtree's child call. -/
theorem different_orders_reuse_learned_failure :
    diamondH - diamondA - diamondB = diamondH - diamondB - diamondA ∧
      lookup diamondLeft.2 (1, diamondH - diamondB - diamondA) = some none ∧
      memoRowsWith diamondPs 1 (diamondH - diamondB - diamondA) diamondLeft.2 =
        (none, diamondLeft.2) ∧
      diamondRight.2.length = diamondLeft.2.length + 1 := by decide +kernel

/-- Four distinct states suffice: the parent, its two children, and their
shared child. This count is about this concrete execution, not asymptotics. -/
theorem diamond_complete_run :
    diamondOut.1 = none ∧ diamondOut.2.length = 4 ∧
      lookup diamondOut.2 (1, 0) = some none ∧
      lookup diamondOut.2 (2, diamondH - diamondA) = some none ∧
      lookup diamondOut.2 (2, diamondH - diamondB) = some none := by decide +kernel

theorem diamond_keys_distinct : KeysNodup diamondOut.2 := by
  unfold KeysNodup
  decide +kernel

/-- An oversized row must not recurse into the truncated zero residual. -/
theorem oversized_transition_skipped :
    (memoRowsWith [![0, 1, 2, 0]] 1 ![0, 1, 1, 0] emptyCache).1 = none ∧
      lookup (memoRowsWith [![0, 1, 2, 0]] 1 ![0, 1, 1, 0] emptyCache).2 (0, 0) = none ∧
      (memoRowsWith [![0, 1, 2, 0]] 1 ![0, 1, 1, 0] emptyCache).2.length = 1 := by
  decide +kernel

theorem signed_virtual_fee_exact_boundary :
    (searchMemo pathFour TreeBudgetLinearCostExamples.p 1
      TreeBudgetLinearCostExamples.sigma 12).map
      (checkCertificate pathFour TreeBudgetLinearCostExamples.p 1
        TreeBudgetLinearCostExamples.sigma 12) = some true ∧
      (searchMemo pathFour TreeBudgetLinearCostExamples.p 1
        TreeBudgetLinearCostExamples.sigma 11).isSome = false := by decide +kernel

theorem initial_root_normalized_and_checked :
    (searchMemo centerThree ![2, 99, 0] 2 (fun _ => 0) 0).map
      (checkCertificate centerThree ![2, 99, 0] 2 (fun _ => 0) 0) = some true := by
  decide +kernel

theorem multiple_branches_checked :
    (searchByRootMemo centerThree directCounts 5 directFees 10).map
      (checkCertificate centerThree directCounts 5 directFees 10) = some true := by
  decide +kernel

theorem zero_root_deep_positive_reject :
    (searchByRootMemo pathFour ![7, 0, 1, 0] 0 (fun _ => 0) 100).isSome = false := by
  decide +kernel

theorem wrong_fleet_reject :
    (searchByRootMemo centerThree directCounts 4 directFees 10).isSome = false := by
  decide +kernel

theorem depot_only_negative_budget_checked :
    (searchByRootMemo depotOnly (fun _ => 999) 0 (fun _ => 999) (-1)).map
      (checkCertificate depotOnly (fun _ => 999) 0 (fun _ => 999) (-1)) = some true := by
  decide +kernel

theorem other_branch_negative_cannot_rescue :
    (searchByRootMemo centerThree ![1, 99, 1] 2 ![11, 999, -100] 10).isSome = false := by
  decide +kernel

theorem incompatible_demand_reject :
    (solveByRootMemo pathFour ![0, 0, 0, 1] 1 (fun _ => 0) 100).isSome = false := by
  decide +kernel

theorem compatible_but_disconnected_reject :
    compatible pathFour ![0, 1, 1, 0] 0 = true ∧
      (solveByRootMemo pathFour ![0, 1, 1, 0] 0 (fun _ => 0) 100).isSome = false := by
  decide +kernel

theorem demand_signed_checked :
    (solveByRootMemo pathFour ![999, 2, 2, 1] 1 ![999, 0, 6, -8] 4).map
      (checkCertificate pathFour (multiplicities pathFour ![999, 2, 2, 1])
        1 ![999, 0, 6, -8] 4) = some true := by decide +kernel

theorem repeated_rows_compressed :
    (searchMemoCompressed centerThree ![2, 99, 0] 2 (fun _ => 0) 0).map
      TreeBudgetBranchCertificate.entries = some [(repeatRow, 2)] := by decide +kernel

theorem branch_compression_checked :
    (searchByRootMemoCompressed centerThree directCounts 5 directFees 10).map
      (fun C => (C.size, checkCertificate centerThree directCounts 5 directFees 10 C)) =
        some (2, true) := by decide +kernel

theorem demand_compression_checked :
    (solveByRootMemoCompressed pathFour ![999, 2, 2, 1] 1 ![999, 0, 6, -8] 4).map
      (checkCertificate pathFour (multiplicities pathFour ![999, 2, 2, 1])
        1 ![999, 0, 6, -8] 4) = some true := by decide +kernel

theorem old_search_flags_agree :
    backtrackOut.1.isSome =
      (TreeBudgetResidualSearch.searchRows
        pathFour backtrackH backtrackFees 2 2 backtrackH).isSome ∧
      diamondOut.1.isSome =
        (TreeBudgetResidualSearch.searchRowsWith diamondPs 3 diamondH).isSome := by
  decide +kernel

end UAVProof.TreeBudgetMemoExamples

#print axioms UAVProof.TreeBudgetMemoExamples.zero_steps_zero_residual
#print axioms UAVProof.TreeBudgetMemoExamples.zero_steps_deep_residual
#print axioms UAVProof.TreeBudgetMemoExamples.zero_steps_root_residual
#print axioms UAVProof.TreeBudgetMemoExamples.same_residual_distinct_steps
#print axioms UAVProof.TreeBudgetMemoExamples.empty_success_warm_hit
#print axioms UAVProof.TreeBudgetMemoExamples.failure_warm_hit
#print axioms UAVProof.TreeBudgetMemoExamples.repeated_pattern_success
#print axioms UAVProof.TreeBudgetMemoExamples.repeated_pattern_cached_states
#print axioms UAVProof.TreeBudgetMemoExamples.nonempty_success_warm_hit
#print axioms UAVProof.TreeBudgetMemoExamples.backtrack_failure_retained_and_parent_succeeds
#print axioms UAVProof.TreeBudgetMemoExamples.backtrack_success_warm_hit
#print axioms UAVProof.TreeBudgetMemoExamples.diamond_candidates_complete
#print axioms UAVProof.TreeBudgetMemoExamples.different_orders_reuse_learned_failure
#print axioms UAVProof.TreeBudgetMemoExamples.diamond_complete_run
#print axioms UAVProof.TreeBudgetMemoExamples.diamond_keys_distinct
#print axioms UAVProof.TreeBudgetMemoExamples.oversized_transition_skipped
#print axioms UAVProof.TreeBudgetMemoExamples.signed_virtual_fee_exact_boundary
#print axioms UAVProof.TreeBudgetMemoExamples.initial_root_normalized_and_checked
#print axioms UAVProof.TreeBudgetMemoExamples.multiple_branches_checked
#print axioms UAVProof.TreeBudgetMemoExamples.zero_root_deep_positive_reject
#print axioms UAVProof.TreeBudgetMemoExamples.wrong_fleet_reject
#print axioms UAVProof.TreeBudgetMemoExamples.depot_only_negative_budget_checked
#print axioms UAVProof.TreeBudgetMemoExamples.other_branch_negative_cannot_rescue
#print axioms UAVProof.TreeBudgetMemoExamples.incompatible_demand_reject
#print axioms UAVProof.TreeBudgetMemoExamples.compatible_but_disconnected_reject
#print axioms UAVProof.TreeBudgetMemoExamples.demand_signed_checked
#print axioms UAVProof.TreeBudgetMemoExamples.repeated_rows_compressed
#print axioms UAVProof.TreeBudgetMemoExamples.branch_compression_checked
#print axioms UAVProof.TreeBudgetMemoExamples.demand_compression_checked
#print axioms UAVProof.TreeBudgetMemoExamples.old_search_flags_agree
