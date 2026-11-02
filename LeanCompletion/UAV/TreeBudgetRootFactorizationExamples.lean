import LeanCompletion.UAV.TreeBudgetRootFactorization
import LeanCompletion.UAV.TreeBudgetCheckerExamples

/-! Regression checks of the factorization interfaces, including empty and signed cases. -/
namespace UAVProof.TreeBudgetRootFactorizationExamples
open TreeFlowExistence TreeBudgetPatterns TreeBudgetMatrix TreeBudgetCriterion
open TreeBudgetRootFactorization TreeBudgetCertificate TreeBudgetFiniteSearch
open TreeBudgetChecker TreeBudgetExamples TreeFlowExamples

def leftChild : RootChild centerThree := ⟨0, by decide +kernel⟩
def rightChild : RootChild centerThree := ⟨2, by decide +kernel⟩
def pathChild : RootChild pathFour := ⟨1, by decide +kernel⟩

theorem zero_branch_negative_budget :
    LocalCountsFeasible centerThree (fun _ => 0) (fun _ => 0) (-1) leftChild :=
  (zero_branch_iff _ _ _ _ _ rfl).mpr (by intros; rfl)

theorem zero_root_positive_descendant :
    ¬ LocalCountsFeasible pathFour ![0, 0, 1, 0] (fun _ => 0) 100 pathChild := by
  intro hl
  have hz := (zero_branch_iff _ _ _ _ _ rfl).mp hl 2 (by decide +kernel)
  change (1 : ℕ) = 0 at hz
  omega

theorem two_branches_feasible :
    ∀ c : RootChild centerThree, LocalCountsFeasible centerThree ![1, 0, 1]
      ![10, 999, 2] 10 c := by
  have hm : MatrixFeasible centerThree ![1, 0, 1] 2 ![10, 999, 2] 10 :=
    (search_correct ..).mp (by decide +kernel)
  exact ((matrix_iff_root_local ..).mp hm).2

theorem two_branches_merge :
    MatrixFeasible centerThree ![1, 0, 1] 2 ![10, 999, 2] 10 := by
  apply (matrix_iff_root_local ..).mpr
  exact ⟨by decide +kernel, two_branches_feasible⟩

theorem signed_other_branch_cannot_rescue :
    ¬ LocalCountsFeasible centerThree ![1, 0, 1] ![11, 999, -100] 10 leftChild := by
  rw [local_counts_iff_matrix, ← search_correct]
  decide +kernel

theorem signed_global_impossible :
    ¬ MatrixFeasible centerThree ![1, 0, 1] 2 ![11, 999, -100] 10 := by
  intro hm
  exact signed_other_branch_cannot_rescue (((matrix_iff_root_local ..).mp hm).2 leftChild)

theorem single_branch_signed_cancellation :
    LocalCountsFeasible pathFour ![0, 1, 1, 1] ![999, 0, 6, -8] 4 pathChild := by
  rw [local_counts_iff_matrix, ← search_correct]
  decide +kernel

theorem child_multiplicity_exceeds_parent :
    LocalCountsFeasible pathFour ![0, 1, 2, 0] (fun _ => 0) 0 pathChild := by
  rw [local_counts_iff_matrix, ← search_correct]
  decide +kernel

theorem wrong_fleet_rejected :
    ¬ MatrixFeasible centerThree ![1, 0, 1] 1 ![10, 999, 2] 10 := by
  intro hm
  have hh := (matrix_iff_root_local ..).mp hm |>.1
  have hn : rootCount centerThree ![1, 0, 1] = 2 := by decide +kernel
  omega

theorem demand_interface_signed :
    FlowCompatible pathFour ![0, 2, 2, 1] 1 ∧
    ∀ c : RootChild pathFour,
      LocalCountsFeasible pathFour
        (normalize pathFour (fun v => (requirement pathFour ![0, 2, 2, 1] v).toNat))
        ![999, 0, 6, -8] 4 c := by
  apply (budget_routes_iff_root_local ..).mp
  exact (check_eq_true_iff ..).mp TreeBudgetCheckerExamples.signed_exact_budget_accept

theorem internal_children_share_budget :
    ¬ MatrixFeasible TreeBudgetCheckerExamples.hubTree ![0, 1, 1, 1, 0] 1
      ![999, 0, 6, 6, 0] 10 := by
  rw [← search_correct]
  decide +kernel

theorem single_child_no_reduction (h : Fin 4 → ℕ) (m : ℕ) (s : Fin 4 → ℚ) (T : ℚ) :
    MatrixFeasible pathFour h m s T ↔ m = h 1 ∧ LocalCountsFeasible pathFour h s T pathChild :=
  single_branch_matrix_iff pathFour h m s T pathChild (by decide +kernel)

theorem depot_only_empty_fleet {V : Type*} [Fintype V] [DecidableEq V]
    (R : RootedTree V) (hr : ∀ v, v = R.root) (h : V → ℕ) (s : V → ℚ) (T : ℚ) :
    MatrixFeasible R h 0 s T := (root_only_matrix_iff R h 0 s T hr).mpr rfl

end UAVProof.TreeBudgetRootFactorizationExamples

#print axioms UAVProof.TreeBudgetRootFactorizationExamples.zero_branch_negative_budget
#print axioms UAVProof.TreeBudgetRootFactorizationExamples.zero_root_positive_descendant
#print axioms UAVProof.TreeBudgetRootFactorizationExamples.two_branches_merge
#print axioms UAVProof.TreeBudgetRootFactorizationExamples.signed_global_impossible
#print axioms UAVProof.TreeBudgetRootFactorizationExamples.single_branch_signed_cancellation
#print axioms UAVProof.TreeBudgetRootFactorizationExamples.child_multiplicity_exceeds_parent
#print axioms UAVProof.TreeBudgetRootFactorizationExamples.demand_interface_signed
#print axioms UAVProof.TreeBudgetRootFactorizationExamples.internal_children_share_budget
#print axioms UAVProof.TreeBudgetRootFactorizationExamples.single_child_no_reduction
#print axioms UAVProof.TreeBudgetRootFactorizationExamples.depot_only_empty_fleet
#print axioms UAVProof.TreeBudgetRootFactorizationExamples.two_branches_feasible
#print axioms UAVProof.TreeBudgetRootFactorizationExamples.signed_other_branch_cannot_rescue
#print axioms UAVProof.TreeBudgetRootFactorizationExamples.wrong_fleet_rejected
