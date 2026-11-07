import LeanCompletion.UAV.HubAssignmentChecker
import LeanCompletion.UAV.HubThreePartitionExamples

/-!
# Assignment-checker regressions

The finite checks use kernel reduction. Rejecting a supplied assignment is
separate from rejecting an instance. Raw-list tests cover shape errors before
budget verification. No source validity hypothesis is imposed by the checker.
-/

namespace UAVProof.HubAssignmentCheckerExamples

open HubThreePartition HubThreePartitionExamples HubAssignmentChecker

def goodAssignment : Item 2 → Fin 2 := ![0, 0, 0, 1, 1, 1]

theorem good_assignment_accepted : checkAssignment goodWeights 30 goodAssignment = true := by
  decide +kernel

theorem good_list_accepted : checkAssignmentList goodWeights 30 [0, 0, 0, 1, 1, 1] = true := by
  decide +kernel

/-- The same feasible instance has a rejected assignment. -/
theorem wrong_assignment_rejected_but_instance_feasible :
    checkAssignment goodWeights 30 (fun _ => 0) = false ∧ RoutingFeasible goodWeights 30 := by
  constructor
  · decide +kernel
  · exact feasible_exact_routing

theorem wrong_list_rejected : checkAssignmentList goodWeights 30 [0, 0, 0, 0, 0, 0] = false := by
  decide +kernel

theorem bad_no_accepted_assignment : ¬ ∃ q, checkAssignment badWeights 30 q = true := by
  intro h
  exact infeasible_exact_routing ((routing_iff_exists_accepted_assignment badWeights 30).mpr h)

theorem bad_no_accepted_list : ¬ ∃ c, checkAssignmentList badWeights 30 c = true := by
  intro h
  exact infeasible_exact_routing ((routing_iff_exists_accepted_list badWeights 30).mpr h)

/-- The empty fleet has exactly the empty raw assignment, at every budget. -/
theorem empty_list_accepted (B : ℕ) : checkAssignmentList emptyWeights B [] = true := by
  rfl

theorem empty_zero_budget_routing : RoutingFeasible emptyWeights 0 := by
  exact (routing_iff_exists_accepted_list emptyWeights 0).mpr ⟨[], empty_list_accepted 0⟩

theorem empty_nonempty_list_rejected : checkAssignmentList emptyWeights 0 [0] = false := by
  decide +kernel

def zeroWeights : Item 2 → ℕ := fun _ => 0

theorem zero_cost_zero_budget_accepts_every_assignment (q : Item 2 → Fin 2) :
    checkAssignment zeroWeights 0 q = true := by
  apply (checkAssignment_eq_true_iff zeroWeights 0 q).mpr
  intro r
  simp [assignmentLoad, zeroWeights]

theorem zero_cost_zero_budget_list_accepted :
    checkAssignmentList zeroWeights 0 [0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem zero_cost_zero_budget_routing : RoutingFeasible zeroWeights 0 := by
  exact (routing_iff_exists_accepted_assignment zeroWeights 0).mpr
    ⟨goodAssignment, zero_cost_zero_budget_accepts_every_assignment goodAssignment⟩

def unitWeights : Item 2 → ℕ := fun _ => 1

theorem empty_row_accepted : checkAssignment unitWeights 6 (fun _ => 0) = true := by
  decide +kernel

/-- An empty assignment row is represented by the existing hub-only route. -/
theorem empty_row_hub_only :
    group (fun _ : Item 2 => (0 : Fin 2)) 1 = ∅ ∧
    (HubSpokePacking.route ([] : List (Item 2))).visits = [HubSpokeSupportExact.hub] ∧
    RoutingFeasible unitWeights 6 := by
  refine ⟨?_, rfl, ?_⟩
  · decide +kernel
  · exact (routing_iff_exists_accepted_assignment unitWeights 6).mpr
      ⟨fun _ => 0, empty_row_accepted⟩

theorem short_list_rejected : checkAssignmentList goodWeights 30 [0, 0, 0, 1, 1] = false := by
  decide +kernel

theorem long_list_rejected : checkAssignmentList goodWeights 30 [0, 0, 0, 1, 1, 1, 1] = false := by
  decide +kernel

theorem out_of_range_list_rejected :
    checkAssignmentList goodWeights 30 [0, 0, 0, 1, 1, 2] = false := by
  decide +kernel

/-- Source saturation is deliberately absent: this valid target certificate
has total weight twenty-four and two route loads twelve, below budget fifteen. -/
theorem underweight_list_accepted :
    checkAssignmentList underweight 15 [0, 0, 0, 1, 1, 1] = true := by
  decide +kernel

theorem underweight_target_without_source_validity :
    RoutingFeasible underweight 15 ∧ ¬ ValidInput underweight 15 := by
  refine ⟨?_, underweight_strict_bounds_but_wrong_total.2.2⟩
  exact (routing_iff_exists_accepted_list underweight 15).mpr
    ⟨[0, 0, 0, 1, 1, 1], underweight_list_accepted⟩

end UAVProof.HubAssignmentCheckerExamples
