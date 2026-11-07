import LeanCompletion.UAV.HubThreePartition

/-!
# Finite regressions for the strict-hub three-partition correspondence

Concrete decisions use kernel reduction. The examples distinguish semantic
feasibility from the source hypotheses, including both strict numerical bounds
and total-weight saturation. They assert no encoding or hardness result.
-/

namespace UAVProof.HubThreePartitionExamples

open HubThreePartition HubSpokeSupportExact SupportExactFeasibility

def goodWeights : Item 2 → ℕ := ![9, 10, 11, 9, 10, 11]

def badWeights : Item 2 → ℕ := ![9, 9, 9, 13, 10, 10]

theorem feasible_input_valid : ValidInput goodWeights 30 := by
  unfold ValidInput
  decide +kernel

/-- Two explicit triples of weight thirty. Distinct equal-weight items retain
their separate identities. -/
theorem feasible_threePartition : ThreePartition goodWeights 30 := by
  refine ⟨![0, 0, 0, 1, 1, 1], ?_⟩
  decide +kernel

theorem feasible_exact_routing : RoutingFeasible goodWeights 30 := by
  exact (exact_iff_threePartition goodWeights 30 feasible_input_valid).mpr
    feasible_threePartition

/-- The negative instance satisfies every strict source assumption. -/
theorem infeasible_input_valid : ValidInput badWeights 30 := by
  unfold ValidInput
  decide +kernel

theorem infeasible_threePartition : ¬ ThreePartition badWeights 30 := by
  unfold ThreePartition
  decide +kernel

theorem infeasible_exact_routing : ¬ RoutingFeasible badWeights 30 := by
  intro h
  exact infeasible_threePartition
    ((exact_iff_threePartition badWeights 30 infeasible_input_valid).mp h)

def emptyWeights : Item 0 → ℕ := Fin.elim0

theorem empty_input_valid : ValidInput emptyWeights 1 := by
  unfold ValidInput
  decide +kernel

theorem empty_threePartition : ThreePartition emptyWeights 1 := by
  refine ⟨Fin.elim0, ?_⟩
  intro r
  exact Fin.elim0 r

/-- An empty fleet, not one route with an empty task sequence. -/
theorem empty_exact_routing : RoutingFeasible emptyWeights 1 := by
  exact (exact_iff_threePartition emptyWeights 1 empty_input_valid).mpr
    empty_threePartition

/-- Replacing the strict upper bound by a weak one permits two items to
saturate a budget, so the cardinality-three conclusion is lost. -/
theorem upper_bound_equality_allows_two :
    (∀ i : Fin 2, 30 < 4 * (fun _ : Fin 2 => 15) i ∧
      2 * (fun _ : Fin 2 => 15) i ≤ 30) ∧
    (∑ i : Fin 2, (fun _ : Fin 2 => 15) i) = 30 ∧
    (Finset.univ : Finset (Fin 2)).card ≠ 3 := by
  decide +kernel

/-- Replacing the strict lower bound by a weak one permits four items. -/
theorem lower_bound_equality_allows_four :
    (∀ i : Fin 4, 32 ≤ 4 * (fun _ : Fin 4 => 8) i ∧
      2 * (fun _ : Fin 4 => 8) i < 32) ∧
    (∑ i : Fin 4, (fun _ : Fin 4 => 8) i) = 32 ∧
    (Finset.univ : Finset (Fin 4)).card ≠ 3 := by
  decide +kernel

/-- The six leaf visits produce six returns to the hub in addition to two
initial hub visits. Leaf demands and separator multiplicities stay exact. -/
theorem canonical_demands_and_flow :
    required 2 (fun _ : Item 2 => 1) hub = 8 ∧
    (∀ i : Item 2, required 2 (fun _ : Item 2 => 1) (satellite i) = 1) ∧
    canonicalFlow 2 (fun _ : Item 2 => 1) depot hub = 2 ∧
    canonicalFlow 2 (fun _ : Item 2 => 1) hub depot = 2 ∧
    (∀ i : Item 2,
      canonicalFlow 2 (fun _ : Item 2 => 1) hub (satellite i) = 1 ∧
      canonicalFlow 2 (fun _ : Item 2 => 1) (satellite i) hub = 1) := by
  decide +kernel

def underweight : Item 2 → ℕ := fun _ => 4

/-- Strict individual bounds alone do not give row saturation: the total
weight hypothesis is necessary. -/
theorem underweight_strict_bounds_but_wrong_total :
    (∀ i : Item 2, 15 < 4 * underweight i ∧ 2 * underweight i < 15) ∧
    (∑ i, underweight i) = 24 ∧ ¬ ValidInput underweight 15 := by
  unfold ValidInput
  decide +kernel

theorem underweight_unitMatrix : UnitMatrixFeasible underweight 15 := by
  refine ⟨![![1, 1, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1]], ?_, ?_⟩
  all_goals decide +kernel

theorem underweight_exact_routing : RoutingFeasible underweight 15 := by
  exact (routing_iff_unitMatrix underweight 15).mpr underweight_unitMatrix

theorem underweight_no_threePartition : ¬ ThreePartition underweight 15 := by
  unfold ThreePartition
  decide +kernel

end UAVProof.HubThreePartitionExamples

#print axioms UAVProof.HubThreePartitionExamples.feasible_input_valid
#print axioms UAVProof.HubThreePartitionExamples.feasible_threePartition
#print axioms UAVProof.HubThreePartitionExamples.feasible_exact_routing
#print axioms UAVProof.HubThreePartitionExamples.infeasible_input_valid
#print axioms UAVProof.HubThreePartitionExamples.infeasible_threePartition
#print axioms UAVProof.HubThreePartitionExamples.infeasible_exact_routing
#print axioms UAVProof.HubThreePartitionExamples.empty_input_valid
#print axioms UAVProof.HubThreePartitionExamples.empty_threePartition
#print axioms UAVProof.HubThreePartitionExamples.empty_exact_routing
#print axioms UAVProof.HubThreePartitionExamples.upper_bound_equality_allows_two
#print axioms UAVProof.HubThreePartitionExamples.lower_bound_equality_allows_four
#print axioms UAVProof.HubThreePartitionExamples.canonical_demands_and_flow
#print axioms UAVProof.HubThreePartitionExamples.underweight_strict_bounds_but_wrong_total
#print axioms UAVProof.HubThreePartitionExamples.underweight_unitMatrix
#print axioms UAVProof.HubThreePartitionExamples.underweight_exact_routing
#print axioms UAVProof.HubThreePartitionExamples.underweight_no_threePartition
