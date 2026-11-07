import LeanCompletion.UAV.HubNumberedInstance
import LeanCompletion.UAV.HubThreePartitionExamples

/-!
# Regressions for the numbered strict-hub target

The vertex set retains the depot and hub even for an empty fleet. The semantic
correspondence is tested both on valid source instances and on an instance
outside the source promise. A repeated-visit route checks that relabeling
preserves multiplicity and signed service fees.
-/

namespace UAVProof.HubNumberedInstanceExamples

open HubNumberedInstance HubSpokeSupportExact ResourceCuts
open HubThreePartition HubThreePartitionExamples

theorem empty_vertices :
    Fintype.card (Vertex 0) = 2 ∧ depotN 0 ≠ hubN 0 ∧
    nodeEquiv 0 (depotN 0) = depot ∧ nodeEquiv 0 (hubN 0) = hub := by
  decide +kernel

theorem explicit_coordinates :
    nodeEquiv 2 0 = depot ∧ nodeEquiv 2 1 = hub ∧
    nodeEquiv 2 2 = satellite (0 : Item 2) ∧
    nodeEquiv 2 7 = satellite (5 : Item 2) := by
  decide +kernel

theorem explicit_numbered_data :
    numberedDemand 2 0 = 0 ∧ numberedDemand 2 1 = 8 ∧
    numberedDemand 2 7 = 1 ∧
    numberedFlow 2 0 1 = 2 ∧ numberedFlow 2 1 0 = 2 ∧
    numberedFlow 2 1 7 = 1 ∧ numberedFlow 2 7 1 = 1 ∧
    numberedFlow 2 0 7 = 0 ∧ numberedFlow 2 2 7 = 0 ∧
    numberedService goodWeights 0 = 0 ∧
    numberedService goodWeights 1 = 0 ∧
    numberedService goodWeights 7 = 11 := by
  decide +kernel

theorem empty_numbered_routing : NumberedRoutingFeasible emptyWeights 1 :=
  (numbered_routing_iff emptyWeights 1).mpr empty_exact_routing

theorem feasible_numbered_routing : NumberedRoutingFeasible goodWeights 30 :=
  (numbered_routing_iff goodWeights 30).mpr feasible_exact_routing

theorem infeasible_numbered_routing : ¬ NumberedRoutingFeasible badWeights 30 := by
  intro h
  exact infeasible_exact_routing ((numbered_routing_iff badWeights 30).mp h)

/-- Relabeling does not assume the source three-partition promise. -/
theorem underweight_numbered_routing : NumberedRoutingFeasible underweight 15 :=
  (numbered_routing_iff underweight 15).mpr underweight_exact_routing

def repeatedRoute : LegalRoute (depotN 1) where
  visits := [1, 2, 1, 2, 1]
  visits_nonempty := by decide +kernel
  depot_not_mem := by decide +kernel
  adjacent_ne := by decide +kernel

theorem repeated_route_count :
    (Relabel.mapRoute (nodeEquiv 1) repeatedRoute).visits.count
      (satellite (0 : Item 1)) = 2 := by
  have h := Relabel.mapRoute_count (nodeEquiv 1) repeatedRoute (leafN (0 : Item 1))
  simpa [repeatedRoute, leafN] using h

theorem repeated_route_flow :
    routeFlow (Relabel.mapRoute (nodeEquiv 1) repeatedRoute).vertices
      hub (satellite (0 : Item 1)) = 2 := by
  have h := Relabel.mapRoute_flow (nodeEquiv 1) repeatedRoute
    (hubN 1) (leafN (0 : Item 1))
  simpa [repeatedRoute, hubN, leafN, LegalRoute.vertices, depotRoute,
    routeFlow, depotN] using h

def signedService : Node (Item 1) → ℚ
  | none => 999
  | some none => -2
  | some (some _) => 1

theorem repeated_route_signed_service :
    routeServiceIn (Relabel.mapRoute (nodeEquiv 1) repeatedRoute)
      Finset.univ signedService = -4 := by
  rw [Relabel.mapRoute_service]
  decide +kernel

end UAVProof.HubNumberedInstanceExamples
