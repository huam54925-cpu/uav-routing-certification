import LeanCompletion.UAV.FixedFlowObstruction
import LeanCompletion.UAV.StructuralServiceCuts

/-!
# The original fixed-flow counterexample violates the general structural cut

Verification: local Lake build passed on 2026-10-23 with Lean 4.30.0-rc2.
See docs/SERVICE_CUTS_VERIFICATION.md for commands and cache limitations.

This file preserves the original instance and reuses its feasible packing,
feasible alternative routes, and aggregate-condition certificate.
The NEW infeasibility proof goes through fixed_flow_integer_structural_cut.
It does not invoke the original no_dominated_cover or no_exact_decomposition.

Only closed finite/numerical certificates use `decide +kernel`.
No enumeration of route families is performed.
The service semantics remain: every visit to a task incurs its service cost.
-/

namespace UAVProof.FixedFlowStructuralCutExample

open ResourceCuts FixedFlowObstruction

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The original edge support has the two forced-successor properties. -/
theorem fixed_flow_pattern :
    StructuralServiceCuts.ForcedReturnPattern
      (fun i j : Node => fixedFlow i j ≠ 0) (0 : Node) 1 2 where
  a_ne_depot := by decide
  b_ne_depot := by decide
  a_ne_b := by decide
  start := by decide +kernel
  after_b := by decide +kernel

/-- All the original depot-free rounded capacity cuts still hold. -/
theorem ordinary_cuts_hold :
    ∀ S : Finset Node, (0 : Node) ∉ S →
      Int.ceil (requiredServiceIn S service required / capacity) ≤
        (outCutFlow S fixedFlow : ℤ) :=
  fixed_flow_aggregate_conditions.roundedCuts

/-- Required route count after charging each b service with its forced a visit. -/
noncomputable def structuralRequiredRoutes : ℤ :=
  Int.ceil (((service 1 + service 2) * (required 2 : ℚ)) /
    (capacity - service 1))

/-- The particular structural cut, evaluated with the original instance data. -/
def StructuralCutHolds (x : Node → Node → ℕ) : Prop :=
  structuralRequiredRoutes ≤ (outCutFlow ({2} : Finset Node) x : ℤ)

theorem structural_required_routes_eq_two : structuralRequiredRoutes = 2 := by
  decide +kernel

theorem fixed_flow_b_cut_eq_one : outCutFlow ({2} : Finset Node) fixedFlow = 1 := by
  decide +kernel

/-- The original fixed flow violates the general structural cut: 2 is not <= 1. -/
theorem fixed_flow_violates_structural_cut : ¬ StructuralCutHolds fixedFlow := by
  intro h
  change structuralRequiredRoutes ≤ (outCutFlow ({2} : Finset Node) fixedFlow : ℤ) at h
  rw [structural_required_routes_eq_two, fixed_flow_b_cut_eq_one] at h
  norm_num at h

section Fleets

variable {ι : Type*}

/-- Any budget-feasible covering family dominated by fixedFlow would satisfy
the structural cut. This is the actual application of the generic theorem. -/
theorem structural_cut_of_dominated_cover
    (ks : Finset ι) (routes : ι → LegalRoute (0 : Node))
    (hdom : ∀ i j, totalRouteFlow ks routes i j ≤ fixedFlow i j)
    (hcover : totalVisitCount ks routes (2 : Node) = required 2)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ capacity) :
    StructuralCutHolds fixedFlow := by
  have ha : (1 : Node) ∈ tasks := by decide
  have hb : (2 : Node) ∈ tasks := by decide
  have hservice : ∀ i ∈ tasks, (0 : ℚ) ≤ service i := by decide +kernel
  have hremaining : (0 : ℚ) < capacity - service 1 := by decide +kernel
  exact StructuralServiceCuts.fixed_flow_integer_structural_cut
    fixedFlow fixed_flow_pattern ks routes tasks service capacity (required 2)
    ha hb hservice hdom hcover hbudget hremaining

/-- Infeasibility now follows solely from the necessary cut and its violation. -/
theorem no_dominated_cover_via_structural_cut
    (ks : Finset ι) (routes : ι → LegalRoute (0 : Node))
    (hdom : ∀ i j, totalRouteFlow ks routes i j ≤ fixedFlow i j)
    (hcover : totalVisitCount ks routes (2 : Node) = required 2)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ capacity) :
    False := by
  exact fixed_flow_violates_structural_cut
    (structural_cut_of_dominated_cover ks routes hdom hcover hbudget)

/-- Exact edge-flow recovery supplies coverage from the route degree identity. -/
theorem no_exact_decomposition_via_structural_cut
    (ks : Finset ι) (routes : ι → LegalRoute (0 : Node))
    (hflow : totalRouteFlow ks routes = fixedFlow)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ capacity) :
    False := by
  have hcover : totalVisitCount ks routes (2 : Node) = required 2 := by
    calc
      totalVisitCount ks routes (2 : Node) =
          outFlow Finset.univ (totalRouteFlow ks routes) (2 : Node) :=
        (total_outFlow_eq_visit_count ks routes (2 : Node) (by decide)).symm
      _ = outFlow Finset.univ fixedFlow (2 : Node) := by rw [hflow]
      _ = required 2 := by decide +kernel
  exact no_dominated_cover_via_structural_cut ks routes
    (fun i j => (congrFun (congrFun hflow i) j).le) hcover hbudget

end Fleets

/-- Complete separation witness: packing and alternative routing are feasible;
all original aggregate conditions hold; the support satisfies the pattern;
the structural cut fails; hence the prescribed flow has no feasible decomposition.
The final exclusion uses the new generic cut, not the old exclusion theorem. -/
theorem ordinary_cuts_pass_but_structural_cut_excludes :
    PackingFeasible ∧
    (∃ routes : Fin 2 → LegalRoute (0 : Node),
      (∀ i, i ≠ (0 : Node) → totalVisitCount Finset.univ routes i = required i) ∧
      (∀ r, routeServiceIn (routes r) tasks service ≤ capacity)) ∧
    AggregateConditions fixedFlow ∧
    StructuralServiceCuts.ForcedReturnPattern
      (fun i j : Node => fixedFlow i j ≠ 0) (0 : Node) 1 2 ∧
    ¬ StructuralCutHolds fixedFlow ∧
    ¬ ∃ routes : Fin 2 → LegalRoute (0 : Node),
      totalRouteFlow Finset.univ routes = fixedFlow ∧
      (∀ r, routeServiceIn (routes r) tasks service ≤ capacity) := by
  refine ⟨packing_feasible, ?_, fixed_flow_aggregate_conditions,
    fixed_flow_pattern, fixed_flow_violates_structural_cut, ?_⟩
  · exact ⟨feasibleRoutes, feasible_routes_cover, fun r => (feasible_routes_budget r).le⟩
  · rintro ⟨routes, hflow, hbudget⟩
    exact no_exact_decomposition_via_structural_cut Finset.univ routes hflow
      (fun r _ => hbudget r)

#print axioms fixed_flow_pattern
#print axioms ordinary_cuts_hold
#print axioms structural_required_routes_eq_two
#print axioms fixed_flow_b_cut_eq_one
#print axioms fixed_flow_violates_structural_cut
#print axioms structural_cut_of_dominated_cover
#print axioms no_dominated_cover_via_structural_cut
#print axioms no_exact_decomposition_via_structural_cut
#print axioms ordinary_cuts_pass_but_structural_cut_excludes

end UAVProof.FixedFlowStructuralCutExample
