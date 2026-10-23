import LeanCompletion.UAV.ResourceCuts
import Mathlib.Tactic

/-!
# Packing is feasible, but a prescribed edge flow obstructs every timed routing

Verification: local Lake build passed on 2026-10-23 with Lean 4.30.0-rc2.
See docs/SERVICE_CUTS_VERIFICATION.md for commands and cache limitations.
This imports the already established ResourceCuts interfaces only.

Nodes: depot=0, a=1, b=2, c=3. Service costs: (0,1,2,1).
Required occurrences: (0,3,1,1). Two routes, each with budget 3.
Travel costs and the overhead lower bound tau are zero.

Feasible packing AND actual routes: 0-a-c-a-0 and 0-a-b-0, each of cost 3.
Prescribed flow: 0->a twice; a->0, a->b, b->a, a->c, c->0 once each.
Every route using this support satisfies count(a) = 1 + count(b).
Consequently its service is at least 1 + 3*count(b): a budget-3 route cannot
visit b. This excludes ALL feasible packings on that support, even with
componentwise edge-flow domination rather than exact recovery.

Only the finite numerical certificate and the explicit feasible witness use
decide +kernel. No enumeration of possible obstructed routes is used.
-/

namespace UAVProof.FixedFlowObstruction

open ResourceCuts

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev Node := Fin 4

def tasks : Finset Node := {1, 2, 3}
def service : Node → ℚ := ![0, 1, 2, 1]
def required : Node → ℕ := ![0, 3, 1, 1]
def degree : Node → ℕ := ![2, 3, 1, 1]
def capacity : ℚ := 3

def fixedFlow : Node → Node → ℕ :=
  ![![0, 2, 0, 0], ![1, 0, 1, 1], ![0, 1, 0, 0], ![1, 0, 0, 0]]

/-! A packing of occurrences, not a partition of distinct vertex names. -/

def packing : Fin 2 → Node → ℕ :=
  ![![0, 2, 0, 1], ![0, 1, 1, 0]]

def PackingFeasible : Prop :=
  ∃ counts : Fin 2 → Node → ℕ,
    (∀ i : Node, i ≠ 0 → (∑ r, counts r i) = required i) ∧
    (∀ r : Fin 2, (∑ i ∈ tasks, service i * (counts r i : ℚ)) ≤ capacity)

theorem packing_cover :
    ∀ i : Node, i ≠ 0 → (∑ r : Fin 2, packing r i) = required i := by
  decide +kernel

theorem packing_budget :
    ∀ r : Fin 2, (∑ i ∈ tasks, service i * (packing r i : ℚ)) = capacity := by
  decide +kernel

theorem packing_feasible : PackingFeasible := by
  exact ⟨packing, packing_cover, fun r => (packing_budget r).le⟩

/-! The same instance is routable when the prescribed flow is not imposed. -/

def routeACA : LegalRoute (0 : Node) where
  visits := [1, 3, 1]
  visits_nonempty := by decide
  depot_not_mem := by decide
  adjacent_ne := by decide +kernel

def routeAB : LegalRoute (0 : Node) where
  visits := [1, 2]
  visits_nonempty := by decide
  depot_not_mem := by decide
  adjacent_ne := by decide +kernel

def feasibleRoutes (r : Fin 2) : LegalRoute (0 : Node) :=
  if r = 0 then routeACA else routeAB

theorem feasible_routes_cover :
    ∀ i : Node, i ≠ 0 →
      totalVisitCount Finset.univ feasibleRoutes i = required i := by
  decide +kernel

theorem feasible_routes_budget :
    ∀ r : Fin 2, routeServiceIn (feasibleRoutes r) tasks service = capacity := by
  decide +kernel

theorem feasible_routes_have_different_flow :
    totalRouteFlow Finset.univ feasibleRoutes ≠ fixedFlow := by
  intro h
  have h20 := congrFun (congrFun h (2 : Node)) (0 : Node)
  have hne : totalRouteFlow Finset.univ feasibleRoutes (2 : Node) (0 : Node) ≠
      fixedFlow (2 : Node) (0 : Node) := by decide +kernel
  exact hne h20

/-! All aggregate conditions, including ALL depot-free rounded cuts. -/

structure AggregateConditions (x : Node → Node → ℕ) : Prop where
  outgoing : ∀ i, outFlow Finset.univ x i = degree i
  incoming : ∀ i, inFlow Finset.univ x i = degree i
  noDiagonal : ∀ i, x i i = 0
  arcBounds : ∀ i j, 0 ≤ x i j ∧ x i j ≤ min (degree i) (degree j)
  connected : ∀ S : Finset Node, S.Nonempty → (0 : Node) ∉ S → 1 ≤ outCutFlow S x
  totalBudget : requiredServiceIn tasks service required ≤ 2 * capacity
  roundedCuts : ∀ S : Finset Node, (0 : Node) ∉ S →
    Int.ceil (requiredServiceIn S service required / capacity) ≤ (outCutFlow S x : ℤ)

theorem fixed_flow_aggregate_conditions : AggregateConditions fixedFlow where
  outgoing := by decide +kernel
  incoming := by decide +kernel
  noDiagonal := by decide +kernel
  arcBounds := by decide +kernel
  connected := by decide +kernel
  totalBudget := by decide +kernel
  roundedCuts := by decide +kernel

/-! Structural obstruction: proofs quantify over arbitrary legal routes. -/

/-- A route uses no edge absent from the prescribed support.
This is weaker than requiring exact edge multiplicities. -/
def UsesSupport (r : LegalRoute (0 : Node)) : Prop :=
  ∀ i j : Node, fixedFlow i j = 0 → routeFlow r.vertices i j = 0

/-- Each supported route enters a once from the depot and once after each b visit. -/
theorem forced_visit_count
    (r : LegalRoute (0 : Node)) (hsupport : UsesSupport r) :
    r.visits.count 1 = 1 + r.visits.count 2 := by
  have h00 := hsupport 0 0 (by decide)
  have h02 := hsupport 0 2 (by decide)
  have h03 := hsupport 0 3 (by decide)
  have h20 := hsupport 2 0 (by decide)
  have h22 := hsupport 2 2 (by decide)
  have h23 := hsupport 2 3 (by decide)
  have h11 := hsupport 1 1 (by decide)
  have h31 := hsupport 3 1 (by decide)
  have h01 : routeFlow r.vertices 0 1 = 1 := by
    simpa [outFlow, Fin.sum_univ_succ, h00, h02, h03] using r.outFlow_depot_eq_one
  have h21 : routeFlow r.vertices 2 1 = r.visits.count 2 := by
    simpa [outFlow, Fin.sum_univ_succ, h20, h22, h23] using
      r.outFlow_eq_visit_count (2 : Node) (by decide)
  have ha := r.inFlow_eq_visit_count (1 : Node) (by decide)
  simpa [inFlow, Fin.sum_univ_succ, h11, h31, h01, h21] using ha.symm

/-- A reusable cost bound on this support, for arbitrary costs at a and b
and a nonnegative cost at c. This is not restricted to the numeric witness. -/
theorem forced_service_lower_bound
    (r : LegalRoute (0 : Node)) (hsupport : UsesSupport r)
    (cost : Node → ℚ) (hc : 0 ≤ cost 3) :
    cost 1 + (cost 1 + cost 2) * (r.visits.count 2 : ℚ) ≤
      routeServiceIn r tasks cost := by
  have hcount := forced_visit_count r hsupport
  have hcountQ : (r.visits.count 1 : ℚ) = 1 + (r.visits.count 2 : ℚ) := by
    exact_mod_cast hcount
  have hwork : routeServiceIn r tasks cost =
      cost 1 * (r.visits.count 1 : ℚ) +
      cost 2 * (r.visits.count 2 : ℚ) +
      cost 3 * (r.visits.count 3 : ℚ) := by
    simp [routeServiceIn, tasks] <;> ring
  have hlast := mul_nonneg hc (Nat.cast_nonneg (r.visits.count 3) : (0 : ℚ) ≤ _)
  rw [hwork, hcountQ]
  nlinarith

theorem b_visit_forces_cost_four
    (r : LegalRoute (0 : Node)) (hsupport : UsesSupport r)
    (hb : 0 < r.visits.count 2) :
    (4 : ℚ) ≤ routeServiceIn r tasks service := by
  have hbound :=
    forced_service_lower_bound r hsupport service (by decide)

  have hs1 : service (1 : Node) = (1 : ℚ) := by
    decide +kernel
  have hs2 : service (2 : Node) = (2 : ℚ) := by
    decide +kernel

  rw [hs1, hs2] at hbound

  have hbNat : 1 ≤ r.visits.count 2 := hb
  have hbQ : (1 : ℚ) ≤ (r.visits.count 2 : ℚ) := by
    exact_mod_cast hbNat

  have hcoef : (0 : ℚ) ≤ (1 + 2 : ℚ) := by
    norm_num

  have hmul :
      (1 + 2 : ℚ) * 1 ≤
        (1 + 2 : ℚ) * (r.visits.count 2 : ℚ) :=
    mul_le_mul_of_nonneg_left hbQ hcoef

  calc
    (4 : ℚ) = 1 + (1 + 2) * 1 := by norm_num
    _ ≤ 1 + (1 + 2) * (r.visits.count 2 : ℚ) :=
            add_le_add (le_refl (1 : ℚ)) hmul
    _ ≤ routeServiceIn r tasks service := hbound

theorem budget_route_cannot_visit_b
    (r : LegalRoute (0 : Node)) (hsupport : UsesSupport r)
    (hbudget : routeServiceIn r tasks service ≤ capacity) :
    r.visits.count 2 = 0 := by
  by_contra hne
  have hb : 0 < r.visits.count 2 := Nat.pos_of_ne_zero hne
  have hfour := b_visit_forces_cost_four r hsupport hb
  norm_num [capacity] at hbudget
  linarith

section Fleets

variable {ι : Type*}

/-- Nonnegative edge counts transfer aggregate domination to each selected route. -/
theorem selected_route_uses_support
    (ks : Finset ι) (routes : ι → LegalRoute (0 : Node))
    (hdom : ∀ i j, totalRouteFlow ks routes i j ≤ fixedFlow i j)
    {r : ι} (hr : r ∈ ks) : UsesSupport (routes r) := by
  intro i j hzero
  have hsingle : routeFlow (routes r).vertices i j ≤ totalRouteFlow ks routes i j :=
    Finset.single_le_sum (fun a _ => Nat.zero_le (routeFlow (routes a).vertices i j)) hr
  have hle := hsingle.trans (hdom i j)
  rw [hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- No budget-feasible fleet under the edge capacities can even cover b once.
The obstruction holds for any finite index set, not merely two fixed lists. -/
theorem no_dominated_cover
    (ks : Finset ι) (routes : ι → LegalRoute (0 : Node))
    (hdom : ∀ i j, totalRouteFlow ks routes i j ≤ fixedFlow i j)
    (hcover : totalVisitCount ks routes (2 : Node) = 1)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ capacity) :
    False := by
  have hzero : totalVisitCount ks routes (2 : Node) = 0 := by
    unfold totalVisitCount
    apply Finset.sum_eq_zero
    intro r hr
    exact budget_route_cannot_visit_b (routes r)
      (selected_route_uses_support ks routes hdom hr) (hbudget r hr)
  omega

/-- Exact recovery forces b coverage by the existing route-to-flow degree theorem. -/
theorem no_exact_decomposition
    (ks : Finset ι) (routes : ι → LegalRoute (0 : Node))
    (hflow : totalRouteFlow ks routes = fixedFlow)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ capacity) :
    False := by
  have hcover : totalVisitCount ks routes (2 : Node) = 1 := by
    calc
      totalVisitCount ks routes (2 : Node) =
          outFlow Finset.univ (totalRouteFlow ks routes) (2 : Node) :=
        (total_outFlow_eq_visit_count ks routes (2 : Node) (by decide)).symm
      _ = outFlow Finset.univ fixedFlow (2 : Node) := by rw [hflow]
      _ = 1 := by decide +kernel
  exact no_dominated_cover ks routes
    (fun i j => (congrFun (congrFun hflow i) j).le) hcover hbudget

end Fleets

/-- Packing and actual routing are feasible, all rounded cuts hold for fixedFlow,
yet no budget-feasible route decomposition can recover fixedFlow. -/
theorem packing_feasible_but_fixed_flow_infeasible :
    PackingFeasible ∧
    (∃ routes : Fin 2 → LegalRoute (0 : Node),
      (∀ i, i ≠ (0 : Node) → totalVisitCount Finset.univ routes i = required i) ∧
      (∀ r, routeServiceIn (routes r) tasks service ≤ capacity)) ∧
    AggregateConditions fixedFlow ∧
    ¬ ∃ routes : Fin 2 → LegalRoute (0 : Node),
      totalRouteFlow Finset.univ routes = fixedFlow ∧
      (∀ r, routeServiceIn (routes r) tasks service ≤ capacity) := by
  refine ⟨packing_feasible, ?_, fixed_flow_aggregate_conditions, ?_⟩
  · exact ⟨feasibleRoutes, feasible_routes_cover, fun r => (feasible_routes_budget r).le⟩
  · rintro ⟨routes, hflow, hbudget⟩
    exact no_exact_decomposition Finset.univ routes hflow (fun r _ => hbudget r)

#print axioms packing_feasible
#print axioms feasible_routes_cover
#print axioms feasible_routes_budget
#print axioms fixed_flow_aggregate_conditions
#print axioms forced_visit_count
#print axioms forced_service_lower_bound
#print axioms no_dominated_cover
#print axioms no_exact_decomposition
#print axioms packing_feasible_but_fixed_flow_infeasible

end UAVProof.FixedFlowObstruction
