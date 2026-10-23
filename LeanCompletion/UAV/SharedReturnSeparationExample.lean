import LeanCompletion.UAV.SharedReturnLargeServiceCuts

/-!
# A strict separation witness for effective large-service counting

STATUS: UNCOMPILED DRAFT for the existing Lean 4.30.0-rc2 project.
All finite numeric conditions were independently checked with exact arithmetic;
this source still needs a local Lean check. No existing modules are modified.

Nodes: depot 0, shared-return node a=1, satellites B={2,3,4}, auxiliary c=5.
Costs: (0,1,2,2,2,1). Demands: (0,5,1,1,1,1). Fleet=2, budget=6.
Every task occurrence is charged, including repeated visits to a.
Travel cost is zero. All nondepot tasks have strictly positive service costs.

The fixed flow sends 0->a twice, a->0 once, a->c->0 once, and
a->b->a once for each of the three satellites. All ordinary rounded cuts
and all applicable immediate-return singleton/set volume bounds hold.

Alternative feasible routes: [a,2,3,a] and [a,c,a,4,a], costs 6 and 6.
The fixed flow itself has an unconstrained route decomposition, costs 8 and 4.
But every budget-feasible supported route can serve at most one satellite:
effective size=3, remaining capacity=5. Covering three satellites needs >=3 routes.

The exclusion invokes SharedReturnLargeServiceCuts, not route enumeration.
Only closed finite certificates use `decide +kernel`.
Strictness is relative to the explicitly listed PreviousConditions, not to
every possible capacity inequality, stronger travel overhead, or arbitrary
multi-hop structural condition.
-/

namespace UAVProof.SharedReturnSeparationExample

open ResourceCuts StructuralServiceCuts SharedReturnServiceCuts

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

abbrev Node := Fin 6

def tasks : Finset Node := {1, 2, 3, 4, 5}
def satellites : Finset Node := {2, 3, 4}
def service : Node → ℚ := ![0, 1, 2, 2, 2, 1]
def required : Node → ℕ := ![0, 5, 1, 1, 1, 1]
def degree : Node → ℕ := ![2, 5, 1, 1, 1, 1]
def capacity : ℚ := 6
def fleet : ℕ := 2

def fixedFlow : Node → Node → ℕ :=
  ![![0, 2, 0, 0, 0, 0],
    ![1, 0, 1, 1, 1, 1],
    ![0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0]]

def allowed (i j : Node) : Prop := fixedFlow i j ≠ 0
instance decidableAllowed (i j : Node) : Decidable (allowed i j) := by
  unfold allowed
  infer_instance
theorem shared_pattern : SharedReturnPattern allowed (0 : Node) 1 satellites where
  a_ne_depot := by decide
  depot_not_mem := by decide
  a_not_mem := by decide
  start := by decide +kernel
  after_mem := by decide +kernel

/-! Positive witnesses: both packing and actual routing are feasible. -/

def alternative1 : LegalRoute (0 : Node) where
  visits := [1, 2, 3, 1]
  visits_nonempty := by decide
  depot_not_mem := by decide
  adjacent_ne := by decide +kernel

def alternative2 : LegalRoute (0 : Node) where
  visits := [1, 5, 1, 4, 1]
  visits_nonempty := by decide
  depot_not_mem := by decide
  adjacent_ne := by decide +kernel

def alternativeRoutes (r : Fin 2) : LegalRoute (0 : Node) :=
  if r = 0 then alternative1 else alternative2

theorem alternative_cover :
    ∀ i : Node, totalVisitCount Finset.univ alternativeRoutes i = required i := by
  decide +kernel

theorem alternative_budget :
    ∀ r : Fin 2, routeServiceIn (alternativeRoutes r) tasks service ≤ capacity := by
  decide +kernel

def PackingFeasible : Prop :=
  ∃ count : Fin 2 → Node → ℕ,
    (∀ i, (∑ r, count r i) = required i) ∧
    (∀ r, (∑ i ∈ tasks, service i * (count r i : ℚ)) ≤ capacity)

theorem packing_feasible : PackingFeasible := by
  exact ⟨fun r i => (alternativeRoutes r).visits.count i,
    alternative_cover, alternative_budget⟩

/-- The fixed flow also decomposes into legal routes if budgets are omitted. -/
def unbudgeted1 : LegalRoute (0 : Node) where
  visits := [1, 2, 1, 3, 1, 5]
  visits_nonempty := by decide
  depot_not_mem := by decide
  adjacent_ne := by decide +kernel

def unbudgeted2 : LegalRoute (0 : Node) where
  visits := [1, 4, 1]
  visits_nonempty := by decide
  depot_not_mem := by decide
  adjacent_ne := by decide +kernel

def unbudgetedRoutes (r : Fin 2) : LegalRoute (0 : Node) :=
  if r = 0 then unbudgeted1 else unbudgeted2

theorem unbudgeted_exact_flow : totalRouteFlow Finset.univ unbudgetedRoutes = fixedFlow := by
  have h : ∀ i j : Node,
      totalRouteFlow Finset.univ unbudgetedRoutes i j = fixedFlow i j := by
    decide +kernel
  funext i j
  exact h i j

/-! Exhaustive coverage of the OLD immediate-return volume constraints. -/

/-- Every applicable shared-return pattern in this support uses a=1 and S subset B.
This prevents the separation claim from checking only one convenient pattern. -/
theorem classify_shared_pattern (a : Node) (S : Finset Node)
    (P : SharedReturnPattern allowed (0 : Node) a S) :
    a = 1 ∧ S ⊆ satellites := by
  have ha : (1 : Node) = a := P.start 1 (by decide +kernel)
  subst a
  refine ⟨rfl, ?_⟩
  have hcheck : ∀ b : Node, b ≠ 0 → (∀ j, allowed b j → j = 1) →
      b ∈ satellites := by decide +kernel
  intro b hb
  exact hcheck b (fun h => P.depot_not_mem (h ▸ hb)) (P.after_mem b hb)

theorem all_satellite_volume_bounds :
    ∀ S : Finset Node, S ⊆ satellites →
      Int.ceil (requiredServiceIn S (chargedService service 1) required /
        (capacity - service 1)) ≤ (fleet : ℤ) ∧
      Int.ceil (requiredServiceIn S (chargedService service 1) required /
        (capacity - service 1)) ≤ (outCutFlow S fixedFlow : ℤ) := by
  decide +kernel

theorem all_applicable_shared_volume_bounds (a : Node) (S : Finset Node)
    (P : SharedReturnPattern allowed (0 : Node) a S) :
    0 < capacity - service a ∧
      Int.ceil (requiredServiceIn S (chargedService service a) required /
        (capacity - service a)) ≤ (fleet : ℤ) ∧
      Int.ceil (requiredServiceIn S (chargedService service a) required /
        (capacity - service a)) ≤ (outCutFlow S fixedFlow : ℤ) := by
  obtain ⟨ha, hS⟩ := classify_shared_pattern a S P
  subst a
  exact ⟨by decide +kernel, all_satellite_volume_bounds S hS⟩

theorem all_applicable_singleton_volume_bounds (a b : Node)
    (P : ForcedReturnPattern allowed (0 : Node) a b) :
    0 < capacity - service a ∧
      Int.ceil (((service a + service b) * (required b : ℚ)) /
        (capacity - service a)) ≤ (fleet : ℤ) ∧
      Int.ceil (((service a + service b) * (required b : ℚ)) /
        (capacity - service a)) ≤ (outCutFlow {b} fixedFlow : ℤ) := by
  simpa [requiredServiceIn, chargedService] using
    all_applicable_shared_volume_bounds a {b}
      ((singleton_pattern_iff allowed).mpr P)

/-- Precisely the old aggregate and structural-volume conditions being separated. -/
structure PreviousConditions : Prop where
  outgoing : ∀ i, outFlow Finset.univ fixedFlow i = degree i
  incoming : ∀ i, inFlow Finset.univ fixedFlow i = degree i
  noDiagonal : ∀ i, fixedFlow i i = 0
  arcBounds : ∀ i j, fixedFlow i j ≤ min (degree i) (degree j)
  connected : ∀ S : Finset Node, S.Nonempty → (0 : Node) ∉ S →
    1 ≤ outCutFlow S fixedFlow
  totalBudget : requiredServiceIn tasks service required ≤ (fleet : ℚ) * capacity
  roundedCuts : ∀ S : Finset Node, (0 : Node) ∉ S →
    Int.ceil (requiredServiceIn S service required / capacity) ≤
      (outCutFlow S fixedFlow : ℤ)
  sharedVolumes : ∀ (a : Node) (S : Finset Node),
    SharedReturnPattern allowed (0 : Node) a S →
      0 < capacity - service a ∧
      Int.ceil (requiredServiceIn S (chargedService service a) required /
        (capacity - service a)) ≤ (fleet : ℤ) ∧
      Int.ceil (requiredServiceIn S (chargedService service a) required /
        (capacity - service a)) ≤ (outCutFlow S fixedFlow : ℤ)

theorem previous_conditions_hold : PreviousConditions where
  outgoing := by decide +kernel
  incoming := by decide +kernel
  noDiagonal := by decide +kernel
  arcBounds := by decide +kernel
  connected := by decide +kernel
  totalBudget := by decide +kernel
  roundedCuts := by decide +kernel
  sharedVolumes := all_applicable_shared_volume_bounds

/-! The NEW condition fails, although all of the preceding ones hold. -/

theorem all_satellites_effectively_large : ∀ b ∈ satellites,
    (capacity - service 1) / ((1 : ℚ) + 1) < chargedService service 1 b := by
  decide +kernel

theorem satellite_demand_eq_three : (∑ b ∈ satellites, required b) = 3 := by
  decide +kernel

theorem effective_large_count_violated : ¬ (∑ b ∈ satellites, required b) ≤ 1 * fleet := by
  decide +kernel

section Fleets

variable {ι : Type*}

/-- Generic counting proves infeasibility for any selected family of at most two routes. -/
theorem no_dominated_cover
    (ks : Finset ι) (routes : ι → LegalRoute (0 : Node))
    (hcard : ks.card ≤ fleet)
    (hdom : ∀ i j, totalRouteFlow ks routes i j ≤ fixedFlow i j)
    (hcover : ∀ b ∈ satellites, totalVisitCount ks routes b = required b)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ capacity) :
    False := by
  have hs : ∀ r ∈ ks, SupportsRoute allowed (routes r) := by
    intro r hr
    exact supported_of_total_domination ks routes fixedFlow hdom hr
  have h := SharedReturnLargeServiceCuts.required_effective_large_count_bounds
    allowed satellites shared_pattern ks routes tasks satellites service required capacity 1
    (by decide) (by decide +kernel) (by intro i hi; exact hi)
    (by decide +kernel) (by decide +kernel) hs
    all_satellites_effectively_large hcover hbudget
  have hc : (∑ b ∈ satellites, required b) ≤ 1 * fleet :=
    h.2.1.trans (Nat.mul_le_mul_left 1 hcard)
  exact effective_large_count_violated hc

/-- Exact flow recovery derives both fleet size and satellite coverage from degrees. -/
theorem no_exact_decomposition
    (ks : Finset ι) (routes : ι → LegalRoute (0 : Node))
    (hflow : totalRouteFlow ks routes = fixedFlow)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ capacity) :
    False := by
  have hcard : ks.card = fleet := by
    calc
      ks.card = outFlow Finset.univ (totalRouteFlow ks routes) (0 : Node) :=
        (total_outFlow_depot_eq_card ks routes).symm
      _ = outFlow Finset.univ fixedFlow (0 : Node) := by rw [hflow]
      _ = fleet := by decide +kernel
  have hdegrees : ∀ b ∈ satellites,
      outFlow Finset.univ fixedFlow b = required b := by decide +kernel
  have hcover : ∀ b ∈ satellites, totalVisitCount ks routes b = required b := by
    intro b hb
    have hb0 : b ≠ (0 : Node) := fun h => shared_pattern.depot_not_mem (h ▸ hb)
    calc
      totalVisitCount ks routes b =
          outFlow Finset.univ (totalRouteFlow ks routes) b :=
        (total_outFlow_eq_visit_count ks routes b hb0).symm
      _ = outFlow Finset.univ fixedFlow b := by rw [hflow]
      _ = required b := hdegrees b hb
  exact no_dominated_cover ks routes hcard.le
    (fun i j => (congrFun (congrFun hflow i) j).le) hcover hbudget

end Fleets

/-- A single witness passes the listed old conditions, has feasible alternative
routes and an unconstrained exact decomposition, but is excluded by the new count. -/
theorem strict_separation :
    PackingFeasible ∧
    (∃ routes : Fin 2 → LegalRoute (0 : Node),
      (∀ i, totalVisitCount Finset.univ routes i = required i) ∧
      (∀ r, routeServiceIn (routes r) tasks service ≤ capacity)) ∧
    PreviousConditions ∧
    SharedReturnPattern allowed (0 : Node) 1 satellites ∧
    (∃ routes : Fin 2 → LegalRoute (0 : Node),
      totalRouteFlow Finset.univ routes = fixedFlow) ∧
    (¬ (∑ b ∈ satellites, required b) ≤ 1 * fleet) ∧
    ¬ ∃ routes : Fin 2 → LegalRoute (0 : Node),
      totalRouteFlow Finset.univ routes = fixedFlow ∧
      (∀ r, routeServiceIn (routes r) tasks service ≤ capacity) := by
  refine ⟨packing_feasible, ⟨alternativeRoutes, alternative_cover, alternative_budget⟩,
    previous_conditions_hold, shared_pattern, ⟨unbudgetedRoutes, unbudgeted_exact_flow⟩,
    effective_large_count_violated, ?_⟩
  rintro ⟨routes, hflow, hbudget⟩
  exact no_exact_decomposition Finset.univ routes hflow (fun r _ => hbudget r)

#print axioms shared_pattern
#print axioms packing_feasible
#print axioms alternative_cover
#print axioms alternative_budget
#print axioms unbudgeted_exact_flow
#print axioms classify_shared_pattern
#print axioms all_applicable_shared_volume_bounds
#print axioms all_applicable_singleton_volume_bounds
#print axioms previous_conditions_hold
#print axioms effective_large_count_violated
#print axioms no_dominated_cover
#print axioms no_exact_decomposition
#print axioms strict_separation

end UAVProof.SharedReturnSeparationExample
