import LeanCompletion.UAV.SupportExactFeasibility

/-!
# Support-feasible routes need not recover prescribed edge multiplicities

New proof candidate: local Lean compilation and axiom reports are pending.
Depends on the stage-1 SupportExactFeasibility module.

Depot 0; task vertices 1, 2, 3; each task requires two visits, each costing 1.
Two nonempty legal routes, each with service budget 3. No travel costs.

Prescribed flow rows:
  [0,1,0,1], [0,0,1,1], [1,1,0,0], [1,0,1,0].
Support feasibility: use 0-1-3-2-0 twice.
Ignoring budgets, exact decomposition: 0-1-2-0 and 0-3-2-1-3-0.

For any feasible two-route family, exact coverage and the budgets force
each visit list to have length 3. No supported, depot-free three-visit route
uses 0->3. But exact recovery requires that edge once: contradiction.

Finite kernel certificates check numerical data, all physical cuts, and the
64 triples of vertices. The negative theorem quantifies over arbitrary legal
route families, reducing to triples by proved length and coverage lemmas.
The Python search and independent enumeration are not proof assumptions.

Support containment is intended: the positive family need not use every
edge of x, and it may traverse a supported edge more often than x does.
-/

namespace UAVProof.SameSupportSeparation

open ResourceCuts SupportExactFeasibility

abbrev Node := Fin 4

def required : Node → ℕ := ![0, 2, 2, 2]
def service : Node → ℚ := ![0, 1, 1, 1]
def capacity : ℚ := 3

def fixedFlow : Node → Node → ℕ :=
  ![![0, 1, 0, 1], ![0, 0, 1, 1], ![1, 1, 0, 0], ![1, 0, 1, 0]]

theorem service_nonneg : ∀ v : Node, 0 ≤ service v := by
  decide +kernel

theorem capacity_pos : 0 < capacity := by
  decide +kernel

/-! Positive support witness, with the same demand, route count and budget. -/

def route132 : LegalRoute (0 : Node) where
  visits := [1, 3, 2]
  visits_nonempty := by decide
  depot_not_mem := by decide
  adjacent_ne := by decide +kernel

def supportRoutes (_ : Fin 2) : LegalRoute (0 : Node) := route132

theorem support_routes_cover :
    ∀ v : Node, v ≠ 0 →
      totalVisitCount Finset.univ supportRoutes v = required v := by
  decide +kernel

theorem support_routes_budget :
    ∀ r : Fin 2,
      routeServiceIn (supportRoutes r) Finset.univ service ≤ capacity := by
  decide +kernel

theorem support_routes_supported :
    ∀ r : Fin 2, RouteUsesSupport fixedFlow (supportRoutes r) := by
  unfold RouteUsesSupport SupportedBy
  decide +kernel

theorem support_feasible :
    SupportFeasible (0 : Node) fixedFlow required 2 service capacity := by
  exact ⟨supportRoutes, support_routes_cover, support_routes_budget,
    support_routes_supported⟩

/-! The prescribed flow itself is legally decomposable when budgets are omitted. -/

def route12 : LegalRoute (0 : Node) where
  visits := [1, 2]
  visits_nonempty := by decide
  depot_not_mem := by decide
  adjacent_ne := by decide +kernel

def route3213 : LegalRoute (0 : Node) where
  visits := [3, 2, 1, 3]
  visits_nonempty := by decide
  depot_not_mem := by decide
  adjacent_ne := by decide +kernel

def unbudgetedRoutes (r : Fin 2) : LegalRoute (0 : Node) :=
  if r = 0 then route12 else route3213

theorem unbudgeted_routes_cover :
    ∀ v : Node, v ≠ 0 →
      totalVisitCount Finset.univ unbudgetedRoutes v = required v := by
  decide +kernel

theorem unbudgeted_routes_exact :
    ∀ u v : Node,
      totalRouteFlow Finset.univ unbudgetedRoutes u v = fixedFlow u v := by
  decide +kernel

theorem unbudgeted_route_costs :
    routeServiceIn (unbudgetedRoutes 0) Finset.univ service = 2 ∧
    routeServiceIn (unbudgetedRoutes 1) Finset.univ service = 4 := by
  decide +kernel

def ExactWithoutBudget : Prop :=
  ∃ routes : Fin 2 → LegalRoute (0 : Node),
    (∀ v, v ≠ (0 : Node) →
      totalVisitCount Finset.univ routes v = required v) ∧
    (∀ u v, totalRouteFlow Finset.univ routes u v = fixedFlow u v)

theorem exact_without_budget : ExactWithoutBudget := by
  exact ⟨unbudgetedRoutes, unbudgeted_routes_cover, unbudgeted_routes_exact⟩

/-! Necessary aggregate conditions, including every physical capacity cut. -/

structure AggregateConditions (x : Node → Node → ℕ) : Prop where
  degrees : HasDegrees (0 : Node) required 2 x
  noDiagonal : ∀ v, x v v = 0
  arcBounds : ∀ u v,
    x u v ≤ min (prescribedDegree (0 : Node) required 2 u)
      (prescribedDegree (0 : Node) required 2 v)
  positiveCuts : ∀ S : Finset Node, S.Nonempty → (0 : Node) ∉ S →
    1 ≤ outCutFlow S x
  totalBudget : requiredServiceIn Finset.univ service required ≤ 2 * capacity
  roundedCuts : ∀ S : Finset Node, (0 : Node) ∉ S →
    Int.ceil (requiredServiceIn S service required / capacity) ≤
      (outCutFlow S x : ℤ)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem fixed_flow_aggregate_conditions : AggregateConditions fixedFlow := by
  constructor
  · unfold HasDegrees prescribedDegree
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-! General list and budget reasoning: no bound on a route is assumed. -/

theorem task_counts_eq_length
    (l : List Node) (hzero : (0 : Node) ∉ l) :
    l.count 1 + l.count 2 + l.count 3 = l.length := by
  revert hzero
  induction l with
  | nil =>
    intro _
    simp
  | cons a l ih =>
    intro hzero
    have ha : a ≠ (0 : Node) := by
      intro h
      apply hzero
      simp [h]
    have hl : (0 : Node) ∉ l := by
      intro h
      apply hzero
      exact List.mem_cons_of_mem a h
    have htail := ih hl
    fin_cases a <;> simp_all [List.count_cons] <;> omega

theorem route_service_eq_length (r : LegalRoute (0 : Node)) :
    routeServiceIn r Finset.univ service = (r.visits.length : ℚ) := by
  have hcount := task_counts_eq_length r.visits r.depot_not_mem
  have hcast :
      ((r.visits.count 1 + r.visits.count 2 + r.visits.count 3 : ℕ) : ℚ) =
        (r.visits.length : ℚ) := by
    exact_mod_cast hcount
  simpa [routeServiceIn, service, Fin.sum_univ_succ, Nat.cast_add, add_assoc] using hcast

theorem total_length_eq_six
    (routes : Fin 2 → LegalRoute (0 : Node))
    (hcover : ∀ v, v ≠ (0 : Node) →
      totalVisitCount Finset.univ routes v = required v) :
    (routes 0).visits.length + (routes 1).visits.length = 6 := by
  have h1 : (routes 0).visits.count 1 + (routes 1).visits.count 1 = 2 := by
    simpa [totalVisitCount, Fin.sum_univ_succ, required] using hcover 1 (by decide)
  have h2 : (routes 0).visits.count 2 + (routes 1).visits.count 2 = 2 := by
    simpa [totalVisitCount, Fin.sum_univ_succ, required] using hcover 2 (by decide)
  have h3 : (routes 0).visits.count 3 + (routes 1).visits.count 3 = 2 := by
    simpa [totalVisitCount, Fin.sum_univ_succ, required] using hcover 3 (by decide)
  have hl0 := task_counts_eq_length (routes 0).visits (routes 0).depot_not_mem
  have hl1 := task_counts_eq_length (routes 1).visits (routes 1).depot_not_mem
  omega

theorem every_route_length_three
    (routes : Fin 2 → LegalRoute (0 : Node))
    (hcover : ∀ v, v ≠ (0 : Node) →
      totalVisitCount Finset.univ routes v = required v)
    (hbudget : ∀ r, routeServiceIn (routes r) Finset.univ service ≤ capacity) :
    ∀ r, (routes r).visits.length = 3 := by
  have htotal := total_length_eq_six routes hcover
  have htotalQ :
      ((routes 0).visits.length : ℚ) +
        ((routes 1).visits.length : ℚ) = 6 := by
    exact_mod_cast htotal
  have h0Q : ((routes 0).visits.length : ℚ) ≤ 3 := by
    simpa only [route_service_eq_length, capacity] using hbudget 0
  have h1Q : ((routes 1).visits.length : ℚ) ≤ 3 := by
    simpa only [route_service_eq_length, capacity] using hbudget 1
  have heq0Q : ((routes 0).visits.length : ℚ) = 3 := by
    linarith only [htotalQ, h0Q, h1Q]
  have heq1Q : ((routes 1).visits.length : ℚ) = 3 := by
    linarith only [htotalQ, h0Q, h1Q]
  have heq0 : (routes 0).visits.length = 3 := by
    exact_mod_cast heq0Q
  have heq1 : (routes 1).visits.length = 3 := by
    exact_mod_cast heq1Q
  intro r
  fin_cases r
  · simpa using heq0
  · simpa using heq1

/-! A small finite structural certificate, independent of possible route families. -/

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem supported_triple_no_departure_to_three :
    ∀ a b c : Node, a ≠ 0 → b ≠ 0 → c ≠ 0 →
      (∀ u v : Node, fixedFlow u v = 0 →
        routeFlow (depotRoute (0 : Node) [a, b, c]) u v = 0) →
      routeFlow (depotRoute (0 : Node) [a, b, c]) 0 3 = 0 := by
  decide +kernel

/-- Any legal route with length 3 reduces to the preceding finite certificate. -/
theorem length_three_no_departure_to_three
    (r : LegalRoute (0 : Node)) (hlen : r.visits.length = 3)
    (hsupport : RouteUsesSupport fixedFlow r) :
    routeFlow r.vertices 0 3 = 0 := by
  obtain ⟨a, b, c, hvisits⟩ :
      ∃ a b c : Node, r.visits = [a, b, c] := by
    cases hlist : r.visits with
    | nil => simp [hlist] at hlen
    | cons a tail =>
      cases tail with
      | nil => simp [hlist] at hlen
      | cons b tail =>
        cases tail with
        | nil => simp [hlist] at hlen
        | cons c tail =>
          have htail : tail.length = 0 := by
            simp only [hlist, List.length_cons] at hlen
            omega
          have hnil : tail = [] := by
            cases tail with
            | nil => rfl
            | cons d rest => simp at htail
          subst tail
          exact ⟨a, b, c, rfl⟩
  have hnonzero : a ≠ (0 : Node) ∧ b ≠ (0 : Node) ∧ c ≠ (0 : Node) := by
    simpa [hvisits, eq_comm] using r.depot_not_mem
  change SupportedBy (routeFlow (depotRoute (0 : Node) r.visits)) fixedFlow
    at hsupport
  rw [hvisits] at hsupport
  change routeFlow (depotRoute (0 : Node) r.visits) 0 3 = 0
  rw [hvisits]
  exact supported_triple_no_departure_to_three a b c
    hnonzero.1 hnonzero.2.1 hnonzero.2.2 hsupport

/-- Universal exclusion: every exact two-route family is ruled out. -/
theorem not_exact_feasible :
    ¬ ExactFeasible (0 : Node) fixedFlow required 2 service capacity := by
  rintro ⟨routes, hcover, hbudget, hexact⟩
  have hlength := every_route_length_three routes hcover hbudget
  have hzero : totalRouteFlow Finset.univ routes (0 : Node) (3 : Node) = 0 := by
    unfold totalRouteFlow
    apply Finset.sum_eq_zero
    intro r _
    exact length_three_no_departure_to_three (routes r) (hlength r)
      (route_supported_of_exact fixedFlow routes hexact r)
  have hone : totalRouteFlow Finset.univ routes (0 : Node) (3 : Node) = 1 := by
    simpa [fixedFlow] using hexact 0 3
  omega

theorem strict_separation :
    SupportFeasible (0 : Node) fixedFlow required 2 service capacity ∧
    ¬ ExactFeasible (0 : Node) fixedFlow required 2 service capacity := by
  exact ⟨support_feasible, not_exact_feasible⟩

/-- Full certificate: the negative result is not caused by failure of these
aggregate conditions, or by the absence of any legal exact decomposition. -/
theorem strict_separation_with_aggregate_conditions :
    AggregateConditions fixedFlow ∧ ExactWithoutBudget ∧
    SupportFeasible (0 : Node) fixedFlow required 2 service capacity ∧
    ¬ ExactFeasible (0 : Node) fixedFlow required 2 service capacity := by
  exact ⟨fixed_flow_aggregate_conditions, exact_without_budget,
    support_feasible, not_exact_feasible⟩

theorem support_does_not_determine_flow :
    ¬ SupportDeterminesFlow (0 : Node) required 2 fixedFlow := by
  intro hunique
  exact not_exact_feasible
    (support_implies_exact_of_unique (0 : Node) fixedFlow required 2
      service capacity hunique support_feasible)

end UAVProof.SameSupportSeparation

#print axioms UAVProof.SameSupportSeparation.service_nonneg
#print axioms UAVProof.SameSupportSeparation.capacity_pos
#print axioms UAVProof.SameSupportSeparation.support_routes_cover
#print axioms UAVProof.SameSupportSeparation.support_routes_budget
#print axioms UAVProof.SameSupportSeparation.support_routes_supported
#print axioms UAVProof.SameSupportSeparation.support_feasible
#print axioms UAVProof.SameSupportSeparation.unbudgeted_routes_cover
#print axioms UAVProof.SameSupportSeparation.unbudgeted_routes_exact
#print axioms UAVProof.SameSupportSeparation.unbudgeted_route_costs
#print axioms UAVProof.SameSupportSeparation.exact_without_budget
#print axioms UAVProof.SameSupportSeparation.fixed_flow_aggregate_conditions
#print axioms UAVProof.SameSupportSeparation.task_counts_eq_length
#print axioms UAVProof.SameSupportSeparation.route_service_eq_length
#print axioms UAVProof.SameSupportSeparation.total_length_eq_six
#print axioms UAVProof.SameSupportSeparation.every_route_length_three
#print axioms UAVProof.SameSupportSeparation.supported_triple_no_departure_to_three
#print axioms UAVProof.SameSupportSeparation.length_three_no_departure_to_three
#print axioms UAVProof.SameSupportSeparation.not_exact_feasible
#print axioms UAVProof.SameSupportSeparation.strict_separation
#print axioms UAVProof.SameSupportSeparation.strict_separation_with_aggregate_conditions
#print axioms UAVProof.SameSupportSeparation.support_does_not_determine_flow
