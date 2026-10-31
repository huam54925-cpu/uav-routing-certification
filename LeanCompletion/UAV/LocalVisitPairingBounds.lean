import LeanCompletion.UAV.LocalVisitPairingCompleteness

/-!
# Numerical bounds for the canonical route certificates

The total demand counts non-depot visits with multiplicity. Exact coverage
identifies this number with the number of route positions, not the number of
distinct physical vertices. The depot's demand is unrestricted and ignored.

The bounds apply to the existing routeRank and routePotential constructions,
not to arbitrary certificates. Empty route families and zero task demand are
allowed. A bound on all potential values explicitly requires a nonnegative
budget, since an empty family's route budgets give no information about T.

These are numerical range bounds only, with no rational encoding-size bound,
search algorithm, or bounded next-certificate predicate.
-/

namespace UAVProof.LocalVisitPairingBounds

open scoped BigOperators
open ResourceCuts VisitCopyLift LocalVisitPairing LocalVisitPairingCompleteness

section TotalVisits

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Total required task occurrences; the depot demand is not counted. -/
def totalVisits (depot : V) (required : V → ℕ) : ℕ :=
  ∑ v ∈ Finset.univ.erase depot, required v

theorem totalVisits_eq_zero_of_task_zero (depot : V) (required : V → ℕ)
    (hzero : ∀ v, v ≠ depot → required v = 0) : totalVisits depot required = 0 := by
  apply Finset.sum_eq_zero
  intro v hv
  exact hzero v (Finset.mem_erase.mp hv).1

variable {ι : Type*} [Fintype ι]
variable (depot : V) (required : V → ℕ) (routes : ι → LegalRoute depot)
variable (hcover : ∀ v, v ≠ depot → totalVisitCount Finset.univ routes v = required v)

include hcover

/-- The occurrence bijection counts repeated visits separately and works for
empty index types. No condition on required depot is used. -/
theorem sum_route_lengths_eq_totalVisits :
    (∑ r, (routes r).visits.length) = totalVisits depot required := by
  calc
    (∑ r, (routes r).visits.length) = ∑ v : {v : V // v ≠ depot}, required v.val := by
      simpa only [VisitPosition, Fintype.card_sigma, Fintype.card_fin] using
        Fintype.card_congr (visitPositionCopiesEquiv depot required routes hcover)
    _ = totalVisits depot required :=
      (Finset.sum_subtype (Finset.univ.erase depot) (by simp) required).symm

theorem route_length_le_totalVisits (r : ι) :
    (routes r).visits.length ≤ totalVisits depot required := by
  rw [← sum_route_lengths_eq_totalVisits depot required routes hcover]
  exact Finset.single_le_sum (fun s _ => Nat.zero_le (routes s).visits.length)
    (Finset.mem_univ r)

/-- In an empty route family exact task coverage forces zero total task demand. -/
theorem totalVisits_eq_zero_of_empty [IsEmpty ι] : totalVisits depot required = 0 := by
  rw [← sum_route_lengths_eq_totalVisits depot required routes hcover]
  simp

end TotalVisits

section SuffixService

variable {V : Type*}

/-- Nonnegative fees give a nonnegative sum on any list, with repetitions. -/
theorem service_sum_nonneg (service : V → ℚ) (hservice : ∀ v, 0 ≤ service v)
    (visits : List V) : 0 ≤ (visits.map service).sum := by
  apply List.sum_nonneg
  intro q hq
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq
  exact hservice v

theorem suffix_service_nonneg (service : V → ℚ) (hservice : ∀ v, 0 ≤ service v)
    (visits : List V) (i : ℕ) : 0 ≤ ((visits.drop i).map service).sum :=
  service_sum_nonneg service hservice (visits.drop i)

/-- Removing a nonnegative prefix cannot increase the service sum.
There is no distinctness condition on the visited vertices. -/
theorem suffix_service_le_total (service : V → ℚ) (hservice : ∀ v, 0 ≤ service v)
    (visits : List V) (i : ℕ) :
    ((visits.drop i).map service).sum ≤ (visits.map service).sum := by
  have hprefix := service_sum_nonneg service hservice (visits.take i)
  have hsplit : ((visits.take i).map service).sum + ((visits.drop i).map service).sum =
      (visits.map service).sum := by
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  linarith only [hprefix, hsplit]

end SuffixService

section RouteBounds

variable {V : Type*} [DecidableEq V]
variable {ι : Type*} [Fintype ι]
variable (depot : V) (required : V → ℕ) (routes : ι → LegalRoute depot)
variable (hcover : ∀ v, v ≠ depot → totalVisitCount Finset.univ routes v = required v)

/-- The canonical depot rank is already normalized to zero. -/
theorem routeRank_depot_zero : routeRank depot required routes hcover none = 0 :=
  routeRank_none depot required routes hcover

/-- At a task position the remaining route length lies between one and N. -/
theorem routeRank_task_bounds [Fintype V] (c : VisitCopy depot required) (hc : c ≠ none) :
    1 ≤ routeRank depot required routes hcover c ∧
      routeRank depot required routes hcover c ≤ totalVisits depot required := by
  obtain ⟨p, rfl, _⟩ := existsUnique_positionCopy depot required routes hcover c hc
  rw [routeRank_position]
  have hpos := p.2.isLt
  have hlen := route_length_le_totalVisits depot required routes hcover p.1
  omega

theorem routePotential_depot_zero (service : V → ℚ) :
    routePotential depot required routes hcover service none = 0 :=
  routePotential_none depot required routes hcover service

/-- Nonnegativity also holds at the depot, independently of any route budget. -/
theorem routePotential_nonneg (service : V → ℚ) (hservice : ∀ v, 0 ≤ service v)
    (c : VisitCopy depot required) :
    0 ≤ routePotential depot required routes hcover service c := by
  by_cases hc : c = none
  · subst c
    rw [routePotential_none]
  · obtain ⟨p, rfl, _⟩ := existsUnique_positionCopy depot required routes hcover c hc
    rw [routePotential_position]
    exact suffix_service_nonneg service hservice (routes p.1).visits p.2.val

/-- At a task the potential is bounded by the full service of its own route. -/
theorem routePotential_position_le_service [Fintype V]
    (service : V → ℚ) (hservice : ∀ v, 0 ≤ service v) (p : VisitPosition routes) :
    routePotential depot required routes hcover service
        (positionCopy depot required routes hcover p) ≤
      routeServiceIn (routes p.1) Finset.univ service := by
  rw [routePotential_position, route_service_eq_list_sum]
  exact suffix_service_le_total service hservice (routes p.1).visits p.2.val

/-- Task bounds need only the actual route budgets, not a sign hypothesis on T. -/
theorem routePotential_task_bounds [Fintype V]
    (service : V → ℚ) (hservice : ∀ v, 0 ≤ service v) (T : ℚ)
    (hbudget : ∀ r, routeServiceIn (routes r) Finset.univ service ≤ T)
    (c : VisitCopy depot required) (hc : c ≠ none) :
    0 ≤ routePotential depot required routes hcover service c ∧
      routePotential depot required routes hcover service c ≤ T := by
  refine ⟨routePotential_nonneg depot required routes hcover service hservice c, ?_⟩
  obtain ⟨p, rfl, _⟩ := existsUnique_positionCopy depot required routes hcover c hc
  exact (routePotential_position_le_service depot required routes hcover
    service hservice p).trans (hbudget p.1)

/-- Including the depot in the upper bound requires an explicit 0 ≤ T.
This is essential when the indexed route family is empty. -/
theorem routePotential_bounds [Fintype V]
    (service : V → ℚ) (hservice : ∀ v, 0 ≤ service v) (T : ℚ) (hT : 0 ≤ T)
    (hbudget : ∀ r, routeServiceIn (routes r) Finset.univ service ≤ T)
    (c : VisitCopy depot required) :
    0 ≤ routePotential depot required routes hcover service c ∧
      routePotential depot required routes hcover service c ≤ T := by
  by_cases hc : c = none
  · subst c
    rw [routePotential_none]
    exact ⟨le_rfl, hT⟩
  · exact routePotential_task_bounds depot required routes hcover service hservice T hbudget c hc

end RouteBounds

end UAVProof.LocalVisitPairingBounds

#check UAVProof.LocalVisitPairingBounds.totalVisits
#check UAVProof.LocalVisitPairingBounds.sum_route_lengths_eq_totalVisits
#check UAVProof.LocalVisitPairingBounds.route_length_le_totalVisits
#check UAVProof.LocalVisitPairingBounds.totalVisits_eq_zero_of_task_zero
#check UAVProof.LocalVisitPairingBounds.totalVisits_eq_zero_of_empty
#check UAVProof.LocalVisitPairingBounds.routeRank_depot_zero
#check UAVProof.LocalVisitPairingBounds.routeRank_task_bounds
#check UAVProof.LocalVisitPairingBounds.suffix_service_nonneg
#check UAVProof.LocalVisitPairingBounds.suffix_service_le_total
#check UAVProof.LocalVisitPairingBounds.routePotential_depot_zero
#check UAVProof.LocalVisitPairingBounds.routePotential_nonneg
#check UAVProof.LocalVisitPairingBounds.routePotential_position_le_service
#check UAVProof.LocalVisitPairingBounds.routePotential_task_bounds
#check UAVProof.LocalVisitPairingBounds.routePotential_bounds

#print axioms UAVProof.LocalVisitPairingBounds.sum_route_lengths_eq_totalVisits
#print axioms UAVProof.LocalVisitPairingBounds.route_length_le_totalVisits
#print axioms UAVProof.LocalVisitPairingBounds.totalVisits_eq_zero_of_task_zero
#print axioms UAVProof.LocalVisitPairingBounds.totalVisits_eq_zero_of_empty
#print axioms UAVProof.LocalVisitPairingBounds.routeRank_depot_zero
#print axioms UAVProof.LocalVisitPairingBounds.routeRank_task_bounds
#print axioms UAVProof.LocalVisitPairingBounds.service_sum_nonneg
#print axioms UAVProof.LocalVisitPairingBounds.suffix_service_nonneg
#print axioms UAVProof.LocalVisitPairingBounds.suffix_service_le_total
#print axioms UAVProof.LocalVisitPairingBounds.routePotential_depot_zero
#print axioms UAVProof.LocalVisitPairingBounds.routePotential_nonneg
#print axioms UAVProof.LocalVisitPairingBounds.routePotential_position_le_service
#print axioms UAVProof.LocalVisitPairingBounds.routePotential_task_bounds
#print axioms UAVProof.LocalVisitPairingBounds.routePotential_bounds
