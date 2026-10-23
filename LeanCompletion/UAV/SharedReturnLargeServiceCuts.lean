import LeanCompletion.UAV.SharedReturnServiceCuts
import LeanCompletion.UAV.LargeServiceCuts

/-!
# Large effective services under a shared-return support pattern

Verification: local Lake build passed on 2026-10-23 with Lean 4.30.0-rc2.
The six printed axiom reports contain no sorryAx. Imports reused local caches.
See docs/SHARED_RETURN_SERVICE_CUTS.md for commands and verification limitations.

For b in B, effective service is s(a)+s(b), and remaining capacity is T-s(a).
The shared-return theorem derives this accounting from the original service
budget. The graph-independent large-service theorem then bounds occurrences.

If H is a subset of B and every effective service in H exceeds
(T-s(a))/(k+1), each feasible supported route visits H at most k times.
Exact coverage gives sum_{b in H} d(b) <= k*q(H), hence <= k*m and <= k*cut(H).
The threshold is strict; no claim is made at equality.

These remain conditional necessary inequalities. This module does not prove
a strict-separation graph witness or sufficiency of the strengthened system.
-/

namespace UAVProof.SharedReturnLargeServiceCuts

open ResourceCuts StructuralServiceCuts SharedReturnServiceCuts

variable {V ι : Type*} [DecidableEq V] [Fintype V]
variable {depot a : V}

/-- Derive the effective budget on any subset H of the shared-return set. -/
theorem effective_subset_budget
    (E : V → V → Prop) (B : Finset V) (P : SharedReturnPattern E depot a B)
    (r : LegalRoute depot) (hsupport : SupportsRoute E r)
    (tasks H : Finset V) (service : V → ℚ) (T : ℚ)
    (ha : a ∈ tasks) (hB : B ⊆ tasks) (hH : H ⊆ B)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hbudget : routeServiceIn r tasks service ≤ T) :
    routeServiceIn r H (chargedService service a) ≤ T - service a := by
  have hforced := SharedReturnServiceCuts.forced_service_lower_bound
    E B P r hsupport tasks service ha hB hservice
  have heffective : ∀ i ∈ B, 0 ≤ chargedService service a i := by
    intro i hi
    exact add_nonneg (hservice a ha) (hservice i (hB hi))
  have hmono := LargeServiceCuts.routeServiceIn_mono r H B
    (chargedService service a) hH heffective
  linarith only [hforced, hmono, hbudget]

/-- The counting step invokes the existing graph-independent theorem. -/
theorem route_count_le_of_effective_threshold
    (E : V → V → Prop) (B : Finset V) (P : SharedReturnPattern E depot a B)
    (r : LegalRoute depot) (hsupport : SupportsRoute E r)
    (tasks H : Finset V) (service : V → ℚ) (T : ℚ) (k : ℕ)
    (ha : a ∈ tasks) (hB : B ⊆ tasks) (hH : H ⊆ B)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hremaining : 0 ≤ T - service a)
    (hlarge : ∀ i ∈ H,
      (T - service a) / ((k : ℚ) + 1) < chargedService service a i)
    (hbudget : routeServiceIn r tasks service ≤ T) :
    (∑ i ∈ H, r.visits.count i) ≤ k := by
  exact LargeServiceCuts.count_le_of_threshold H (fun i => r.visits.count i)
    (chargedService service a) (T - service a) k hremaining hlarge
    (effective_subset_budget E B P r hsupport tasks H service T
      ha hB hH hservice hbudget)

omit [Fintype V] in
/-- A general counting bridge: only routes actually serving H contribute.
No graph support, cost, or capacity assumption is needed in this lemma. -/
theorem demand_count_le_serving_capacity
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (H : Finset V) (required : V → ℕ) (k : ℕ)
    (hcover : ∀ i ∈ H, totalVisitCount ks routes i = required i)
    (hper : ∀ r ∈ ks, (∑ i ∈ H, (routes r).visits.count i) ≤ k) :
    (∑ i ∈ H, required i) ≤ k * servingCount ks routes H := by
  classical
  have hroute : ∀ r ∈ ks, (∑ i ∈ H, (routes r).visits.count i) ≤
      if Serves (routes r) H then k else 0 := by
    intro r hr
    by_cases hs : Serves (routes r) H
    · simpa only [if_pos hs] using hper r hr
    · rw [if_neg hs]
      have hz : (∑ i ∈ H, (routes r).visits.count i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply List.count_eq_zero.mpr
        intro hvis
        exact hs ⟨i, hvis, hi⟩
      exact hz.le
  calc
    (∑ i ∈ H, required i) = ∑ i ∈ H, ∑ r ∈ ks, (routes r).visits.count i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hcover i hi).symm
    _ = ∑ r ∈ ks, ∑ i ∈ H, (routes r).visits.count i := Finset.sum_comm
    _ ≤ ∑ r ∈ ks, if Serves (routes r) H then k else 0 := Finset.sum_le_sum hroute
    _ = k * servingCount ks routes H := by
      rw [← Finset.sum_filter]
      simp [servingCount, Nat.mul_comm]

/-- Combine structural resource accounting with indivisible-service counting. -/
theorem required_effective_large_count_le
    (E : V → V → Prop) (B : Finset V) (P : SharedReturnPattern E depot a B)
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (tasks H : Finset V) (service : V → ℚ) (required : V → ℕ) (T : ℚ) (k : ℕ)
    (ha : a ∈ tasks) (hB : B ⊆ tasks) (hH : H ⊆ B)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hremaining : 0 ≤ T - service a)
    (hsupport : ∀ r ∈ ks, SupportsRoute E (routes r))
    (hlarge : ∀ i ∈ H,
      (T - service a) / ((k : ℚ) + 1) < chargedService service a i)
    (hcover : ∀ i ∈ H, totalVisitCount ks routes i = required i)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ T) :
    (∑ i ∈ H, required i) ≤ k * servingCount ks routes H := by
  apply demand_count_le_serving_capacity ks routes H required k hcover
  intro r hr
  exact route_count_le_of_effective_threshold E B P (routes r) (hsupport r hr)
    tasks H service T k ha hB hH hservice hremaining hlarge (hbudget r hr)

/-- Keep q(H), and also obtain fleet and edge-flow upper bounds. -/
theorem required_effective_large_count_bounds
    (E : V → V → Prop) (B : Finset V) (P : SharedReturnPattern E depot a B)
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (tasks H : Finset V) (service : V → ℚ) (required : V → ℕ) (T : ℚ) (k : ℕ)
    (ha : a ∈ tasks) (hB : B ⊆ tasks) (hH : H ⊆ B)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hremaining : 0 ≤ T - service a)
    (hsupport : ∀ r ∈ ks, SupportsRoute E (routes r))
    (hlarge : ∀ i ∈ H,
      (T - service a) / ((k : ℚ) + 1) < chargedService service a i)
    (hcover : ∀ i ∈ H, totalVisitCount ks routes i = required i)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ T) :
    (∑ i ∈ H, required i) ≤ k * servingCount ks routes H ∧
      (∑ i ∈ H, required i) ≤ k * ks.card ∧
      (∑ i ∈ H, required i) ≤ k * outCutFlow H (totalRouteFlow ks routes) := by
  have hc := required_effective_large_count_le E B P ks routes tasks H
    service required T k ha hB hH hservice hremaining hsupport hlarge hcover hbudget
  have hdepot : depot ∉ H := fun hi => P.depot_not_mem (hH hi)
  obtain ⟨hm, hx⟩ := servingCount_bounds ks routes H hdepot
  exact ⟨hc, hc.trans (Nat.mul_le_mul_left k hm),
    hc.trans (Nat.mul_le_mul_left k hx)⟩

/-- Direct threshold-set interface, with exact coverage required only on B. -/
theorem required_effective_threshold_count_le
    (E : V → V → Prop) (B : Finset V) (P : SharedReturnPattern E depot a B)
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (tasks : Finset V) (service : V → ℚ) (required : V → ℕ) (T : ℚ) (k : ℕ)
    (ha : a ∈ tasks) (hB : B ⊆ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hremaining : 0 ≤ T - service a)
    (hsupport : ∀ r ∈ ks, SupportsRoute E (routes r))
    (hcover : ∀ i ∈ B, totalVisitCount ks routes i = required i)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ T) :
    (∑ i ∈ B.filter (fun i =>
      (T - service a) / ((k : ℚ) + 1) < chargedService service a i), required i) ≤
      k * ks.card := by
  classical
  let H := B.filter (fun i =>
    (T - service a) / ((k : ℚ) + 1) < chargedService service a i)
  have hH : H ⊆ B := Finset.filter_subset _ _
  have hlarge : ∀ i ∈ H,
      (T - service a) / ((k : ℚ) + 1) < chargedService service a i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hcov : ∀ i ∈ H, totalVisitCount ks routes i = required i := by
    intro i hi
    exact hcover i (hH hi)
  have h := required_effective_large_count_bounds E B P ks routes tasks H
    service required T k ha hB hH hservice hremaining hsupport hlarge hcov hbudget
  exact h.2.1

#print axioms effective_subset_budget
#print axioms route_count_le_of_effective_threshold
#print axioms demand_count_le_serving_capacity
#print axioms required_effective_large_count_le
#print axioms required_effective_large_count_bounds
#print axioms required_effective_threshold_count_le

end UAVProof.SharedReturnLargeServiceCuts
