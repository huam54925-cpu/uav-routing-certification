import LeanCompletion.UAV.ResourceCuts
import Mathlib.Tactic

/-!
# Structural service lower bounds and support-aware capacity cuts

Verification status: the user reported a successful local check of this module
with Lean 4.30.0-rc2 (exit 0; printed axiom lists contain no sorryAx).
The publishing environment has not independently compiled this source.
No new project or changes to existing modules are needed.

Given an allowed-edge relation E on an arbitrary finite vertex type:
  * every allowed departure from the depot goes to a;
  * every allowed departure from b goes to a;
  * depot, a, b are distinct.
Any supported legal route satisfies count(a) >= 1 + count(b).
Other incoming edges at a ARE allowed; hence this is a lower bound, not an equality.

With nonnegative service costs and a,b in the budgeted task set:
  serviceTotal(r) >= s(a) + (s(a)+s(b))*count(b).
For exact fleet coverage this yields
  (s(a)+s(b))*d(b) <= q({b})*(T-s(a)),
and, when T >= s(a), the corresponding outgoing-cut inequality.

The effective work charges each b visit together with its forced a visit.
The initial a visit is charged as an overhead of s(a).
This is an accounting lower bound, not a change to the original service model.
All support and resource hypotheses are explicit. This file does not implement
a general dominator search, multi-hop mandatory-node detection, or sufficiency.
-/

namespace UAVProof.StructuralServiceCuts

open ResourceCuts

variable {V ι : Type*} [DecidableEq V] [Fintype V]
variable {depot a b : V}

/-- A local, finitely checkable pattern in an allowed-edge relation. -/
structure ForcedReturnPattern (E : V → V → Prop) (depot a b : V) : Prop where
  a_ne_depot : a ≠ depot
  b_ne_depot : b ≠ depot
  a_ne_b : a ≠ b
  start : ∀ j, E depot j → j = a
  after_b : ∀ j, E b j → j = a

/-- A route uses no edge outside E. -/
def SupportsRoute (E : V → V → Prop) (r : LegalRoute depot) : Prop :=
  ∀ i j, ¬ E i j → routeFlow r.vertices i j = 0

/-- If the only allowed successor is a, the full outflow uses that one edge. -/
theorem outFlow_eq_unique_target
    (E : V → V → Prop) (r : LegalRoute depot)
    (hsupport : SupportsRoute E r) (i a : V)
    (honly : ∀ j, E i j → j = a) :
    outFlow Finset.univ (routeFlow r.vertices) i = routeFlow r.vertices i a := by
  classical
  unfold outFlow
  apply Finset.sum_eq_single a
  · intro j _ hja
    exact hsupport i j (fun he => hja (honly j he))
  · intro ha
    exact False.elim (ha (Finset.mem_univ a))

/-- Two distinct source vertices contribute separate, additive incoming flows. -/
theorem two_arcs_le_inFlow (x : V → V → ℕ) (p q a : V) (hpq : p ≠ q) :
    x p a + x q a ≤ inFlow Finset.univ x a := by
  classical
  calc
    x p a + x q a = ∑ i ∈ ({p, q} : Finset V), x i a := by simp [hpq]
    _ ≤ ∑ i ∈ (Finset.univ : Finset V), x i a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact Nat.zero_le _
    _ = inFlow Finset.univ x a := rfl

/-- No prohibition on additional incoming edges at a is required. -/
theorem forced_count_lower_bound
    (E : V → V → Prop) (P : ForcedReturnPattern E depot a b)
    (r : LegalRoute depot) (hsupport : SupportsRoute E r) :
    1 + r.visits.count b ≤ r.visits.count a := by
  have hstart : routeFlow r.vertices depot a = 1 :=
    (outFlow_eq_unique_target E r hsupport depot a P.start).symm.trans
      r.outFlow_depot_eq_one
  have hreturn : routeFlow r.vertices b a = r.visits.count b :=
    (outFlow_eq_unique_target E r hsupport b a P.after_b).symm.trans
      (r.outFlow_eq_visit_count b P.b_ne_depot)
  have h := two_arcs_le_inFlow (routeFlow r.vertices) depot b a P.b_ne_depot.symm
  rw [hstart, hreturn, r.inFlow_eq_visit_count a P.a_ne_depot] at h
  exact h

/-- Nonnegative service at all other tasks can only increase the route budget. -/
theorem forced_service_lower_bound
    (E : V → V → Prop) (P : ForcedReturnPattern E depot a b)
    (r : LegalRoute depot) (hsupport : SupportsRoute E r)
    (tasks : Finset V) (service : V → ℚ)
    (ha : a ∈ tasks) (hb : b ∈ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i) :
    service a + (service a + service b) * (r.visits.count b : ℚ) ≤
      routeServiceIn r tasks service := by
  classical
  have hcount : (1 : ℚ) + (r.visits.count b : ℚ) ≤ (r.visits.count a : ℚ) := by
    exact_mod_cast forced_count_lower_bound E P r hsupport
  have hmul := mul_le_mul_of_nonneg_left hcount (hservice a ha)
  have hsub : ({a, b} : Finset V) ⊆ tasks := by
    intro i hi
    rcases Finset.mem_insert.mp hi with hia | hib
    · simpa only [hia] using ha
    · have hib' : i = b := Finset.mem_singleton.mp hib
      simpa only [hib'] using hb
  have hpair : service a * (r.visits.count a : ℚ) +
      service b * (r.visits.count b : ℚ) ≤ routeServiceIn r tasks service := by
    calc
      service a * (r.visits.count a : ℚ) + service b * (r.visits.count b : ℚ) =
          ∑ i ∈ ({a, b} : Finset V), service i * (r.visits.count i : ℚ) := by
        simp [P.a_ne_b]
      _ ≤ ∑ i ∈ tasks, service i * (r.visits.count i : ℚ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro i hi _
        exact mul_nonneg (hservice i hi) (Nat.cast_nonneg _)
      _ = routeServiceIn r tasks service := rfl
  nlinarith only [hmul, hpair]

/-- A b occurrence requires two a services plus one b service. -/
theorem cannot_visit_of_budget_lt
    (E : V → V → Prop) (P : ForcedReturnPattern E depot a b)
    (r : LegalRoute depot) (hsupport : SupportsRoute E r)
    (tasks : Finset V) (service : V → ℚ) (T : ℚ)
    (ha : a ∈ tasks) (hb : b ∈ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hbudget : routeServiceIn r tasks service ≤ T)
    (hgap : T < 2 * service a + service b) :
    r.visits.count b = 0 := by
  by_contra hne
  have hbNat : 1 ≤ r.visits.count b := Nat.pos_of_ne_zero hne
  have hbQ : (1 : ℚ) ≤ (r.visits.count b : ℚ) := by exact_mod_cast hbNat
  have hcoef : 0 ≤ service a + service b := add_nonneg (hservice a ha) (hservice b hb)
  have hmul := mul_le_mul_of_nonneg_left hbQ hcoef
  have hbound := forced_service_lower_bound E P r hsupport tasks service ha hb hservice
  nlinarith only [hmul, hbound, hbudget, hgap]

/-- Each b occurrence is charged together with its forced a occurrence. -/
def chargedWork (r : LegalRoute depot) (service : V → ℚ) (a b : V) : ℚ :=
  (service a + service b) * (r.visits.count b : ℚ)

theorem charged_work_zero_of_not_serves
    (r : LegalRoute depot) (service : V → ℚ) (a b : V)
    (hnot : ¬ Serves r ({b} : Finset V)) :
    chargedWork r service a b = 0 := by
  have hmissing : b ∉ r.visits := by
    intro hb
    exact hnot ⟨b, hb, by simp⟩
  simp [chargedWork, List.count_eq_zero.mpr hmissing]

/-- Exact service coverage determines the total effective work. -/
theorem sum_charged_work
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (service : V → ℚ) (a b : V) (d : ℕ)
    (hcover : totalVisitCount ks routes b = d) :
    (∑ r ∈ ks, chargedWork (routes r) service a b) =
      (service a + service b) * (d : ℚ) := by
  calc
    (∑ r ∈ ks, chargedWork (routes r) service a b) =
        (service a + service b) * (totalVisitCount ks routes b : ℚ) := by
      simp [chargedWork, totalVisitCount, Finset.mul_sum]
    _ = (service a + service b) * (d : ℚ) := by rw [hcover]

/-- The overhead is DERIVED from the original service accounting.
No sign assumption on T-s(a) is needed for the serving-count bound. -/
theorem fleet_charged_capacity
    (E : V → V → Prop) (P : ForcedReturnPattern E depot a b)
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (tasks : Finset V) (service : V → ℚ) (T : ℚ) (d : ℕ)
    (ha : a ∈ tasks) (hb : b ∈ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hsupport : ∀ r ∈ ks, SupportsRoute E (routes r))
    (hcover : totalVisitCount ks routes b = d)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ T) :
    (service a + service b) * (d : ℚ) ≤
      (servingCount ks routes {b} : ℚ) * (T - service a) := by
  apply service_le_serving_capacity ks routes {b}
    (fun r => chargedWork (routes r) service a b)
    (fun r => routeServiceIn (routes r) tasks service - chargedWork (routes r) service a b)
    ((service a + service b) * (d : ℚ)) T (service a)
  · exact sum_charged_work ks routes service a b d hcover
  · intro r _ hnot
    exact charged_work_zero_of_not_serves (routes r) service a b hnot
  · intro r hr
    have h := hbudget r hr
    linarith only [h]
  · intro r hr _
    have h := forced_service_lower_bound E P (routes r) (hsupport r hr)
      tasks service ha hb hservice
    change service a ≤ routeServiceIn (routes r) tasks service -
      ((service a + service b) * ((routes r).visits.count b : ℚ))
    linarith only [h]

/-- Support-aware capacity cut; the real service model has not been changed. -/
theorem structural_capacity_cut
    (E : V → V → Prop) (P : ForcedReturnPattern E depot a b)
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (tasks : Finset V) (service : V → ℚ) (T : ℚ) (d : ℕ)
    (ha : a ∈ tasks) (hb : b ∈ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hsupport : ∀ r ∈ ks, SupportsRoute E (routes r))
    (hcover : totalVisitCount ks routes b = d)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ T)
    (hremaining : 0 ≤ T - service a) :
    (service a + service b) * (d : ℚ) ≤
      (outCutFlow {b} (totalRouteFlow ks routes) : ℚ) * (T - service a) := by
  have hwork := fleet_charged_capacity E P ks routes tasks service T d
    ha hb hservice hsupport hcover hbudget
  have hdepot : depot ∉ ({b} : Finset V) := by simp [P.b_ne_depot.symm]
  have hcount : (servingCount ks routes {b} : ℚ) ≤
      (outCutFlow {b} (totalRouteFlow ks routes) : ℚ) := by
    exact_mod_cast servingCount_le_cutFlow ks routes {b} hdepot
  exact hwork.trans (mul_le_mul_of_nonneg_right hcount hremaining)

/-- Integer structural cut for strictly positive remaining capacity. -/
theorem integer_structural_capacity_cut
    (E : V → V → Prop) (P : ForcedReturnPattern E depot a b)
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (tasks : Finset V) (service : V → ℚ) (T : ℚ) (d : ℕ)
    (ha : a ∈ tasks) (hb : b ∈ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hsupport : ∀ r ∈ ks, SupportsRoute E (routes r))
    (hcover : totalVisitCount ks routes b = d)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ T)
    (hremaining : 0 < T - service a) :
    Int.ceil (((service a + service b) * (d : ℚ)) / (T - service a)) ≤
      (outCutFlow {b} (totalRouteFlow ks routes) : ℤ) := by
  have hcut := structural_capacity_cut E P ks routes tasks service T d
    ha hb hservice hsupport hcover hbudget (le_of_lt hremaining)
  have hdiv : ((service a + service b) * (d : ℚ)) / (T - service a) ≤
      (outCutFlow {b} (totalRouteFlow ks routes) : ℚ) :=
    (div_le_iff₀ hremaining).2 hcut
  apply Int.ceil_le.mpr
  exact_mod_cast hdiv

/-- Positive effective demand rules out zero or negative remaining capacity. -/
theorem positive_demand_requires_base_room
    (E : V → V → Prop) (P : ForcedReturnPattern E depot a b)
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (tasks : Finset V) (service : V → ℚ) (T : ℚ) (d : ℕ)
    (ha : a ∈ tasks) (hb : b ∈ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hsupport : ∀ r ∈ ks, SupportsRoute E (routes r))
    (hcover : totalVisitCount ks routes b = d)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ T)
    (hpositive : 0 < service a + service b) (hd : 0 < d) :
    service a < T := by
  have hwork := fleet_charged_capacity E P ks routes tasks service T d
    ha hb hservice hsupport hcover hbudget
  by_contra hnot
  have hremaining : T - service a ≤ 0 := by linarith only [hnot]
  have hmul := mul_nonpos_of_nonneg_of_nonpos
    (Nat.cast_nonneg (servingCount ks routes {b}) : (0 : ℚ) ≤ _)
    hremaining
  have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hpos := mul_pos hpositive hdQ
  linarith only [hwork, hmul, hpos]

/-- Edge capacities transfer their support to each selected route.
This applies to exact recovery as a special case, and does not assume a pattern. -/
theorem supported_of_total_domination
    (ks : Finset ι) (routes : ι → LegalRoute depot) (x : V → V → ℕ)
    (hdom : ∀ i j, totalRouteFlow ks routes i j ≤ x i j)
    {r : ι} (hr : r ∈ ks) :
    SupportsRoute (fun i j => x i j ≠ 0) (routes r) := by
  intro i j hnot
  have hx : x i j = 0 := by
    by_contra hne
    exact hnot hne
  have hsingle : routeFlow (routes r).vertices i j ≤ totalRouteFlow ks routes i j :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (routeFlow (routes k).vertices i j)) hr
  have hle := hsingle.trans (hdom i j)
  rw [hx] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- A cut directly on a prescribed edge flow. Domination suffices, so exact
edge-flow recovery is included. The support pattern is checked on x itself. -/
theorem fixed_flow_structural_capacity_cut
    (x : V → V → ℕ)
    (P : ForcedReturnPattern (fun i j => x i j ≠ 0) depot a b)
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (tasks : Finset V) (service : V → ℚ) (T : ℚ) (d : ℕ)
    (ha : a ∈ tasks) (hb : b ∈ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hdom : ∀ i j, totalRouteFlow ks routes i j ≤ x i j)
    (hcover : totalVisitCount ks routes b = d)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ T)
    (hremaining : 0 ≤ T - service a) :
    (service a + service b) * (d : ℚ) ≤
      (outCutFlow {b} x : ℚ) * (T - service a) := by
  have hs : ∀ r ∈ ks, SupportsRoute (fun i j => x i j ≠ 0) (routes r) := by
    intro r hr
    exact supported_of_total_domination ks routes x hdom hr
  have hc := structural_capacity_cut (fun i j => x i j ≠ 0) P
    ks routes tasks service T d ha hb hservice hs hcover hbudget hremaining
  have hmono : outCutFlow {b} (totalRouteFlow ks routes) ≤ outCutFlow {b} x := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact hdom i j
  have hmonoQ : (outCutFlow {b} (totalRouteFlow ks routes) : ℚ) ≤
      (outCutFlow {b} x : ℚ) := by exact_mod_cast hmono
  exact hc.trans (mul_le_mul_of_nonneg_right hmonoQ hremaining)

/-- Integer cut directly on a prescribed edge flow. -/
theorem fixed_flow_integer_structural_cut
    (x : V → V → ℕ)
    (P : ForcedReturnPattern (fun i j => x i j ≠ 0) depot a b)
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (tasks : Finset V) (service : V → ℚ) (T : ℚ) (d : ℕ)
    (ha : a ∈ tasks) (hb : b ∈ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hdom : ∀ i j, totalRouteFlow ks routes i j ≤ x i j)
    (hcover : totalVisitCount ks routes b = d)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ T)
    (hremaining : 0 < T - service a) :
    Int.ceil (((service a + service b) * (d : ℚ)) / (T - service a)) ≤
      (outCutFlow {b} x : ℤ) := by
  have hc := fixed_flow_structural_capacity_cut x P ks routes tasks service T d
    ha hb hservice hdom hcover hbudget (le_of_lt hremaining)
  have hd : ((service a + service b) * (d : ℚ)) / (T - service a) ≤
      (outCutFlow {b} x : ℚ) := (div_le_iff₀ hremaining).2 hc
  apply Int.ceil_le.mpr
  exact_mod_cast hd

#print axioms forced_count_lower_bound
#print axioms forced_service_lower_bound
#print axioms cannot_visit_of_budget_lt
#print axioms fleet_charged_capacity
#print axioms structural_capacity_cut
#print axioms integer_structural_capacity_cut
#print axioms positive_demand_requires_base_room
#print axioms supported_of_total_domination
#print axioms fixed_flow_structural_capacity_cut
#print axioms fixed_flow_integer_structural_cut

end UAVProof.StructuralServiceCuts
