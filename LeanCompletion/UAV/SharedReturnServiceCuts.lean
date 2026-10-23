import LeanCompletion.UAV.StructuralServiceCuts

/-!
# Shared-return service cuts

Every departure from the depot and from B must go to a, with depot and a
outside B. Incoming arcs from insert depot B are counted together, so the
initial a service is charged exactly once, even when B has many vertices.
Service counts refer to occurrences, not distinct visited vertices.

The serving-route bound needs no sign assumption on T - service a.
Replacing the serving count by fleet size or cut flow needs nonnegative
remaining capacity; division and rounding need strictly positive capacity.
The set edge cut is implied by all singleton edge cuts under this support
pattern. No strict-strength claim or large-service packing extension is made.
-/

namespace UAVProof.SharedReturnServiceCuts

open ResourceCuts StructuralServiceCuts

variable {V ι : Type*} [DecidableEq V] [Fintype V]
variable {depot a b : V}

/-- A common immediate successor for the depot and every vertex of B. -/
structure SharedReturnPattern (E : V → V → Prop) (depot a : V)
    (B : Finset V) : Prop where
  a_ne_depot : a ≠ depot
  depot_not_mem : depot ∉ B
  a_not_mem : a ∉ B
  start : ∀ j, E depot j → j = a
  after_mem : ∀ b ∈ B, ∀ j, E b j → j = a

/-- The depot is inserted once into a disjoint set of incoming sources. -/
theorem source_arcs_le_inFlow (x : V → V → ℕ) (B : Finset V)
    (hdepot : depot ∉ B) :
    x depot a + ∑ b ∈ B, x b a ≤ inFlow Finset.univ x a := by
  classical
  calc
    x depot a + ∑ b ∈ B, x b a = ∑ i ∈ insert depot B, x i a := by
      rw [Finset.sum_insert hdepot]
    _ ≤ ∑ i ∈ (Finset.univ : Finset V), x i a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
    _ = inFlow Finset.univ x a := rfl

/-- Set counting bound, including the empty set and repeated visits. -/
theorem forced_count_lower_bound
    (E : V → V → Prop) (B : Finset V) (P : SharedReturnPattern E depot a B)
    (r : LegalRoute depot) (hsupport : SupportsRoute E r) :
    1 + ∑ b ∈ B, r.visits.count b ≤ r.visits.count a := by
  have hstart : routeFlow r.vertices depot a = 1 :=
    (outFlow_eq_unique_target E r hsupport depot a P.start).symm.trans
      r.outFlow_depot_eq_one
  have hreturn : ∀ b ∈ B, routeFlow r.vertices b a = r.visits.count b := by
    intro b hb
    have hbd : b ≠ depot := fun h => P.depot_not_mem (h ▸ hb)
    exact (outFlow_eq_unique_target E r hsupport b a (P.after_mem b hb)).symm.trans
      (r.outFlow_eq_visit_count b hbd)
  have h := source_arcs_le_inFlow (routeFlow r.vertices) B P.depot_not_mem
    (a := a)
  rw [hstart, r.inFlow_eq_visit_count a P.a_ne_depot,
    Finset.sum_congr rfl hreturn] at h
  exact h

/-- The effective service charged to each B occurrence. -/
def chargedService (service : V → ℚ) (a : V) (b : V) : ℚ :=
  service a + service b

/-- Each forced a occurrence is charged once, with one additional initial a. -/
theorem forced_service_lower_bound
    (E : V → V → Prop) (B : Finset V) (P : SharedReturnPattern E depot a B)
    (r : LegalRoute depot) (hsupport : SupportsRoute E r)
    (tasks : Finset V) (service : V → ℚ)
    (ha : a ∈ tasks) (hB : B ⊆ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i) :
    service a + routeServiceIn r B (chargedService service a) ≤
      routeServiceIn r tasks service := by
  have hcount : (1 : ℚ) + ∑ b ∈ B, (r.visits.count b : ℚ) ≤
      (r.visits.count a : ℚ) := by
    exact_mod_cast forced_count_lower_bound E B P r hsupport
  have hmul := mul_le_mul_of_nonneg_left hcount (hservice a ha)
  have hsub : insert a B ⊆ tasks := Finset.insert_subset ha hB
  have hsum : service a * (r.visits.count a : ℚ) +
      ∑ b ∈ B, service b * (r.visits.count b : ℚ) ≤
      routeServiceIn r tasks service := by
    calc
      _ = ∑ i ∈ insert a B, service i * (r.visits.count i : ℚ) := by
        rw [Finset.sum_insert P.a_not_mem]
      _ ≤ ∑ i ∈ tasks, service i * (r.visits.count i : ℚ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i hi _ => mul_nonneg (hservice i hi) (Nat.cast_nonneg _))
      _ = routeServiceIn r tasks service := rfl
  unfold routeServiceIn at hsum
  unfold routeServiceIn chargedService
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith only [hmul, hsum]

omit [Fintype V] in
/-- Coverage is needed only on B. -/
theorem sum_charged_work
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (B : Finset V) (service : V → ℚ) (a : V) (required : V → ℕ)
    (hcover : ∀ b ∈ B, totalVisitCount ks routes b = required b) :
    (∑ r ∈ ks, routeServiceIn (routes r) B (chargedService service a)) =
      requiredServiceIn B (chargedService service a) required := by
  unfold routeServiceIn requiredServiceIn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [← Finset.mul_sum, ← Nat.cast_sum]
  rw [show (∑ r ∈ ks, (routes r).visits.count b) = required b from hcover b hb]

/-- Preserve the number of routes serving B, with no remaining-capacity sign assumption. -/
theorem fleet_charged_capacity
    (E : V → V → Prop) (B : Finset V) (P : SharedReturnPattern E depot a B)
    (ks : Finset ι) (routes : ι → LegalRoute depot)
    (tasks : Finset V) (service : V → ℚ) (T : ℚ) (required : V → ℕ)
    (ha : a ∈ tasks) (hB : B ⊆ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i)
    (hsupport : ∀ r ∈ ks, SupportsRoute E (routes r))
    (hcover : ∀ b ∈ B, totalVisitCount ks routes b = required b)
    (hbudget : ∀ r ∈ ks, routeServiceIn (routes r) tasks service ≤ T) :
    requiredServiceIn B (chargedService service a) required ≤
      (servingCount ks routes B : ℚ) * (T - service a) := by
  apply service_le_serving_capacity ks routes B
    (fun r => routeServiceIn (routes r) B (chargedService service a))
    (fun r => routeServiceIn (routes r) tasks service -
      routeServiceIn (routes r) B (chargedService service a))
    _ T (service a)
  · exact sum_charged_work ks routes B service a required hcover
  · intro r _ hnot
    exact routeServiceIn_zero_of_not_serves _ _ _ hnot
  · intro r hr
    linarith only [hbudget r hr]
  · intro r hr _
    have h := forced_service_lower_bound E B P (routes r) (hsupport r hr)
      tasks service ha hB hservice
    linarith only [h]

omit [DecidableEq V] [Fintype V] in
/-- Serving routes are a subset of the selected fleet. -/
theorem servingCount_le_fleet (ks : Finset ι) (routes : ι → LegalRoute depot)
    (B : Finset V) : servingCount ks routes B ≤ ks.card := by
  classical
  exact Finset.card_filter_le _ _

/-- Both combinatorial upper bounds hold without resource sign assumptions. -/
theorem servingCount_bounds (ks : Finset ι) (routes : ι → LegalRoute depot)
    (B : Finset V) (hdepot : depot ∉ B) :
    servingCount ks routes B ≤ ks.card ∧
      servingCount ks routes B ≤ outCutFlow B (totalRouteFlow ks routes) :=
  ⟨servingCount_le_fleet ks routes B, servingCount_le_cutFlow ks routes B hdepot⟩

/-- A reusable arithmetic interface for retaining q while deriving fleet and edge cuts. -/
theorem capacity_bounds (ks : Finset ι) (routes : ι → LegalRoute depot)
    (B : Finset V) (hdepot : depot ∉ B) (W C : ℚ) (hC : 0 ≤ C)
    (hwork : W ≤ (servingCount ks routes B : ℚ) * C) :
    W ≤ (ks.card : ℚ) * C ∧
      W ≤ (outCutFlow B (totalRouteFlow ks routes) : ℚ) * C := by
  obtain ⟨hm, hx⟩ := servingCount_bounds ks routes B hdepot
  constructor
  · exact hwork.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hC)
  · exact hwork.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hx) hC)

/-- Positive capacity gives rounded lower bounds while retaining q. -/
theorem integer_capacity_bounds (ks : Finset ι) (routes : ι → LegalRoute depot)
    (B : Finset V) (hdepot : depot ∉ B) (W C : ℚ) (hC : 0 < C)
    (hwork : W ≤ (servingCount ks routes B : ℚ) * C) :
    Int.ceil (W / C) ≤ (servingCount ks routes B : ℤ) ∧
      (servingCount ks routes B ≤ ks.card ∧
        servingCount ks routes B ≤ outCutFlow B (totalRouteFlow ks routes)) :=
  ⟨ceil_div_le_nat_of_le_mul W C _ hC hwork,
    servingCount_bounds ks routes B hdepot⟩

omit [DecidableEq V] [Fintype V] in
/-- Singleton patterns are exactly the earlier three-vertex pattern. -/
theorem singleton_pattern_iff (E : V → V → Prop) :
    SharedReturnPattern E depot a {b} ↔ ForcedReturnPattern E depot a b := by
  constructor
  · intro P
    exact ⟨P.a_ne_depot, by simpa [ne_comm] using P.depot_not_mem,
      by simpa using P.a_not_mem, P.start, P.after_mem b (by simp)⟩
  · intro P
    refine ⟨P.a_ne_depot, by simpa [ne_comm] using P.b_ne_depot,
      by simpa using P.a_ne_b, P.start, ?_⟩
    intro i hi j hj
    have hi' : i = b := Finset.mem_singleton.mp hi
    subst i
    exact P.after_b j hj

/-- The set counting theorem specializes to the original counting statement. -/
theorem singleton_count
    (E : V → V → Prop) (P : ForcedReturnPattern E depot a b)
    (r : LegalRoute depot) (hsupport : SupportsRoute E r) :
    1 + r.visits.count b ≤ r.visits.count a := by
  simpa using forced_count_lower_bound E {b} (singleton_pattern_iff E |>.mpr P)
    r hsupport

/-- The set resource theorem specializes to the original resource statement. -/
theorem singleton_service
    (E : V → V → Prop) (P : ForcedReturnPattern E depot a b)
    (r : LegalRoute depot) (hsupport : SupportsRoute E r)
    (tasks : Finset V) (service : V → ℚ)
    (ha : a ∈ tasks) (hb : b ∈ tasks)
    (hservice : ∀ i ∈ tasks, 0 ≤ service i) :
    service a + (service a + service b) * (r.visits.count b : ℚ) ≤
      routeServiceIn r tasks service := by
  simpa [routeServiceIn, chargedService] using
    forced_service_lower_bound E {b} (singleton_pattern_iff E |>.mpr P)
      r hsupport tasks service ha (Finset.singleton_subset_iff.mpr hb) hservice

/-- Singleton fleet specialization retains exactly the old serving-route count. -/
theorem singleton_fleet_capacity
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
  simpa [requiredServiceIn, chargedService] using
    fleet_charged_capacity E {b} (singleton_pattern_iff E |>.mpr P)
      ks routes tasks service T (fun _ => d) ha
      (Finset.singleton_subset_iff.mpr hb) hservice hsupport
      (by intro i hi; simpa only [Finset.mem_singleton.mp hi] using hcover) hbudget

/-- If each source in S has only target a outside S, its cut uses that edge. -/
theorem cut_eq_sum_unique_target (x : V → V → ℕ) (S : Finset V)
    (ha : a ∉ S)
    (honly : ∀ i ∈ S, ∀ j, j ≠ a → x i j = 0) :
    outCutFlow S x = ∑ i ∈ S, x i a := by
  classical
  unfold outCutFlow
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_eq_single a
  · intro j _ hja
    exact honly i hi j hja
  · intro hnot
    exact False.elim (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩))

/-- Under the shared-return support, the set cut is the sum of singleton cuts. -/
theorem cut_eq_sum_singletons
    (E : V → V → Prop) (B : Finset V) (P : SharedReturnPattern E depot a B)
    (x : V → V → ℕ) (hsupport : ∀ i j, ¬ E i j → x i j = 0) :
    outCutFlow B x = ∑ b ∈ B, outCutFlow {b} x := by
  have honly : ∀ i ∈ B, ∀ j, j ≠ a → x i j = 0 := by
    intro i hi j hja
    exact hsupport i j (fun h => hja (P.after_mem i hi j h))
  rw [cut_eq_sum_unique_target x B P.a_not_mem honly]
  apply Finset.sum_congr rfl
  intro b hb
  have hab : a ∉ ({b} : Finset V) := by
    simp only [Finset.mem_singleton]
    exact fun h => P.a_not_mem (h.symm ▸ hb)
  symm
  simpa using cut_eq_sum_unique_target x {b} hab
    (by intro i hi; exact honly i ((Finset.mem_singleton.mp hi).symm ▸ hb))

/-- Summing unrounded singleton cuts already implies the rounded set edge cut.
This does not identify the serving-route count with the sum of singleton counts. -/
theorem rounded_set_cut_of_singletons
    (E : V → V → Prop) (B : Finset V) (P : SharedReturnPattern E depot a B)
    (x : V → V → ℕ) (hsupport : ∀ i j, ¬ E i j → x i j = 0)
    (work : V → ℚ) (C : ℚ) (hC : 0 < C)
    (hsingle : ∀ b ∈ B, work b ≤ (outCutFlow {b} x : ℚ) * C) :
    Int.ceil ((∑ b ∈ B, work b) / C) ≤ (outCutFlow B x : ℤ) := by
  apply ceil_div_le_nat_of_le_mul _ C _ hC
  calc
    (∑ b ∈ B, work b) ≤ ∑ b ∈ B, (outCutFlow {b} x : ℚ) * C :=
      Finset.sum_le_sum hsingle
    _ = (outCutFlow B x : ℚ) * C := by
      rw [cut_eq_sum_singletons E B P x hsupport, Nat.cast_sum, Finset.sum_mul]

#print axioms forced_count_lower_bound
#print axioms forced_service_lower_bound
#print axioms fleet_charged_capacity
#print axioms servingCount_bounds
#print axioms capacity_bounds
#print axioms integer_capacity_bounds
#print axioms singleton_pattern_iff
#print axioms singleton_count
#print axioms singleton_service
#print axioms singleton_fleet_capacity
#print axioms cut_eq_sum_singletons
#print axioms rounded_set_cut_of_singletons

end UAVProof.SharedReturnServiceCuts
