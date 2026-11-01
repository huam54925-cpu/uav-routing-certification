import LeanCompletion.UAV.HubSpokeSupportExact

/-! Integer packing for the strict non-depot hub. Repeated satellite visits
are charged together with the ensuing hub visit. Empty rows are hub-only routes. -/

namespace UAVProof.HubSpokePacking
open SupportExactFeasibility HubSpokeSupportExact ResourceCuts
variable {B : Type*} [Fintype B] [DecidableEq B]
local instance : BEq (Node B) := instBEqOfDecidableEq

def MatrixFeasible (m : ℕ) (d : B → ℕ) (service : Node B → ℚ) (T : ℚ) : Prop :=
  ∃ n : Fin m → B → ℕ,
    (∀ b, ∑ r, n r b = d b) ∧
    ∀ r, service hub + ∑ b, (service hub + service (satellite b)) * (n r b : ℚ) ≤ T

def visits (l : List B) : List (Node B) :=
  hub :: l.flatMap (fun b => [satellite b, hub])

def route (l : List B) : LegalRoute (depot : Node B) where
  visits := visits l
  visits_nonempty := List.cons_ne_nil _ _
  depot_not_mem := by simp [visits, hub, depot, satellite]
  adjacent_ne := by
    have h : (visits l ++ [depot]).IsChain (· ≠ ·) := by
      induction l with
      | nil => simp [visits, hub, depot]
      | cons b l ih =>
        simpa [visits, List.isChain_cons_cons, hub, satellite, depot] using ih
    simpa [depotRoute, visits, List.isChain_cons_cons, depot, hub] using h

@[simp] theorem route_count_satellite (l : List B) (b : B) :
    (route l).visits.count (satellite b) = l.count b := by
  change (visits l).count (satellite b) = _
  induction l with
  | nil => simp [visits, hub, satellite]
  | cons c l ih =>
    simpa [visits, hub, satellite, List.count_cons, beq_iff_eq] using ih

@[simp] theorem route_count_hub (l : List B) :
    (route l).visits.count hub = 1 + l.length := by
  change (visits l).count hub = _
  induction l with
  | nil => simp [visits, hub]
  | cons b l ih =>
    simp_all [visits, hub, satellite, List.count_cons]
    omega

theorem route_flow (l : List B) (i j : Node B) :
    routeFlow (route l).vertices i j = canonicalFlow 1 (fun b => l.count b) i j := by
  induction l with
  | nil =>
    rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
      simp [routeFlow, route, LegalRoute.vertices, depotRoute, visits, canonicalFlow, hub, depot, satellite]
  | cons b l ih =>
    rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
      simp_all [routeFlow, route, LegalRoute.vertices, depotRoute, visits, canonicalFlow, hub, depot, satellite, List.count_cons]
theorem supported_hub_count {m : ℕ} {d : B → ℕ} (r : LegalRoute (depot : Node B))
    (hs : RouteUsesSupport (canonicalFlow m d) r) :
    r.visits.count hub = 1 + ∑ b, r.visits.count (satellite b) := by
  let f := routeFlow r.vertices
  have shape : ∀ i j, i ≠ hub → j ≠ hub → f i j = 0 :=
    fun i j hi hj => hs i j (canonicalFlow_shape m d i j hi hj)
  have leaf (v : Node B) (hv : v ≠ hub) : f hub v = inFlow Finset.univ f v :=
    (inFlow_eq_hub_entry hub f shape v hv).symm
  have hd : f hub depot = 1 :=
    (leaf depot (by simp [depot, hub])).trans r.inFlow_depot_eq_one
  have hb (b : B) : f hub (satellite b) = r.visits.count (satellite b) :=
    (leaf (satellite b) (by simp [satellite, hub])).trans
      (r.inFlow_eq_visit_count (satellite b) (by simp [satellite, depot]))
  have hh : f hub hub = 0 := hs hub hub (canonicalFlow_no_loops m d hub)
  calc
    r.visits.count hub = outFlow Finset.univ f hub :=
      (r.outFlow_eq_visit_count hub (by simp [hub, depot])).symm
    _ = 1 + ∑ b, r.visits.count (satellite b) := by
      simp only [outFlow, Fintype.sum_option]
      change f hub depot + (f hub hub + ∑ b, f hub (satellite b)) = _
      simp [hd, hh, hb]

theorem service_formula (r : LegalRoute (depot : Node B))
    (h : r.visits.count hub = 1 + ∑ b, r.visits.count (satellite b))
    (service : Node B → ℚ) :
    routeServiceIn r Finset.univ service = service hub +
      ∑ b, (service hub + service (satellite b)) * (r.visits.count (satellite b) : ℚ) := by
  have hd : r.visits.count depot = 0 := List.count_eq_zero.mpr r.depot_not_mem
  simp only [routeServiceIn, Finset.mem_univ, Fintype.sum_option]
  change service depot * (r.visits.count depot : ℚ) +
    (service hub * (r.visits.count hub : ℚ) + ∑ b, service (satellite b) * (r.visits.count (satellite b) : ℚ)) = _
  rw [hd, h]
  simp [Nat.cast_add, Nat.cast_sum, mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, add_assoc]

theorem exact_implies_matrix (m : ℕ) (d : B → ℕ) (service : Node B → ℚ) (T : ℚ)
    (h : ExactFeasible depot (canonicalFlow m d) (required m d) m service T) :
    MatrixFeasible m d service T := by
  obtain ⟨rs, hc, hb, hf⟩ := h
  refine ⟨fun r b => (rs r).visits.count (satellite b), ?_, ?_⟩
  · intro b
    exact hc (satellite b) (by simp [satellite, depot])
  · intro r
    rw [← service_formula (rs r) (supported_hub_count (rs r)
      (route_supported_of_exact _ rs hf r)) service]
    exact hb r

theorem exists_list_counts (n : B → ℕ) : ∃ l : List B, ∀ b, l.count b = n b := by
  classical
  have h : ∀ S : Finset B, ∃ l : List B, ∀ b, l.count b = if b ∈ S then n b else 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨[], by simp⟩
    | @insert a S ha ih =>
      obtain ⟨l, hl⟩ := ih
      refine ⟨List.replicate (n a) a ++ l, ?_⟩
      intro b
      by_cases hb : a = b
      · subst b; simp [hl, ha]
      · simp [List.count_append, List.count_replicate, hl, hb, Ne.symm hb]
  simpa using h Finset.univ

theorem sum_counts (l : List B) : (∑ b, l.count b) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.count_cons, Finset.sum_add_distrib, beq_iff_eq, ih]

theorem matrix_implies_exact (m : ℕ) (d : B → ℕ) (service : Node B → ℚ) (T : ℚ)
    (h : MatrixFeasible m d service T) :
    ExactFeasible depot (canonicalFlow m d) (required m d) m service T := by
  classical
  obtain ⟨n, hn, hb⟩ := h
  choose ls hls using fun r => exists_list_counts (n r)
  have hh (r : Fin m) : (route (ls r)).visits.count hub = 1 + ∑ b, n r b := by
    rw [route_count_hub, ← sum_counts]
    simp [hls]
  refine ⟨fun r => route (ls r), ?_, ?_, ?_⟩
  · intro v hv
    rcases v with _ | (_ | b)
    · exact (hv rfl).elim
    · change (∑ r, (route (ls r)).visits.count hub) = m + ∑ b, d b
      simp only [hh, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      simp [hn]
    · change (∑ r, (route (ls r)).visits.count (satellite b)) = d b
      simpa [hls] using hn b
  · intro r
    rw [service_formula (route (ls r)) (by simpa [hls] using hh r)]
    simpa [hls] using hb r
  · intro i j
    simp only [totalRouteFlow, route_flow]
    rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j) <;>
      simp [canonicalFlow, hls, hn]

/-- The exact packing equivalence, including m = 0 and zero demands.
No sign assumption on rational service costs is needed for this identity. -/
theorem exact_iff_matrix (m : ℕ) (d : B → ℕ) (service : Node B → ℚ) (T : ℚ) :
    ExactFeasible depot (canonicalFlow m d) (required m d) m service T ↔
      MatrixFeasible m d service T :=
  ⟨exact_implies_matrix m d service T, matrix_implies_exact m d service T⟩

end UAVProof.HubSpokePacking

#print axioms UAVProof.HubSpokePacking.exact_iff_matrix
