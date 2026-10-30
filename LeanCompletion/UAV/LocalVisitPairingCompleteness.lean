import LeanCompletion.UAV.LocalVisitPairing
import LeanCompletion.UAV.SupportExactFeasibility

/-!
# Recovering local visit pairings from exact route families

The first stage recovers the pairing and proves equality with the existing
occurrence lift, including every edge multiplicity. The second stage constructs
a decreasing rank and a suffix-service budget potential from the same routes.
The final stage packages these data as a local certificate and proves equivalence
with exact feasibility, retaining the depot-outflow condition for a fixed fleet size.

Route identifiers and visit positions remain distinct even for identical
routes or repeated physical visits. No nonempty index-type assumption is used.
-/

namespace UAVProof.LocalVisitPairingCompleteness

open scoped BigOperators
open ResourceCuts VisitCopyLift LocalVisitPairing

variable {V : Type*} [DecidableEq V]
variable {ι : Type*} [Fintype ι]
variable (depot : V) (required : V → ℕ) (routes : ι → LegalRoute depot)
variable (hcover : ∀ v, v ≠ depot → totalVisitCount Finset.univ routes v = required v)

/-- Recover the unique route position of every canonical task copy. -/
noncomputable def copyPosition
    (c : Σ v : {v : V // v ≠ depot}, Fin (required v.val)) : VisitPosition routes :=
  (visitPositionCopiesEquiv depot required routes hcover).symm c

@[simp] theorem copyPosition_positionCopy (p : VisitPosition routes) :
    copyPosition depot required routes hcover
      (visitPositionCopiesEquiv depot required routes hcover p) = p := by
  exact (visitPositionCopiesEquiv depot required routes hcover).symm_apply_apply p

@[simp] theorem positionCopy_copyPosition
    (c : Σ v : {v : V // v ≠ depot}, Fin (required v.val)) :
    positionCopy depot required routes hcover
      (copyPosition depot required routes hcover c) = some c := by
  simp [positionCopy, copyPosition]

theorem existsUnique_positionCopy (c : VisitCopy depot required) (hc : c ≠ none) :
    ∃! p : VisitPosition routes, positionCopy depot required routes hcover p = c := by
  cases c with
  | none => exact (hc rfl).elim
  | some c =>
    refine ⟨copyPosition depot required routes hcover c,
      positionCopy_copyPosition depot required routes hcover c, ?_⟩
    intro p hp
    exact positionCopy_injective depot required routes hcover
      (hp.trans (positionCopy_copyPosition depot required routes hcover c).symm)

/-- Successor within one route, or the depot at its last position. -/
noncomputable def nextAt (p : VisitPosition routes) : VisitCopy depot required :=
  if h : p.2.val + 1 < (routes p.1).visits.length then
    positionCopy depot required routes hcover ⟨p.1, ⟨p.2.val + 1, h⟩⟩
  else none

/-- Predecessor within one route, or the depot at its first position. -/
noncomputable def prevAt (p : VisitPosition routes) : VisitCopy depot required :=
  if h : 0 < p.2.val then
    positionCopy depot required routes hcover
      ⟨p.1, ⟨p.2.val - 1, by have := p.2.isLt; omega⟩⟩
  else none

noncomputable def nextCopy : VisitCopy depot required → VisitCopy depot required
  | none => none
  | some c => nextAt depot required routes hcover (copyPosition depot required routes hcover c)

noncomputable def prevCopy : VisitCopy depot required → VisitCopy depot required
  | none => none
  | some c => prevAt depot required routes hcover (copyPosition depot required routes hcover c)

@[simp] theorem nextAt_eq_none_iff (p : VisitPosition routes) :
    nextAt depot required routes hcover p = none ↔
      p.2.val + 1 = (routes p.1).visits.length := by
  unfold nextAt
  split_ifs with h
  · simp only [positionCopy_ne_none, false_iff]
    omega
  · simp only [true_iff]
    have := p.2.isLt
    omega

@[simp] theorem prevAt_eq_none_iff (p : VisitPosition routes) :
    prevAt depot required routes hcover p = none ↔ p.2.val = 0 := by
  unfold prevAt
  split_ifs with h
  · simp only [positionCopy_ne_none, false_iff]
    omega
  · simp only [true_iff]
    omega

@[simp] theorem nextCopy_positionCopy (p : VisitPosition routes) :
    nextCopy depot required routes hcover (positionCopy depot required routes hcover p) =
      nextAt depot required routes hcover p := by
  simp [positionCopy, nextCopy]

@[simp] theorem prevCopy_positionCopy (p : VisitPosition routes) :
    prevCopy depot required routes hcover (positionCopy depot required routes hcover p) =
      prevAt depot required routes hcover p := by
  simp [positionCopy, prevCopy]

/-- The depot does not match arrivals to departures, even between equal routes. -/
noncomputable def pairingOfRoutes : Pairing (VisitCopy depot required) none where
  next := nextCopy depot required routes hcover
  prev := prevCopy depot required routes hcover
  prev_next := by
    intro c hc hn
    obtain ⟨p, rfl, _⟩ := existsUnique_positionCopy depot required routes hcover c hc
    rw [nextCopy_positionCopy] at hn ⊢
    unfold nextAt at hn ⊢
    split_ifs with h
    · rw [prevCopy_positionCopy]
      simp only [prevAt]
      rw [dif_pos (by omega)]
      congr 2
    · exact (hn (dif_neg h)).elim
  next_prev := by
    intro c hc hp
    obtain ⟨p, rfl, _⟩ := existsUnique_positionCopy depot required routes hcover c hc
    rw [prevCopy_positionCopy] at hp ⊢
    unfold prevAt at hp ⊢
    split_ifs with h
    · rw [nextCopy_positionCopy]
      simp only [nextAt]
      rw [dif_pos (by have := p.2.isLt; omega)]
      congr 2
      apply Fin.ext
      dsimp
      omega
    · exact (hp (dif_neg h)).elim

@[simp] theorem pairingOfRoutes_next_none :
    (pairingOfRoutes depot required routes hcover).next none = none := rfl

@[simp] theorem pairingOfRoutes_prev_none :
    (pairingOfRoutes depot required routes hcover).prev none = none := rfl

@[simp] theorem pairingOfRoutes_next_position (p : VisitPosition routes) :
    (pairingOfRoutes depot required routes hcover).next
      (positionCopy depot required routes hcover p) = nextAt depot required routes hcover p :=
  nextCopy_positionCopy depot required routes hcover p

@[simp] theorem pairingOfRoutes_prev_position (p : VisitPosition routes) :
    (pairingOfRoutes depot required routes hcover).prev
      (positionCopy depot required routes hcover p) = prevAt depot required routes hcover p :=
  prevCopy_positionCopy depot required routes hcover p

/-- A singleton visit both starts and ends at the depot, without depot pairing. -/
theorem pairingOfRoutes_singleton (p : VisitPosition routes)
    (hlen : (routes p.1).visits.length = 1) :
    (pairingOfRoutes depot required routes hcover).next
      (positionCopy depot required routes hcover p) = none ∧
    (pairingOfRoutes depot required routes hcover).prev
      (positionCopy depot required routes hcover p) = none := by
  rw [pairingOfRoutes_next_position, pairingOfRoutes_prev_position,
    nextAt_eq_none_iff, prevAt_eq_none_iff]
  have := p.2.isLt
  omega

/- The next two list lemmas identify the actual consecutive edge, including
the boundary edge. They do not infer adjacency from degree information. -/
private theorem chain_next {C : Type*} {n : ℕ} (d : C) (f : Fin n → C)
    (R : C → C → Prop) (hchain : (d :: (List.ofFn f ++ [d])).IsChain R)
    (i : Fin n) :
    R (f i) (if h : i.val + 1 < n then f ⟨i.val + 1, h⟩ else d) := by
  have h := List.isChain_iff_getElem.mp hchain.tail i.val
    (by simp)
  by_cases hi : i.val + 1 < n
  · simpa [List.getElem_append, hi, i.isLt] using h
  · have he : i.val + 1 = n := by omega
    simpa [List.getElem_append, hi, i.isLt, he] using h

private theorem chain_prev {C : Type*} {n : ℕ} (d : C) (f : Fin n → C)
    (R : C → C → Prop) (hchain : (d :: (List.ofFn f ++ [d])).IsChain R)
    (i : Fin n) :
    R (if h : 0 < i.val then f ⟨i.val - 1, by omega⟩ else d) (f i) := by
  have h := List.isChain_iff_getElem.mp hchain i.val (by simp)
  rcases i with ⟨i, hi⟩
  cases i with
  | zero => simpa [List.getElem_append, hi] using h
  | succ j =>
    simpa [List.getElem_append, hi, show j < n by omega] using h

/-- The exact successor edge occurs in the original lifted route. -/
theorem liftedFlow_nextAt_pos (p : VisitPosition routes) :
    0 < liftedFlow depot required routes hcover
      (positionCopy depot required routes hcover p) (nextAt depot required routes hcover p) := by
  have h := exact_family_supported none (liftedLegalRoute depot required routes hcover)
    (liftedFlow depot required routes hcover) (fun _ _ => rfl) p.1
  change (none :: (List.ofFn (fun k => positionCopy depot required routes hcover ⟨p.1, k⟩)
    ++ [none])).IsChain _ at h
  exact chain_next none _ _ h p.2

/-- The exact predecessor edge occurs in the original lifted route. -/
theorem liftedFlow_prevAt_pos (p : VisitPosition routes) :
    0 < liftedFlow depot required routes hcover (prevAt depot required routes hcover p)
      (positionCopy depot required routes hcover p) := by
  have h := exact_family_supported none (liftedLegalRoute depot required routes hcover)
    (liftedFlow depot required routes hcover) (fun _ _ => rfl) p.1
  change (none :: (List.ofFn (fun k => positionCopy depot required routes hcover ⟨p.1, k⟩)
    ++ [none])).IsChain _ at h
  exact chain_prev none _ _ h p.2

/-- A specified positive entry of a natural-valued unit sum is exactly one;
every other entry is zero. The specified edge is essential to this conclusion. -/
private theorem unit_sum_entry {C : Type*} [Fintype C] [DecidableEq C]
    (f : C → ℕ) (hsum : ∑ c, f c = 1) (k : C) (hk : 0 < f k) (b : C) :
    f b = if k = b then 1 else 0 := by
  have hsplit := Finset.sum_erase_add Finset.univ f (Finset.mem_univ k)
  rw [hsum] at hsplit
  have hkone : f k = 1 := by omega
  have hzero : ∑ c ∈ Finset.univ.erase k, f c = 0 := by omega
  by_cases hb : k = b
  · subst b
    simp [hkone]
  · have hle := Finset.single_le_sum (fun c _ => Nat.zero_le (f c))
      (Finset.mem_erase.mpr ⟨Ne.symm hb, Finset.mem_univ b⟩)
    rw [hzero] at hle
    simp [hb, Nat.eq_zero_of_le_zero hle]

/-- Exact edge multiplicities in a task row, including the return to the depot. -/
theorem liftedFlow_from_position [Finite V]
    (p : VisitPosition routes) (b : VisitCopy depot required) :
    liftedFlow depot required routes hcover (positionCopy depot required routes hcover p) b =
      if nextAt depot required routes hcover p = b then 1 else 0 := by
  classical
  letI := Fintype.ofFinite V
  exact unit_sum_entry _
    (liftedFlow_unit_degrees depot required routes hcover _
      (positionCopy_ne_none depot required routes hcover p)).1
    _ (liftedFlow_nextAt_pos depot required routes hcover p) b

/-- Exact edge multiplicities in a task column, including departure from the depot. -/
theorem liftedFlow_to_position [Finite V]
    (a : VisitCopy depot required) (p : VisitPosition routes) :
    liftedFlow depot required routes hcover a (positionCopy depot required routes hcover p) =
      if a = prevAt depot required routes hcover p then 1 else 0 := by
  classical
  letI := Fintype.ofFinite V
  simpa only [eq_comm] using unit_sum_entry
    (fun a => liftedFlow depot required routes hcover a
      (positionCopy depot required routes hcover p))
    (liftedFlow_unit_degrees depot required routes hcover _
      (positionCopy_ne_none depot required routes hcover p)).2
    _ (liftedFlow_prevAt_pos depot required routes hcover p) a

/-- Task-to-task edges agree, using the actual next position on the same route. -/
theorem pairedFlow_task_task [Finite V] (p q : VisitPosition routes) :
    pairedFlow (pairingOfRoutes depot required routes hcover)
      (positionCopy depot required routes hcover p) (positionCopy depot required routes hcover q) =
    liftedFlow depot required routes hcover
      (positionCopy depot required routes hcover p)
      (positionCopy depot required routes hcover q) := by
  classical
  letI := Fintype.ofFinite V
  rw [flow_from_task _ _ _ (positionCopy_ne_none depot required routes hcover p),
    pairingOfRoutes_next_position, liftedFlow_from_position]

/-- Depot departures are exactly first positions, independently for each route. -/
theorem pairedFlow_depot_task [Finite V] (p : VisitPosition routes) :
    pairedFlow (pairingOfRoutes depot required routes hcover) none
      (positionCopy depot required routes hcover p) =
    liftedFlow depot required routes hcover none (positionCopy depot required routes hcover p) := by
  classical
  letI := Fintype.ofFinite V
  rw [flow_to_task _ _ _ (positionCopy_ne_none depot required routes hcover p),
    pairingOfRoutes_prev_position, liftedFlow_to_position]

/-- Returns to the depot are exactly last positions. -/
theorem pairedFlow_task_depot [Finite V] (p : VisitPosition routes) :
    pairedFlow (pairingOfRoutes depot required routes hcover)
      (positionCopy depot required routes hcover p) none =
    liftedFlow depot required routes hcover (positionCopy depot required routes hcover p) none := by
  classical
  letI := Fintype.ofFinite V
  rw [flow_from_task _ _ _ (positionCopy_ne_none depot required routes hcover p),
    pairingOfRoutes_next_position, liftedFlow_from_position]

/-- Neither representation creates a depot-to-depot edge. -/
theorem pairedFlow_depot_depot :
    pairedFlow (pairingOfRoutes depot required routes hcover) none none =
    liftedFlow depot required routes hcover none none := by
  classical
  rw [liftedFlow_no_self_loops]
  simp [pairedFlow]

/-- Equality of every copy edge multiplicity, not merely support or degrees. -/
theorem pairedFlow_pairingOfRoutes_eq_liftedFlow [Finite V] :
    pairedFlow (pairingOfRoutes depot required routes hcover) =
      liftedFlow depot required routes hcover := by
  classical
  funext a b
  by_cases ha : a = none
  · subst a
    by_cases hb : b = none
    · subst b
      exact pairedFlow_depot_depot depot required routes hcover
    · obtain ⟨q, rfl, _⟩ := existsUnique_positionCopy depot required routes hcover b hb
      exact pairedFlow_depot_task depot required routes hcover q
  · obtain ⟨p, rfl, _⟩ := existsUnique_positionCopy depot required routes hcover a ha
    by_cases hb : b = none
    · subst b
      exact pairedFlow_task_depot depot required routes hcover p
    · obtain ⟨q, rfl, _⟩ := existsUnique_positionCopy depot required routes hcover b hb
      exact pairedFlow_task_task depot required routes hcover p q

/-- Exact input route multiplicities are preserved by the recovered pairing. -/
theorem pairingOfRoutes_projects_exact [Fintype V] (x : V → V → ℕ)
    (hexact : ∀ u v, totalRouteFlow Finset.univ routes u v = x u v) :
    ∀ u v, projectFlow (project depot required)
      (pairedFlow (pairingOfRoutes depot required routes hcover)) u v = x u v := by
  classical
  rw [pairedFlow_pairingOfRoutes_eq_liftedFlow]
  exact liftedFlow_projects_exact depot required routes hcover x hexact

/-- An empty indexed route family recovers the zero copy flow. -/
theorem pairedFlow_empty [Finite V] [IsEmpty ι] :
    pairedFlow (pairingOfRoutes depot required routes hcover) =
      fun _ _ => 0 := by
  classical
  rw [pairedFlow_pairingOfRoutes_eq_liftedFlow]
  funext a b
  simp [liftedFlow, totalRouteFlow]

/-- Remaining edges to the depot: the last visit has rank one. -/
noncomputable def routeRank : VisitCopy depot required → ℕ
  | none => 0
  | some c =>
    let p := copyPosition depot required routes hcover c
    (routes p.1).visits.length - p.2.val

@[simp] theorem routeRank_none : routeRank depot required routes hcover none = 0 := rfl

@[simp] theorem routeRank_position (p : VisitPosition routes) :
    routeRank depot required routes hcover (positionCopy depot required routes hcover p) =
      (routes p.1).visits.length - p.2.val := by
  exact congrArg (fun q : VisitPosition routes => (routes q.1).visits.length - q.2.val)
    (copyPosition_positionCopy depot required routes hcover p)

/-- The return edge has rank exactly one at its source, also on singleton routes. -/
theorem routeRank_last (p : VisitPosition routes)
    (hlast : p.2.val + 1 = (routes p.1).visits.length) :
    (pairingOfRoutes depot required routes hcover).next
        (positionCopy depot required routes hcover p) = none ∧
      routeRank depot required routes hcover
        (positionCopy depot required routes hcover p) = 1 := by
  rw [pairingOfRoutes_next_position, nextAt_eq_none_iff, routeRank_position]
  exact ⟨hlast, by omega⟩

/-- Every task successor strictly reduces the number of edges remaining. -/
theorem routeRank_descending :
    DescendingRank (pairingOfRoutes depot required routes hcover)
      (routeRank depot required routes hcover) := by
  intro c hc
  obtain ⟨p, rfl, _⟩ := existsUnique_positionCopy depot required routes hcover c hc
  by_cases hnext : p.2.val + 1 < (routes p.1).visits.length
  · rw [pairingOfRoutes_next_position, nextAt, dif_pos hnext,
      routeRank_position, routeRank_position]
    dsimp
    omega
  · have hlast : p.2.val + 1 = (routes p.1).visits.length := by
      have := p.2.isLt
      omega
    obtain ⟨hn, hr⟩ := routeRank_last depot required routes hcover p hlast
    rw [hn, hr, routeRank_none]
    exact Nat.zero_lt_one

omit [DecidableEq V] in
/-- The suffix includes the current visit and counts repeated visits separately. -/
theorem suffix_service_step (service : V → ℚ) (visits : List V)
    (i : Fin visits.length) :
    service (visits.get i) + ((visits.drop (i.val + 1)).map service).sum =
      ((visits.drop i.val).map service).sum := by
  conv_rhs => rw [List.drop_eq_getElem_cons i.isLt]
  simp

/-- Remaining service cost of the route suffix, with zero at the depot. -/
noncomputable def routePotential (service : V → ℚ) : VisitCopy depot required → ℚ
  | none => 0
  | some c =>
    let p := copyPosition depot required routes hcover c
    (((routes p.1).visits.drop p.2.val).map service).sum

@[simp] theorem routePotential_none (service : V → ℚ) :
    routePotential depot required routes hcover service none = 0 := rfl

@[simp] theorem routePotential_position (service : V → ℚ) (p : VisitPosition routes) :
    routePotential depot required routes hcover service
      (positionCopy depot required routes hcover p) =
        (((routes p.1).visits.drop p.2.val).map service).sum := by
  exact congrArg (fun q : VisitPosition routes =>
    (((routes q.1).visits.drop q.2.val).map service).sum)
    (copyPosition_positionCopy depot required routes hcover p)

/-- At the next copy the suffix drops the current visit; at the depot it is empty. -/
theorem routePotential_next_position (service : V → ℚ) (p : VisitPosition routes) :
    routePotential depot required routes hcover service
      ((pairingOfRoutes depot required routes hcover).next
        (positionCopy depot required routes hcover p)) =
      (((routes p.1).visits.drop (p.2.val + 1)).map service).sum := by
  rw [pairingOfRoutes_next_position, nextAt]
  split_ifs with hnext
  · rw [routePotential_position]
  · rw [routePotential_none, List.drop_eq_nil_of_le (by omega)]
    rfl

/-- Exact cost telescoping; zero service fees need not decrease the potential. -/
theorem routePotential_step (service : V → ℚ) (c : VisitCopy depot required)
    (hc : c ≠ none) :
    copyService depot required service c +
      routePotential depot required routes hcover service
        ((pairingOfRoutes depot required routes hcover).next c) =
      routePotential depot required routes hcover service c := by
  obtain ⟨p, rfl, _⟩ := existsUnique_positionCopy depot required routes hcover c hc
  rw [routePotential_next_position, routePotential_position]
  change service ((routes p.1).visits.get p.2) + _ = _
  exact suffix_service_step service (routes p.1).visits p.2

/-- A depot departure is precisely the zeroth position of a unique copy's route. -/
theorem exists_first_position_of_prev_none (c : VisitCopy depot required)
    (hc : c ≠ none) (hprev : (pairingOfRoutes depot required routes hcover).prev c = none) :
    ∃ p : VisitPosition routes,
      positionCopy depot required routes hcover p = c ∧ p.2.val = 0 := by
  obtain ⟨p, hp, _⟩ := existsUnique_positionCopy depot required routes hcover c hc
  refine ⟨p, hp, ?_⟩
  rw [← hp, pairingOfRoutes_prev_position, prevAt_eq_none_iff] at hprev
  exact hprev

/-- At the first position, the suffix is the entire route's counted service cost. -/
theorem routePotential_first [Fintype V] (service : V → ℚ) (p : VisitPosition routes)
    (hfirst : p.2.val = 0) :
    routePotential depot required routes hcover service
      (positionCopy depot required routes hcover p) =
      routeServiceIn (routes p.1) Finset.univ service := by
  rw [routePotential_position, hfirst, List.drop_zero, route_service_eq_list_sum]

/-- Every departure potential equals the cost of its original physical route. -/
theorem routePotential_start [Fintype V] (service : V → ℚ) (c : VisitCopy depot required)
    (hc : c ≠ none) (hprev : (pairingOfRoutes depot required routes hcover).prev c = none) :
    ∃ r : ι, routePotential depot required routes hcover service c =
      routeServiceIn (routes r) Finset.univ service := by
  obtain ⟨p, rfl, hfirst⟩ :=
    exists_first_position_of_prev_none depot required routes hcover c hc hprev
  exact ⟨p.1, routePotential_first depot required routes hcover service p hfirst⟩

/-- Turn the exact suffix potential into the existing budget-certificate data.
Only the input route budgets are needed; zero fees are allowed. -/
noncomputable def routePotential_isBudgetPotential [Fintype V]
    (service : V → ℚ) (T : ℚ)
    (hbudget : ∀ r, routeServiceIn (routes r) Finset.univ service ≤ T) :
    BudgetPotential (pairingOfRoutes depot required routes hcover)
      (copyService depot required service) T where
  value := routePotential depot required routes hcover service
  depot_zero := routePotential_none depot required routes hcover service
  step := fun c hc => (routePotential_step depot required routes hcover service c hc).le
  start := by
    intro c hc hprev
    obtain ⟨r, hr⟩ := routePotential_start depot required routes hcover service c hc hprev
    rw [hr]
    exact hbudget r

include hcover in
/-- Any budget-feasible exact finite route family constructs all local certificate
components. The data-valued budget potential is expressed via `Nonempty`.
The final fixed-route-count feasibility equivalence is not asserted here. -/
theorem exists_local_certificate_of_exact_family [Fintype V] (x : V → V → ℕ)
    (hexact : ∀ u v, totalRouteFlow Finset.univ routes u v = x u v)
    (service : V → ℚ) (T : ℚ)
    (hbudget : ∀ r, routeServiceIn (routes r) Finset.univ service ≤ T) :
    ∃ (p : Pairing (VisitCopy depot required) none) (rank : VisitCopy depot required → ℕ),
      DescendingRank p rank ∧
      (∀ u v, projectFlow (project depot required) (pairedFlow p) u v = x u v) ∧
      Nonempty (BudgetPotential p (copyService depot required service) T) := by
  classical
  exact ⟨pairingOfRoutes depot required routes hcover, routeRank depot required routes hcover,
    routeRank_descending depot required routes hcover,
    pairingOfRoutes_projects_exact depot required routes hcover x hexact,
    ⟨routePotential_isBudgetPotential depot required routes hcover service T hbudget⟩⟩

section Certificate

open SupportExactFeasibility

variable [Fintype V]

/-- Existence of local pairing, cycle-exclusion rank, exact physical projection
and budget-potential data. The route count is supplied separately by depot outflow. -/
def HasLocalCertificate (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ) : Prop :=
  ∃ (p : Pairing (VisitCopy depot required) none) (rank : VisitCopy depot required → ℕ),
    DescendingRank p rank ∧
    (∀ u v, projectFlow (project depot required) (pairedFlow p) u v = x u v) ∧
    Nonempty (BudgetPotential p (copyService depot required service) T)

/-- Recover a local certificate from any prescribed-size exact feasible family. -/
theorem hasLocalCertificate_of_exactFeasible
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (m : ℕ)
    (service : V → ℚ) (T : ℚ)
    (h : ExactFeasible depot x required m service T) :
    HasLocalCertificate depot required x service T := by
  obtain ⟨routes, hcounts, hbudget, hexact⟩ := h
  exact exists_local_certificate_of_exact_family depot required routes hcounts
    x hexact service T hbudget

/-- The sufficient direction reconstructs the canonical number of routes.
Reorder coverage/exactness/budget into the existing ExactFeasible convention. -/
theorem exactFeasible_of_hasLocalCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ)
    (hloop : ∀ v, x v v = 0) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T)
    (h : HasLocalCertificate depot required x service T) :
    ExactFeasible depot x required (outFlow Finset.univ x depot) service T := by
  obtain ⟨p, rank, hrank, hproject, ⟨cert⟩⟩ := h
  obtain ⟨rs, hcounts, hexact, hbudget⟩ :=
    exact_decomposition_of_pairing_potential depot required x hloop p rank hrank
      hproject service T hservice hT cert
  exact ⟨rs, hcounts, hbudget, hexact⟩

/-- With the canonical fleet size, local certificates exactly characterize feasibility. -/
theorem exactFeasible_iff_hasLocalCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ)
    (hloop : ∀ v, x v v = 0) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T) :
    ExactFeasible depot x required (outFlow Finset.univ x depot) service T ↔
      HasLocalCertificate depot required x service T := by
  exact ⟨hasLocalCertificate_of_exactFeasible depot required x _ service T,
    exactFeasible_of_hasLocalCertificate depot required x service T hloop hservice hT⟩

/-- Fixed-fleet feasibility retains the necessary depot-outflow equality.
Neither a positive fleet size nor a nonempty task set is assumed. -/
theorem exactFeasible_iff_count_and_hasLocalCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (m : ℕ)
    (service : V → ℚ) (T : ℚ)
    (hloop : ∀ v, x v v = 0) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T) :
    ExactFeasible depot x required m service T ↔
      m = outFlow Finset.univ x depot ∧ HasLocalCertificate depot required x service T := by
  constructor
  · intro h
    have hdegree := (exact_has_degrees depot x required m service T h).1 depot
    have hcount : m = outFlow Finset.univ x depot := by
      simpa only [prescribedDegree, if_pos rfl] using hdegree.symm
    exact ⟨hcount, hasLocalCertificate_of_exactFeasible depot required x m service T h⟩
  · rintro ⟨hcount, hcert⟩
    rw [hcount]
    exact exactFeasible_of_hasLocalCertificate depot required x service T hloop hservice hT hcert

/-- The empty family witnesses zero demand and zero flow, for any service function. -/
theorem zero_exactFeasible (depot : V) (service : V → ℚ) (T : ℚ) :
    ExactFeasible depot (fun _ _ => 0) (fun _ => 0) 0 service T := by
  refine ⟨fun i => Fin.elim0 i, ?_, ?_, ?_⟩
  · intro v _
    simp [totalVisitCount]
  · intro i
    exact Fin.elim0 i
  · intro u v
    simp [totalRouteFlow]

/-- Empty instances also have a certificate; in particular zero fees are allowed. -/
theorem zero_hasLocalCertificate (depot : V) (service : V → ℚ) (T : ℚ) :
    HasLocalCertificate depot (fun _ => 0) (fun _ _ => 0) service T :=
  hasLocalCertificate_of_exactFeasible depot _ _ 0 service T
    (zero_exactFeasible depot service T)

end Certificate

end UAVProof.LocalVisitPairingCompleteness

#print axioms UAVProof.LocalVisitPairingCompleteness.copyPosition
#print axioms UAVProof.LocalVisitPairingCompleteness.existsUnique_positionCopy
#print axioms UAVProof.LocalVisitPairingCompleteness.pairingOfRoutes
#print axioms UAVProof.LocalVisitPairingCompleteness.pairedFlow_pairingOfRoutes_eq_liftedFlow
#print axioms UAVProof.LocalVisitPairingCompleteness.pairingOfRoutes_projects_exact
#print axioms UAVProof.LocalVisitPairingCompleteness.pairingOfRoutes_singleton
#print axioms UAVProof.LocalVisitPairingCompleteness.pairedFlow_empty
#print axioms UAVProof.LocalVisitPairingCompleteness.routeRank
#print axioms UAVProof.LocalVisitPairingCompleteness.routeRank_last
#print axioms UAVProof.LocalVisitPairingCompleteness.routeRank_descending
#print axioms UAVProof.LocalVisitPairingCompleteness.routePotential
#print axioms UAVProof.LocalVisitPairingCompleteness.routePotential_step
#print axioms UAVProof.LocalVisitPairingCompleteness.routePotential_start
#print axioms UAVProof.LocalVisitPairingCompleteness.routePotential_isBudgetPotential
#print axioms UAVProof.LocalVisitPairingCompleteness.exists_local_certificate_of_exact_family

#check UAVProof.LocalVisitPairingCompleteness.HasLocalCertificate
#print UAVProof.LocalVisitPairingCompleteness.HasLocalCertificate
#check UAVProof.LocalVisitPairingCompleteness.hasLocalCertificate_of_exactFeasible
#check UAVProof.LocalVisitPairingCompleteness.exactFeasible_of_hasLocalCertificate
#check UAVProof.LocalVisitPairingCompleteness.exactFeasible_iff_hasLocalCertificate
#check UAVProof.LocalVisitPairingCompleteness.exactFeasible_iff_count_and_hasLocalCertificate
#check UAVProof.LocalVisitPairingCompleteness.exists_local_certificate_of_exact_family
#print axioms UAVProof.LocalVisitPairingCompleteness.HasLocalCertificate
#print axioms UAVProof.LocalVisitPairingCompleteness.hasLocalCertificate_of_exactFeasible
#print axioms UAVProof.LocalVisitPairingCompleteness.exactFeasible_of_hasLocalCertificate
#print axioms UAVProof.LocalVisitPairingCompleteness.exactFeasible_iff_hasLocalCertificate
#print axioms UAVProof.LocalVisitPairingCompleteness.exactFeasible_iff_count_and_hasLocalCertificate
#print axioms UAVProof.LocalVisitPairingCompleteness.zero_exactFeasible
#print axioms UAVProof.LocalVisitPairingCompleteness.zero_hasLocalCertificate
