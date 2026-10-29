import LeanCompletion.UAV.CopyProfileDecomposition

/-!
# Local visit pairing, cycle exclusion and local budget certificates

Proof candidate; Lean compilation and axiom reports are pending.
No toolchain or dependency changes are required.

A visit is an occurrence, not just a physical vertex. Its predecessor and
successor pair one incoming edge with one outgoing edge. At the depot we
do NOT pair arrivals with departures: routes end and begin separately.

The derived copy flow is not stored as a dense matrix. Mutual consistency
of predecessor/successor gives unit task degrees. A strictly decreasing
natural rank gives positive depot-free cuts. A rational suffix-cost upper
bound gives every route's service budget. Existing theorems then supply
all copy capacity cuts and the physical exact decomposition.

This is a sufficient sparse certificate, not a minimal-information theorem,
not a polynomial-time search algorithm, and not a pairing of physical arc
tokens without occurrence labels. The rank and potential are additional
certificates. No converse/completeness theorem is claimed in this module.
Only service costs are included; travel costs are absent.
-/

namespace UAVProof.LocalVisitPairing

open scoped BigOperators

open ResourceCuts VisitCopyLift CopyLiftObstruction CopyProfileDecomposition

/-- Local pairing on visit occurrences. Depot entries of next/prev are ignored. -/
structure Pairing (C : Type*) (depot : C) where
  next : C → C
  prev : C → C
  prev_next : ∀ c, c ≠ depot → next c ≠ depot → prev (next c) = c
  next_prev : ∀ c, c ≠ depot → prev c ≠ depot → next (prev c) = c

section Generic

variable {C : Type*} [Fintype C] [DecidableEq C] {depot : C}

/-- Depot departures are selected by prev c = depot; task edges by next. -/
def pairedFlow (p : Pairing C depot) (a b : C) : ℕ :=
  if a = depot then
    if b ≠ depot ∧ p.prev b = depot then 1 else 0
  else
    if p.next a = b then 1 else 0

theorem flow_from_task (p : Pairing C depot) (a b : C) (ha : a ≠ depot) :
    pairedFlow p a b = if p.next a = b then 1 else 0 := by
  simp [pairedFlow, ha]

theorem next_prev_iff (p : Pairing C depot) (a b : C)
    (ha : a ≠ depot) (hb : b ≠ depot) :
    p.next a = b ↔ a = p.prev b := by
  constructor
  · intro hnext
    have hnd : p.next a ≠ depot := by
      rw [hnext]
      exact hb
    have h := p.prev_next a ha hnd
    rw [hnext] at h
    exact h.symm
  · intro hprev
    have hpd : p.prev b ≠ depot := by
      rw [← hprev]
      exact ha
    have h := p.next_prev b hb hpd
    rw [← hprev] at h
    exact h

/-- The reconstructed column has exactly the recorded predecessor. -/
theorem flow_to_task (p : Pairing C depot) (a b : C) (hb : b ≠ depot) :
    pairedFlow p a b = if a = p.prev b then 1 else 0 := by
  by_cases ha : a = depot
  · subst a
    simp [pairedFlow, hb, eq_comm]
  · rw [flow_from_task p a b ha]
    simp only [next_prev_iff p a b ha hb]

theorem paired_out_one (p : Pairing C depot) (c : C) (hc : c ≠ depot) :
    outFlow Finset.univ (pairedFlow p) c = 1 := by
  simp [outFlow, pairedFlow, hc]

theorem paired_in_one (p : Pairing C depot) (c : C) (hc : c ≠ depot) :
    inFlow Finset.univ (pairedFlow p) c = 1 := by
  unfold inFlow
  simp_rw [flow_to_task p _ c hc]
  simp

theorem next_edge_one (p : Pairing C depot) (c : C) (hc : c ≠ depot) :
    pairedFlow p c (p.next c) = 1 := by
  simp [pairedFlow, hc]

theorem positive_task_edge_next (p : Pairing C depot) (a b : C)
    (ha : a ≠ depot) (hpos : 0 < pairedFlow p a b) : p.next a = b := by
  by_contra hne
  simp [pairedFlow, ha, hne] at hpos

theorem positive_departure_prev (p : Pairing C depot) (b : C)
    (hpos : 0 < pairedFlow p depot b) : b ≠ depot ∧ p.prev b = depot := by
  by_contra hne
  simp [pairedFlow, hne] at hpos

/-- This is an independently checkable cycle-exclusion certificate. -/
def DescendingRank (p : Pairing C depot) (rank : C → ℕ) : Prop :=
  ∀ c, c ≠ depot → rank (p.next c) < rank c

/-- A minimum-rank member of a depot-free set must have its successor outside. -/
theorem rank_gives_exit
    (p : Pairing C depot) (rank : C → ℕ) (hrank : DescendingRank p rank)
    (S : Finset C) (hne : S.Nonempty) (hdepot : depot ∉ S) :
    ∃ c ∈ S, p.next c ∉ S := by
  classical
  have hex : ∃ n : ℕ, ∃ c ∈ S, rank c = n := by
    obtain ⟨c, hc⟩ := hne
    exact ⟨rank c, c, hc, rfl⟩
  obtain ⟨c, hc, hvalue⟩ := Nat.find_spec hex
  have hcdepot : c ≠ depot := by
    intro heq
    subst c
    exact hdepot hc
  refine ⟨c, hc, ?_⟩
  intro hnext
  have hmin : Nat.find hex ≤ rank (p.next c) :=
    Nat.find_min' hex ⟨p.next c, hnext, rfl⟩
  have hdrop := hrank c hcdepot
  omega

theorem rank_gives_positive_cuts
    (p : Pairing C depot) (rank : C → ℕ) (hrank : DescendingRank p rank)
    (S : Finset C) (hne : S.Nonempty) (hdepot : depot ∉ S) :
    1 ≤ outCutFlow S (pairedFlow p) := by
  obtain ⟨c, hc, hnext⟩ := rank_gives_exit p rank hrank S hne hdepot
  have hcdepot : c ≠ depot := by
    intro heq
    subst c
    exact hdepot hc
  have hedge := arc_le_outCutFlow S (pairedFlow p) hc hnext
  rw [next_edge_one p c hcdepot] at hedge
  exact hedge

theorem rank_gives_no_loops
    (p : Pairing C depot) (rank : C → ℕ) (hrank : DescendingRank p rank) :
    ∀ c, pairedFlow p c c = 0 := by
  intro c
  by_cases hc : c = depot
  · subst c
    simp [pairedFlow]
  · have hnext : p.next c ≠ c := by
      intro heq
      have h := hrank c hc
      rw [heq] at h
      exact (Nat.lt_irrefl _ h)
    simp [pairedFlow, hc, hnext]

/-- A local upper bound on remaining service along each successor chain.
No nonnegativity condition on value is needed for telescoping. -/
structure BudgetPotential (p : Pairing C depot) (fee : C → ℚ) (T : ℚ) where
  value : C → ℚ
  depot_zero : value depot = 0
  step : ∀ c, c ≠ depot → fee c + value (p.next c) ≤ value c
  start : ∀ c, c ≠ depot → p.prev c = depot → value c ≤ T

/-- Convert the existing count-based service definition to a list sum. -/
theorem weighted_counts_eq_list_sum (fee : C → ℚ) (l : List C) :
    (∑ c, fee c * (l.count c : ℚ)) = (l.map fee).sum := by
  induction l with
  | nil => simp
  | cons a tail ih =>
    have hterm (c : C) :
        fee c * ((a :: tail).count c : ℚ) =
          fee c * (tail.count c : ℚ) + if c = a then fee a else 0 := by
      by_cases hca : c = a
      · subst c
        simp [List.count_cons, Nat.cast_add, mul_add, add_comm]
      · simp [List.count_cons, hca, Ne.symm hca]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ih]
    simp [List.map_cons, List.sum_cons, add_comm]

theorem route_service_eq_list_sum (fee : C → ℚ) (r : LegalRoute depot) :
    routeServiceIn r Finset.univ fee = (r.visits.map fee).sum := by
  exact weighted_counts_eq_list_sum fee r.visits

/-- Telescoping along any finite supported suffix ending at the depot. -/
theorem suffix_work_le
    (p : Pairing C depot) (fee : C → ℚ) (T : ℚ)
    (cert : BudgetPotential p fee T) (tail : List C) :
    ∀ a, depot ∉ a :: tail →
      ((a :: tail) ++ [depot]).IsChain (fun u v => 0 < pairedFlow p u v) →
      ((a :: tail).map fee).sum ≤ cert.value a := by
  induction tail with
  | nil =>
    intro a hdepot hchain
    have ha : a ≠ depot := by
      intro heq
      subst a
      simp at hdepot
    have hedge := (List.isChain_cons_cons.mp hchain).1
    have hnext := positive_task_edge_next p a depot ha hedge
    have hstep := cert.step a ha
    rw [hnext, cert.depot_zero] at hstep
    simpa using hstep
  | cons b tail ih =>
    intro a hdepot hchain
    have ha : a ≠ depot := by
      intro heq
      subst a
      simp at hdepot
    have htail : depot ∉ b :: tail := by
      intro hm
      exact hdepot (List.mem_cons_of_mem a hm)
    obtain ⟨hedge, hrest⟩ := List.isChain_cons_cons.mp hchain
    have hnext := positive_task_edge_next p a b ha hedge
    have hcost := ih b htail hrest
    have hstep := cert.step a ha
    rw [hnext] at hstep
    have htotal :
        fee a + ((b :: tail).map fee).sum ≤ cert.value a := by
      linarith only [hcost, hstep]
    simpa only [List.map_cons, List.sum_cons] using htotal

theorem supported_route_budget
    (p : Pairing C depot) (fee : C → ℚ) (T : ℚ)
    (cert : BudgetPotential p fee T) (r : LegalRoute depot)
    (hsupport : r.vertices.IsChain (fun u v => 0 < pairedFlow p u v)) :
    routeServiceIn r Finset.univ fee ≤ T := by
  cases hlist : r.visits with
  | nil => exact (r.visits_nonempty hlist).elim
  | cons a tail =>
    have hchain : (depot :: a :: (tail ++ [depot])).IsChain
        (fun u v => 0 < pairedFlow p u v) := by
      simpa [LegalRoute.vertices, depotRoute, hlist] using hsupport
    obtain ⟨hstart, hrest⟩ := List.isChain_cons_cons.mp hchain
    have hprev := positive_departure_prev p a hstart
    have hdepot : depot ∉ a :: tail := by
      simpa only [hlist] using r.depot_not_mem
    have hcost := suffix_work_le p fee T cert tail a hdepot hrest
    have hbudget := cert.start a hprev.1 hprev.2
    rw [route_service_eq_list_sum, hlist]
    exact hcost.trans hbudget

/-- All capacity cuts are DERIVED from the local certificates, not assumed. -/
theorem pairing_potential_gives_rounded_cuts
    (p : Pairing C depot) (rank : C → ℕ) (hrank : DescendingRank p rank)
    (fee : C → ℚ) (T : ℚ) (hfee : ∀ c, 0 ≤ fee c) (hT : 0 < T)
    (cert : BudgetPotential p fee T) :
    ∀ S : Finset C, depot ∉ S →
      Int.ceil ((∑ c ∈ S, fee c) / T) ≤ (outCutFlow S (pairedFlow p) : ℤ) := by
  classical
  obtain ⟨routes, _hnodup, hcounts, hexact, _hcard⟩ :=
    SingleVisitDecomposition.exists_exact_singleVisit_decomposition
      (pairedFlow p) depot (paired_out_one p) (paired_in_one p)
      (rank_gives_positive_cuts p rank hrank) (rank_gives_no_loops p rank hrank)
  have hsupport := exact_family_supported depot routes (pairedFlow p) hexact
  have hbudget : ∀ d, routeServiceIn (routes d) Finset.univ fee ≤ T := by
    intro d
    exact supported_route_budget p fee T cert (routes d) (hsupport d)
  exact SingleVisitDecomposition.rounded_service_cuts_of_exact_family
    (pairedFlow p) depot routes fee T hfee hT hcounts hexact hbudget

end Generic

section PhysicalProjection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Local pairing plus rank and exact projection reconstruct a structural lift. -/
theorem structural_lift_of_pairing
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (p : Pairing (VisitCopy depot required) none)
    (rank : VisitCopy depot required → ℕ) (hrank : DescendingRank p rank)
    (hproject : ∀ u v, projectFlow (project depot required) (pairedFlow p) u v = x u v) :
    IsStructuralCopyLift depot required x (pairedFlow p) := by
  exact {
    project_exact := hproject
    out_one := paired_out_one p
    in_one := paired_in_one p
    positive_cuts := rank_gives_positive_cuts p rank hrank
  }

/-- Add local cost certificates to obtain the existing full service-lift predicate. -/
theorem service_lift_of_pairing_potential
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (p : Pairing (VisitCopy depot required) none)
    (rank : VisitCopy depot required → ℕ) (hrank : DescendingRank p rank)
    (hproject : ∀ u v, projectFlow (project depot required) (pairedFlow p) u v = x u v)
    (service : V → ℚ) (T : ℚ) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T)
    (cert : BudgetPotential p (copyService depot required service) T) :
    IsServiceCopyLift depot required x service T (pairedFlow p) := by
  refine {
    project_exact := hproject
    out_one := paired_out_one p
    in_one := paired_in_one p
    positive_cuts := rank_gives_positive_cuts p rank hrank
    rounded_cuts := ?_
  }
  intro S _hne hdepot
  exact pairing_potential_gives_rounded_cuts p rank hrank
    (copyService depot required service) T
    (copyService_nonneg depot required service hservice) hT cert S hdepot

/-- The local certificate also implies all existing bounded profile cuts. -/
theorem bounded_profile_cuts_of_pairing_potential
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (p : Pairing (VisitCopy depot required) none)
    (rank : VisitCopy depot required → ℕ) (hrank : DescendingRank p rank)
    (hproject : ∀ u v, projectFlow (project depot required) (pairedFlow p) u v = x u v)
    (service : V → ℚ) (T : ℚ) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T)
    (cert : BudgetPotential p (copyService depot required service) T) :
    AllBoundedProfileCuts depot required (pairedFlow p) service T := by
  exact ((serviceCopyLift_iff_structural_bounded_profile_cuts
    depot required x (pairedFlow p) service T).mp
      (service_lift_of_pairing_potential depot required x p rank hrank
        hproject service T hservice hT cert)).2

/-- Main sufficient-condition theorem. The physical route family is a conclusion. -/
theorem exact_decomposition_of_pairing_potential
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (hloop : ∀ v, x v v = 0)
    (p : Pairing (VisitCopy depot required) none)
    (rank : VisitCopy depot required → ℕ) (hrank : DescendingRank p rank)
    (hproject : ∀ u v, projectFlow (project depot required) (pairedFlow p) u v = x u v)
    (service : V → ℚ) (T : ℚ) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T)
    (cert : BudgetPotential p (copyService depot required service) T) :
    ∃ routes : Fin (outFlow Finset.univ x depot) → LegalRoute depot,
      (∀ v, v ≠ depot → totalVisitCount Finset.univ routes v = required v) ∧
      (∀ u v, totalRouteFlow Finset.univ routes u v = x u v) ∧
      (∀ r, routeServiceIn (routes r) Finset.univ service ≤ T) := by
  apply (serviceCopyLift_iff_exact_decomposition
    depot required x hloop service T hservice hT).mp
  exact ⟨pairedFlow p, service_lift_of_pairing_potential depot required x p
    rank hrank hproject service T hservice hT cert⟩

end PhysicalProjection

namespace Examples

abbrev Node := Fin 3

/-- A supported path 0 -> 1 -> 2 -> 0. -/
def pathPairing : Pairing Node 0 where
  next := ![0, 2, 0]
  prev := ![0, 0, 1]
  prev_next := by decide +kernel
  next_prev := by decide +kernel

def pathRank : Node → ℕ := ![0, 2, 1]
def unitFees : Node → ℚ := ![0, 1, 1]

theorem path_rank_valid : DescendingRank pathPairing pathRank := by
  unfold DescendingRank
  decide +kernel

def pathBudget : BudgetPotential pathPairing unitFees 2 where
  value := ![0, 2, 1]
  depot_zero := by decide +kernel
  step := by decide +kernel
  start := by decide +kernel

theorem path_all_capacity_cuts :
    ∀ S : Finset Node, (0 : Node) ∉ S →
      Int.ceil ((∑ c ∈ S, unitFees c) / (2 : ℚ)) ≤
        (outCutFlow S (pairedFlow pathPairing) : ℤ) := by
  exact pairing_potential_gives_rounded_cuts pathPairing pathRank path_rank_valid
    unitFees 2 (by decide +kernel) (by norm_num) pathBudget

/-- Mutual local pairing alone allows an isolated task cycle 1 <-> 2. -/
def cyclePairing : Pairing Node 0 where
  next := ![0, 2, 1]
  prev := ![0, 2, 1]
  prev_next := by decide +kernel
  next_prev := by decide +kernel

theorem cycle_has_no_descending_rank :
    ¬ ∃ rank : Node → ℕ, DescendingRank cyclePairing rank := by
  rintro ⟨rank, hrank⟩
  have h1 := hrank 1 (by decide)
  have h2 := hrank 2 (by decide)
  change rank 2 < rank 1 at h1
  change rank 1 < rank 2 at h2
  omega

/-- Cycle exclusion alone cannot fit a cost-2 path into budget 1. -/
theorem path_has_no_budget_one_potential :
    ¬ Nonempty (BudgetPotential pathPairing unitFees 1) := by
  rintro ⟨cert⟩
  have h0 := cert.depot_zero
  have h1 := cert.step 1 (by decide)
  have h2 := cert.step 2 (by decide)
  have hs := cert.start 1 (by decide) (by decide +kernel)
  change 1 + cert.value 2 ≤ cert.value 1 at h1
  change 1 + cert.value 0 ≤ cert.value 2 at h2
  linarith only [h0, h1, h2, hs]

end Examples

end UAVProof.LocalVisitPairing

#print axioms UAVProof.LocalVisitPairing.next_prev_iff
#print axioms UAVProof.LocalVisitPairing.flow_to_task
#print axioms UAVProof.LocalVisitPairing.paired_out_one
#print axioms UAVProof.LocalVisitPairing.paired_in_one
#print axioms UAVProof.LocalVisitPairing.rank_gives_exit
#print axioms UAVProof.LocalVisitPairing.rank_gives_positive_cuts
#print axioms UAVProof.LocalVisitPairing.rank_gives_no_loops
#print axioms UAVProof.LocalVisitPairing.weighted_counts_eq_list_sum
#print axioms UAVProof.LocalVisitPairing.suffix_work_le
#print axioms UAVProof.LocalVisitPairing.supported_route_budget
#print axioms UAVProof.LocalVisitPairing.pairing_potential_gives_rounded_cuts
#print axioms UAVProof.LocalVisitPairing.structural_lift_of_pairing
#print axioms UAVProof.LocalVisitPairing.service_lift_of_pairing_potential
#print axioms UAVProof.LocalVisitPairing.bounded_profile_cuts_of_pairing_potential
#print axioms UAVProof.LocalVisitPairing.exact_decomposition_of_pairing_potential
#print axioms UAVProof.LocalVisitPairing.Examples.path_rank_valid
#print axioms UAVProof.LocalVisitPairing.Examples.path_all_capacity_cuts
#print axioms UAVProof.LocalVisitPairing.Examples.cycle_has_no_descending_rank
#print axioms UAVProof.LocalVisitPairing.Examples.path_has_no_budget_one_potential
