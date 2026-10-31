import LeanCompletion.UAV.LocalVisitPairingBoundedCertificate
import LeanCompletion.UAV.LocalVisitPairingPotentialGrid

/-!
# Finite candidate data for complete next-only certificates

The input fixes the denominator D and both range bounds. Candidates contain
only successor, finite rank and finite scaled-potential functions. Validity is
a separate proposition about those exact fields, with an explicit 0 ≤ T guard.
This guard rejects negative budgets even when floor(D*T).toNat truncates to zero.

Soundness decodes a candidate into one bounded certificate. Completeness uses
the canonical pairing, rank and suffix potential of exact feasible routes,
with the fixed input denominator; arbitrary bounded potentials are not assumed
to lie on that grid. Empty tasks, zero fees and repeated visits are allowed.

The Fintype instance establishes mathematical finiteness of the actual data.
Classical reconstruction is not an executable checker or search procedure.
No encoding-length or complexity bound, or preservation of an input next
function, is claimed.
-/

namespace UAVProof.LocalVisitPairingFiniteCertificate

open ResourceCuts VisitCopyLift SupportExactFeasibility
open LocalVisitPairing LocalVisitPairingCompleteness LocalVisitPairingNext
open LocalVisitPairingNextCertificate LocalVisitPairingBounds
open LocalVisitPairingBoundedCertificate LocalVisitPairingPotentialGrid

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Natural range bound determined by the inputs, even for invalid negative budgets. -/
def gridBound (service : V → ℚ) (T : ℚ) : ℕ :=
  (Int.floor ((serviceDenominator service : ℚ) * T)).toNat

omit [DecidableEq V] in
theorem denominator_rat_pos (service : V → ℚ) : (0 : ℚ) < serviceDenominator service := by
  exact_mod_cast serviceDenominator_pos service

omit [DecidableEq V] in
theorem scaled_budget_floor_nonneg (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
    0 ≤ Int.floor ((serviceDenominator service : ℚ) * T) := by
  apply Int.le_floor.mpr
  simpa only [Int.cast_zero] using mul_nonneg (denominator_rat_pos service).le hT

omit [DecidableEq V] in
theorem gridBound_cast (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
    (gridBound service T : ℤ) = Int.floor ((serviceDenominator service : ℚ) * T) :=
  Int.toNat_of_nonneg (scaled_budget_floor_nonneg service T hT)

/-- Pure candidate data: no prev, rational potential, route family, or proof fields.
The denominator is fixed by service and is not a candidate field. -/
structure FiniteCandidate (depot : V) (required : V → ℕ) (service : V → ℚ) (T : ℚ) where
  next : VisitCopy depot required → VisitCopy depot required
  rank : VisitCopy depot required → Fin (totalVisits depot required + 1)
  potential : VisitCopy depot required → Fin (gridBound service T + 1)

/-- A product of finite function spaces enumerates exactly the candidate fields.
This classical instance does not claim an executable validation algorithm. -/
noncomputable instance finiteCandidateFintype
    (depot : V) (required : V → ℕ) (service : V → ℚ) (T : ℚ) :
    Fintype (FiniteCandidate depot required service T) := by
  classical
  exact Fintype.ofEquiv
    ((VisitCopy depot required → VisitCopy depot required) ×
      (VisitCopy depot required → Fin (totalVisits depot required + 1)) ×
      (VisitCopy depot required → Fin (gridBound service T + 1)))
    { toFun := fun f => ⟨f.1, f.2.1, f.2.2⟩
      invFun := fun code => (code.next, code.rank, code.potential)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Decode the grid numerator using the positive input denominator. -/
def decodedPotential {depot : V} {required : V → ℕ} {service : V → ℚ} {T : ℚ}
    (code : FiniteCandidate depot required service T) (c : VisitCopy depot required) : ℚ :=
  ((code.potential c).val : ℚ) / (serviceDenominator service : ℚ)

/-- The finite grid bounds yield the rational bounds when the budget is nonnegative. -/
theorem decodedPotential_bounds {depot : V} {required : V → ℕ} {service : V → ℚ} {T : ℚ}
    (code : FiniteCandidate depot required service T) (hT : 0 ≤ T)
    (c : VisitCopy depot required) :
    0 ≤ decodedPotential code c ∧ decodedPotential code c ≤ T := by
  have hD := denominator_rat_pos service
  have hk : (code.potential c).val ≤ gridBound service T :=
    Nat.le_of_lt_succ (code.potential c).isLt
  have hkz : ((code.potential c).val : ℤ) ≤
      Int.floor ((serviceDenominator service : ℚ) * T) := by
    rw [← gridBound_cast service T hT]
    exact_mod_cast hk
  have hkq : ((code.potential c).val : ℚ) ≤ (serviceDenominator service : ℚ) * T := by
    simpa only [Int.cast_natCast] using Int.le_floor.mp hkz
  refine ⟨div_nonneg (Nat.cast_nonneg _) hD.le, ?_⟩
  apply (div_le_iff₀ hD).2
  simpa only [mul_comm] using hkq

/-- Validity checks the very same candidate fields. Budget inequalities use
the decoded potential; the projection uses the pairing recovered from next. -/
structure ValidFiniteCertificate (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ) (code : FiniteCandidate depot required service T) : Prop where
  budget_nonneg : 0 ≤ T
  predecessor_unique : ∀ a b, a ≠ none → b ≠ none →
    code.next a = code.next b → code.next a ≠ none → a = b
  rank_zero : (code.rank none).val = 0
  rank_descending : ∀ c, c ≠ none → (code.rank (code.next c)).val < (code.rank c).val
  rank_positive : ∀ c, c ≠ none → 1 ≤ (code.rank c).val
  potential_zero : (code.potential none).val = 0
  step : ∀ c, c ≠ none → copyService depot required service c +
    decodedPotential code (code.next c) ≤ decodedPotential code c
  start : ∀ c, c ≠ none → (¬ ∃ a, a ≠ none ∧ code.next a = c) →
    decodedPotential code c ≤ T
  project_exact : ∀ u v, projectFlow (project depot required)
    (pairedFlow (toPairing ⟨code.next, predecessor_unique⟩)) u v = x u v

namespace ValidFiniteCertificate

variable {depot : V} {required : V → ℕ} {x : V → V → ℕ} {service : V → ℚ} {T : ℚ}
variable {code : FiniteCandidate depot required service T}

def toNextPairing (h : ValidFiniteCertificate depot required x service T code) :
    NextPairing (VisitCopy depot required) none := ⟨code.next, h.predecessor_unique⟩

def toBudgetPotential (h : ValidFiniteCertificate depot required x service T code) :
    NextBudgetPotential h.toNextPairing (copyService depot required service) T where
  value := decodedPotential code
  depot_zero := by simp [decodedPotential, h.potential_zero]
  step := h.step
  start := h.start

end ValidFiniteCertificate

/-- Soundness needs no service-sign or physical no-loop hypothesis. -/
theorem hasBoundedNextCertificate_of_valid
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (service : V → ℚ) (T : ℚ)
    (code : FiniteCandidate depot required service T)
    (h : ValidFiniteCertificate depot required x service T code) :
    HasBoundedNextCertificate depot required x service T := by
  refine ⟨h.toNextPairing, fun c => (code.rank c).val, h.toBudgetPotential,
    h.rank_descending, h.project_exact, h.rank_zero, ?_, ?_⟩
  · intro c hc
    exact ⟨h.rank_positive c hc, Nat.le_of_lt_succ (code.rank c).isLt⟩
  · exact decodedPotential_bounds code h.budget_nonneg

/-- Completeness chooses the canonical route witnesses and the fixed service
denominator. It does not infer grid integrality of an arbitrary budget potential. -/
theorem exists_validFiniteCertificate_of_exactFeasible
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (m : ℕ)
    (service : V → ℚ) (T : ℚ) (hservice : ∀ v, 0 ≤ service v) (hT : 0 ≤ T)
    (h : ExactFeasible depot x required m service T) :
    ∃ code : FiniteCandidate depot required service T,
      ValidFiniteCertificate depot required x service T code := by
  classical
  obtain ⟨routes, hcover, hbudget, hexact⟩ := h
  have hrange : ∀ c, routeRank depot required routes hcover c ≤ totalVisits depot required := by
    intro c
    by_cases hc : c = none
    · subst c
      simp
    · exact (routeRank_task_bounds depot required routes hcover c hc).2
  have hgrid : ∀ c : VisitCopy depot required, ∃ k : ℕ,
      (k : ℚ) = (serviceDenominator service : ℚ) *
        routePotential depot required routes hcover service c ∧ k ≤ gridBound service T := by
    intro c
    obtain ⟨k, hk, hkbound⟩ := routePotential_nat_grid_bounds depot required routes hcover
      service hservice T hT hbudget (serviceDenominator service)
      (serviceDenominator_pos service) (serviceDenominator_integral service) c
    refine ⟨k, hk, ?_⟩
    rw [← gridBound_cast service T hT] at hkbound
    exact_mod_cast hkbound
  choose k hk hkle using hgrid
  let code : FiniteCandidate depot required service T := {
    next := (pairingOfRoutes depot required routes hcover).next
    rank := fun c => ⟨routeRank depot required routes hcover c, Nat.lt_succ_of_le (hrange c)⟩
    potential := fun c => ⟨k c, Nat.lt_succ_of_le (hkle c)⟩
  }
  have hdecode : ∀ c, decodedPotential code c =
      routePotential depot required routes hcover service c := by
    intro c
    change (k c : ℚ) / (serviceDenominator service : ℚ) = _
    apply (div_eq_iff (ne_of_gt (denominator_rat_pos service))).2
    rw [hk c, mul_comm]
  refine ⟨code, {
    budget_nonneg := hT
    predecessor_unique :=
      pairing_task_predecessor_unique (pairingOfRoutes depot required routes hcover)
    rank_zero := rfl
    rank_descending := routeRank_descending depot required routes hcover
    rank_positive := fun c hc => (routeRank_task_bounds depot required routes hcover c hc).1
    potential_zero := ?_
    step := ?_
    start := ?_
    project_exact := ?_
  }⟩
  · change k none = 0
    have hz : (k none : ℚ) = 0 := by simpa only [routePotential_none, mul_zero] using hk none
    exact_mod_cast hz
  · intro c hc
    rw [hdecode c, hdecode (code.next c)]
    exact (routePotential_isBudgetPotential
      depot required routes hcover service T hbudget).step c hc
  · intro c hc hs
    rw [hdecode c]
    exact (budgetOfPairingToNext
      (routePotential_isBudgetPotential
        depot required routes hcover service T hbudget)).start c hc hs
  · change ∀ u v, projectFlow (project depot required)
      (pairedFlow (toPairing (ofPairing
        (pairingOfRoutes depot required routes hcover)))) u v = x u v
    rw [pairedFlow_toPairing_ofPairing]
    exact pairingOfRoutes_projects_exact depot required routes hcover x hexact

/-- Canonical-count feasibility is exactly existence of a valid finite candidate. -/
theorem exactFeasible_iff_exists_validFiniteCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ)
    (hloop : ∀ v, x v v = 0) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T) :
    ExactFeasible depot x required (outFlow Finset.univ x depot) service T ↔
      ∃ code : FiniteCandidate depot required service T,
        ValidFiniteCertificate depot required x service T code := by
  constructor
  · exact exists_validFiniteCertificate_of_exactFeasible depot required x _ service T hservice hT.le
  · rintro ⟨code, hc⟩
    exact (exactFeasible_iff_hasBoundedNextCertificate
      depot required x service T hloop hservice hT).2
      (hasBoundedNextCertificate_of_valid depot required x service T code hc)

/-- Fixed-count feasibility retains the necessary depot-outflow equality. -/
theorem exactFeasible_iff_count_and_exists_validFiniteCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (m : ℕ)
    (service : V → ℚ) (T : ℚ)
    (hloop : ∀ v, x v v = 0) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T) :
    ExactFeasible depot x required m service T ↔
      m = outFlow Finset.univ x depot ∧
        ∃ code : FiniteCandidate depot required service T,
          ValidFiniteCertificate depot required x service T code := by
  constructor
  · intro h
    have hcount := (exactFeasible_iff_count_and_hasBoundedNextCertificate
      depot required x m service T hloop hservice hT).1 h
    exact ⟨hcount.1,
      exists_validFiniteCertificate_of_exactFeasible depot required x m service T hservice hT.le h⟩
  · rintro ⟨hcount, code, hc⟩
    exact (exactFeasible_iff_count_and_hasBoundedNextCertificate
      depot required x m service T hloop hservice hT).2
      ⟨hcount, hasBoundedNextCertificate_of_valid depot required x service T code hc⟩

/-- The explicit guard prevents acceptance of negative budgets, even after truncation. -/
theorem no_validFiniteCertificate_of_negative_budget
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (service : V → ℚ) (T : ℚ)
    (hT : T < 0) :
    ¬ ∃ code : FiniteCandidate depot required service T,
      ValidFiniteCertificate depot required x service T code := by
  rintro ⟨code, hc⟩
  exact (not_le_of_gt hT) hc.budget_nonneg

/-- With no tasks, constant-zero data are valid for arbitrary service fees exactly
when the budget is nonnegative. This is not a general feasibility theorem at T = 0. -/
theorem zero_exists_validFiniteCertificate_iff (depot : V) (service : V → ℚ) (T : ℚ) :
    (∃ code : FiniteCandidate depot (fun _ => 0) service T,
      ValidFiniteCertificate depot (fun _ => 0) (fun _ _ => 0) service T code) ↔ 0 ≤ T := by
  constructor
  · rintro ⟨code, hc⟩
    exact hc.budget_nonneg
  · intro hT
    have hcopy : ∀ c : VisitCopy depot (fun _ => 0), c = none := by
      intro c
      cases c with
      | none => rfl
      | some c => exact Fin.elim0 c.2
    let code : FiniteCandidate depot (fun _ => 0) service T := {
      next := fun _ => none
      rank := fun _ => 0
      potential := fun _ => 0
    }
    refine ⟨code, {
      budget_nonneg := hT
      predecessor_unique := fun _ _ _ _ _ hn => (hn rfl).elim
      rank_zero := rfl
      rank_descending := fun c hc => (hc (hcopy c)).elim
      rank_positive := fun c hc => (hc (hcopy c)).elim
      potential_zero := rfl
      step := fun c hc => (hc (hcopy c)).elim
      start := fun c hc => (hc (hcopy c)).elim
      project_exact := ?_
    }⟩
    intro u v
    have hflow (q : NextPairing (VisitCopy depot (fun _ => 0)) none) :
        pairedFlow (toPairing q) = fun _ _ => 0 := by
      funext a b
      rw [hcopy a, hcopy b]
      simp [pairedFlow]
    rw [hflow]
    simp [projectFlow]

end UAVProof.LocalVisitPairingFiniteCertificate

#print UAVProof.LocalVisitPairingFiniteCertificate.FiniteCandidate
#print UAVProof.LocalVisitPairingFiniteCertificate.ValidFiniteCertificate
#check UAVProof.LocalVisitPairingFiniteCertificate.gridBound_cast
#check UAVProof.LocalVisitPairingFiniteCertificate.finiteCandidateFintype
#check UAVProof.LocalVisitPairingFiniteCertificate.decodedPotential_bounds
#check UAVProof.LocalVisitPairingFiniteCertificate.hasBoundedNextCertificate_of_valid
#check UAVProof.LocalVisitPairingFiniteCertificate.exists_validFiniteCertificate_of_exactFeasible
#check UAVProof.LocalVisitPairingFiniteCertificate.exactFeasible_iff_exists_validFiniteCertificate
open UAVProof.LocalVisitPairingFiniteCertificate in
#check exactFeasible_iff_count_and_exists_validFiniteCertificate
#check UAVProof.LocalVisitPairingFiniteCertificate.no_validFiniteCertificate_of_negative_budget
#check UAVProof.LocalVisitPairingFiniteCertificate.zero_exists_validFiniteCertificate_iff

#print axioms UAVProof.LocalVisitPairingFiniteCertificate.scaled_budget_floor_nonneg
#print axioms UAVProof.LocalVisitPairingFiniteCertificate.gridBound_cast
#print axioms UAVProof.LocalVisitPairingFiniteCertificate.finiteCandidateFintype
#print axioms UAVProof.LocalVisitPairingFiniteCertificate.decodedPotential_bounds
#print axioms UAVProof.LocalVisitPairingFiniteCertificate.ValidFiniteCertificate.toBudgetPotential
#print axioms UAVProof.LocalVisitPairingFiniteCertificate.hasBoundedNextCertificate_of_valid
#print axioms
  UAVProof.LocalVisitPairingFiniteCertificate.exists_validFiniteCertificate_of_exactFeasible
#print axioms
  UAVProof.LocalVisitPairingFiniteCertificate.exactFeasible_iff_exists_validFiniteCertificate
open UAVProof.LocalVisitPairingFiniteCertificate in
#print axioms exactFeasible_iff_count_and_exists_validFiniteCertificate
#print axioms
  UAVProof.LocalVisitPairingFiniteCertificate.no_validFiniteCertificate_of_negative_budget
#print axioms UAVProof.LocalVisitPairingFiniteCertificate.zero_exists_validFiniteCertificate_iff
