import LeanCompletion.UAV.LocalVisitPairingBounds
import LeanCompletion.UAV.LocalVisitPairingNextCertificate

/-!
# Complete next-only certificates with bounded numerical values

One successor pairing, one rank, and one budget potential jointly witness all
certificate conditions and all bounds. No predecessor data is stored.
Exact feasible routes yield the specific canonical rank and suffix potential
already bounded in LocalVisitPairingBounds.

Forgetting bounds has no sign or no-loop assumptions. Construction from routes
uses nonnegative service fees and a nonnegative budget, without a physical
no-loop assumption. The final equivalences retain the existing no-loop and
strictly positive budget hypotheses, as well as the fixed-fleet count condition.

Existence of bounded witnesses does not promise to preserve an input
certificate's next function. These are numerical bounds, not rational encoding
bit bounds or an executable search procedure. The depot demand is unrestricted;
empty families, zero fees, and nonadjacent repeated visits remain allowed.
-/

namespace UAVProof.LocalVisitPairingBoundedCertificate

open ResourceCuts VisitCopyLift SupportExactFeasibility
open LocalVisitPairing LocalVisitPairingCompleteness LocalVisitPairingNext
open LocalVisitPairingNextCertificate LocalVisitPairingBounds

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All bounds concern the same witnesses as the local consistency, rank,
projection, and budget conditions. The potential's depot-zero field is reused. -/
def HasBoundedNextCertificate (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ) : Prop :=
  ∃ (q : NextPairing (VisitCopy depot required) none)
    (rank : VisitCopy depot required → ℕ)
    (cert : NextBudgetPotential q (copyService depot required service) T),
    NextDescendingRank q rank ∧
    (∀ u v, projectFlow (project depot required) (pairedFlow (toPairing q)) u v = x u v) ∧
    rank none = 0 ∧
    (∀ c, c ≠ none → 1 ≤ rank c ∧ rank c ≤ totalVisits depot required) ∧
    (∀ c, 0 ≤ cert.value c ∧ cert.value c ≤ T)

/-- Dropping only the range conditions needs no additional assumptions. -/
theorem hasNextCertificate_of_hasBoundedNextCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (service : V → ℚ) (T : ℚ)
    (h : HasBoundedNextCertificate depot required x service T) :
    HasNextCertificate depot required x service T := by
  obtain ⟨q, rank, cert, hrank, hproject, _⟩ := h
  exact ⟨q, rank, hrank, hproject, ⟨cert⟩⟩

/-- The all-copy potential bound includes the depot, even if there are no tasks. -/
theorem budget_nonneg_of_hasBoundedNextCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (service : V → ℚ) (T : ℚ)
    (h : HasBoundedNextCertificate depot required x service T) : 0 ≤ T := by
  obtain ⟨_, _, cert, _, _, _, _, hvalue⟩ := h
  have hdepot := (hvalue none).2
  rw [cert.depot_zero] at hdepot
  exact hdepot

/-- Explicitly select the canonical witnesses of the supplied feasible routes.
The potential conversion preserves exactly the suffix values used by the bounds.
Only 0 ≤ T is needed here; no physical no-loop assumption is added. -/
theorem hasBoundedNextCertificate_of_exactFeasible
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (m : ℕ)
    (service : V → ℚ) (T : ℚ) (hservice : ∀ v, 0 ≤ service v) (hT : 0 ≤ T)
    (h : ExactFeasible depot x required m service T) :
    HasBoundedNextCertificate depot required x service T := by
  obtain ⟨routes, hcover, hbudget, hexact⟩ := h
  refine ⟨ofPairing (pairingOfRoutes depot required routes hcover),
    routeRank depot required routes hcover,
    budgetOfPairingToNext
      (routePotential_isBudgetPotential depot required routes hcover service T hbudget),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (nextDescendingRank_ofPairing_iff _ _).2
      (routeRank_descending depot required routes hcover)
  · rw [pairedFlow_toPairing_ofPairing]
    exact pairingOfRoutes_projects_exact depot required routes hcover x hexact
  · exact routeRank_depot_zero depot required routes hcover
  · exact routeRank_task_bounds depot required routes hcover
  · intro c
    rw [budgetOfPairingToNext_value]
    exact routePotential_bounds depot required routes hcover service hservice T hT hbudget c

/-- Under the existing feasibility hypotheses, bounds do not restrict certificate
existence. Reconstruction may choose a different successor function. -/
theorem hasBoundedNextCertificate_iff_hasNextCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ)
    (hloop : ∀ v, x v v = 0) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T) :
    HasBoundedNextCertificate depot required x service T ↔
      HasNextCertificate depot required x service T := by
  constructor
  · exact hasNextCertificate_of_hasBoundedNextCertificate depot required x service T
  · intro h
    exact hasBoundedNextCertificate_of_exactFeasible depot required x _ service T hservice hT.le
      ((exactFeasible_iff_hasNextCertificate depot required x service T hloop hservice hT).2 h)

/-- Bounded certificates characterize feasibility at the canonical fleet size. -/
theorem exactFeasible_iff_hasBoundedNextCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ)
    (hloop : ∀ v, x v v = 0) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T) :
    ExactFeasible depot x required (outFlow Finset.univ x depot) service T ↔
      HasBoundedNextCertificate depot required x service T :=
  (exactFeasible_iff_hasNextCertificate depot required x service T hloop hservice hT).trans
    (hasBoundedNextCertificate_iff_hasNextCertificate
      depot required x service T hloop hservice hT).symm

/-- The fixed-fleet theorem keeps the depot-outflow equality, including m = 0. -/
theorem exactFeasible_iff_count_and_hasBoundedNextCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (m : ℕ)
    (service : V → ℚ) (T : ℚ)
    (hloop : ∀ v, x v v = 0) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T) :
    ExactFeasible depot x required m service T ↔
      m = outFlow Finset.univ x depot ∧ HasBoundedNextCertificate depot required x service T := by
  rw [hasBoundedNextCertificate_iff_hasNextCertificate
    depot required x service T hloop hservice hT]
  exact exactFeasible_iff_count_and_hasNextCertificate depot required x m service T
    hloop hservice hT

/-- With zero demand there are no task copies. Constant zero rank and potential
work for any service function, provided the depot value fits the budget. -/
theorem zero_hasBoundedNextCertificate (depot : V) (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
    HasBoundedNextCertificate depot (fun _ => 0) (fun _ _ => 0) service T := by
  have hcopy : ∀ c : VisitCopy depot (fun _ => 0), c = none := by
    intro c
    cases c with
    | none => rfl
    | some c => exact Fin.elim0 c.2
  obtain ⟨q, _, _, hproject, _⟩ := zero_hasNextCertificate depot service T
  let cert : NextBudgetPotential q (copyService depot (fun _ => 0) service) T := {
    value := fun _ => 0
    depot_zero := rfl
    step := fun c hc => (hc (hcopy c)).elim
    start := fun c hc => (hc (hcopy c)).elim
  }
  refine ⟨q, fun _ => 0, cert, ?_, hproject, rfl, ?_, ?_⟩
  · intro c hc
    exact (hc (hcopy c)).elim
  · intro c hc
    exact (hc (hcopy c)).elim
  · intro c
    exact ⟨le_rfl, hT⟩

/-- Unlike the unbounded zero-instance certificate, this one cannot have T < 0.
This boundary statement does not extend the general feasibility iff to T = 0. -/
theorem zero_hasBoundedNextCertificate_iff (depot : V) (service : V → ℚ) (T : ℚ) :
    HasBoundedNextCertificate depot (fun _ => 0) (fun _ _ => 0) service T ↔ 0 ≤ T :=
  ⟨budget_nonneg_of_hasBoundedNextCertificate depot _ _ service T,
    zero_hasBoundedNextCertificate depot service T⟩

end UAVProof.LocalVisitPairingBoundedCertificate

#print UAVProof.LocalVisitPairingBoundedCertificate.HasBoundedNextCertificate
#check UAVProof.LocalVisitPairingBoundedCertificate.hasNextCertificate_of_hasBoundedNextCertificate
#check UAVProof.LocalVisitPairingBoundedCertificate.budget_nonneg_of_hasBoundedNextCertificate
#check UAVProof.LocalVisitPairingBoundedCertificate.hasBoundedNextCertificate_of_exactFeasible
#check UAVProof.LocalVisitPairingBoundedCertificate.hasBoundedNextCertificate_iff_hasNextCertificate
#check UAVProof.LocalVisitPairingBoundedCertificate.exactFeasible_iff_hasBoundedNextCertificate
#check
  UAVProof.LocalVisitPairingBoundedCertificate.exactFeasible_iff_count_and_hasBoundedNextCertificate
#check UAVProof.LocalVisitPairingBoundedCertificate.zero_hasBoundedNextCertificate
#check UAVProof.LocalVisitPairingBoundedCertificate.zero_hasBoundedNextCertificate_iff

#print axioms UAVProof.LocalVisitPairingBoundedCertificate.HasBoundedNextCertificate
#print axioms
  UAVProof.LocalVisitPairingBoundedCertificate.hasNextCertificate_of_hasBoundedNextCertificate
#print axioms
  UAVProof.LocalVisitPairingBoundedCertificate.budget_nonneg_of_hasBoundedNextCertificate
#print axioms
  UAVProof.LocalVisitPairingBoundedCertificate.hasBoundedNextCertificate_of_exactFeasible
#print axioms
  UAVProof.LocalVisitPairingBoundedCertificate.hasBoundedNextCertificate_iff_hasNextCertificate
#print axioms
  UAVProof.LocalVisitPairingBoundedCertificate.exactFeasible_iff_hasBoundedNextCertificate
#print axioms
  UAVProof.LocalVisitPairingBoundedCertificate.exactFeasible_iff_count_and_hasBoundedNextCertificate
#print axioms UAVProof.LocalVisitPairingBoundedCertificate.zero_hasBoundedNextCertificate
#print axioms UAVProof.LocalVisitPairingBoundedCertificate.zero_hasBoundedNextCertificate_iff
