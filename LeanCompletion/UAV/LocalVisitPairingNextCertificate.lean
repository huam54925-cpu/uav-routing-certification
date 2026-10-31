import LeanCompletion.UAV.LocalVisitPairingNext
import LeanCompletion.UAV.LocalVisitPairingCompleteness

/-!
# Complete next-only certificates

Predecessors are recovered, never supplied as additional certificate data.
Rank and service-potential conditions use the stored successor directly; a
route start is a task with no task predecessor. Potential conversions preserve
the entire value function, including its depot value.

The representation equivalence needs no sign, budget-positivity or physical
no-loop hypotheses. Only the final feasibility equivalences inherit those
hypotheses from the existing route-decomposition theorem. The fixed-fleet
version retains the depot-outflow equality, including the zero-route case.

Recovery remains classical and noncomputable. No rank/potential range bounds
or search algorithm are asserted. Predecessor uniqueness alone allows task
cycles; the separate strictly descending rank excludes them.
-/

namespace UAVProof.LocalVisitPairingNextCertificate

open LocalVisitPairing LocalVisitPairingNext LocalVisitPairingCompleteness
open ResourceCuts VisitCopyLift SupportExactFeasibility

section Generic

variable {C : Type*} {depot : C}

/-- A suffix-service bound stated entirely using successors. Neither the
potential nor fees must be nonnegative, and the step inequality is not strict. -/
structure NextBudgetPotential (q : NextPairing C depot) (fee : C → ℚ) (T : ℚ) where
  value : C → ℚ
  depot_zero : value depot = 0
  step : ∀ c, c ≠ depot → fee c + value (q.next c) ≤ value c
  start : ∀ c, c ≠ depot → (¬ ∃ a, a ≠ depot ∧ q.next a = c) → value c ≤ T

/-- Convert to the existing budget data on the recovered pairing. -/
def nextBudgetToBudget {q : NextPairing C depot} {fee : C → ℚ} {T : ℚ}
    (cert : NextBudgetPotential q fee T) : BudgetPotential (toPairing q) fee T where
  value := cert.value
  depot_zero := cert.depot_zero
  step := by
    intro c hc
    rw [toPairing_next_task q c hc]
    exact cert.step c hc
  start := by
    intro c hc hp
    exact cert.start c hc ((prevOfNext_eq_depot_iff q c hc).1 hp)

/-- Convert recovered-pairing budget data back to a successor-only condition. -/
def budgetToNextBudget {q : NextPairing C depot} {fee : C → ℚ} {T : ℚ}
    (cert : BudgetPotential (toPairing q) fee T) : NextBudgetPotential q fee T where
  value := cert.value
  depot_zero := cert.depot_zero
  step := by
    intro c hc
    simpa only [toPairing_next_task q c hc] using cert.step c hc
  start := by
    intro c hc hs
    exact cert.start c hc ((prevOfNext_eq_depot_iff q c hc).2 hs)

@[simp] theorem nextBudgetToBudget_value {q : NextPairing C depot} {fee : C → ℚ} {T : ℚ}
    (cert : NextBudgetPotential q fee T) : (nextBudgetToBudget cert).value = cert.value := rfl

@[simp] theorem budgetToNextBudget_value {q : NextPairing C depot} {fee : C → ℚ} {T : ℚ}
    (cert : BudgetPotential (toPairing q) fee T) :
    (budgetToNextBudget cert).value = cert.value := rfl

theorem nonempty_nextBudgetPotential_iff (q : NextPairing C depot) (fee : C → ℚ) (T : ℚ) :
    Nonempty (NextBudgetPotential q fee T) ↔ Nonempty (BudgetPotential (toPairing q) fee T) :=
  ⟨fun ⟨cert⟩ => ⟨nextBudgetToBudget cert⟩, fun ⟨cert⟩ => ⟨budgetToNextBudget cert⟩⟩

/-- An original pairing need not be normalized. Its task predecessors recover
exactly, so its original potential also gives next-only budget data. -/
def budgetOfPairingToNext {p : Pairing C depot} {fee : C → ℚ} {T : ℚ}
    (cert : BudgetPotential p fee T) : NextBudgetPotential (ofPairing p) fee T where
  value := cert.value
  depot_zero := cert.depot_zero
  step := cert.step
  start := by
    intro c hc hs
    apply cert.start c hc
    rw [← prevOfNext_ofPairing_task p c hc]
    exact (prevOfNext_eq_depot_iff (ofPairing p) c hc).2 hs

@[simp] theorem budgetOfPairingToNext_value {p : Pairing C depot} {fee : C → ℚ} {T : ℚ}
    (cert : BudgetPotential p fee T) : (budgetOfPairingToNext cert).value = cert.value := rfl

/-- Cycle exclusion directly on the stored successor; depot entries are ignored. -/
def NextDescendingRank (q : NextPairing C depot) (rank : C → ℕ) : Prop :=
  ∀ c, c ≠ depot → rank (q.next c) < rank c

theorem nextDescendingRank_iff (q : NextPairing C depot) (rank : C → ℕ) :
    NextDescendingRank q rank ↔ DescendingRank (toPairing q) rank := by
  constructor
  · intro h c hc
    rw [toPairing_next_task q c hc]
    exact h c hc
  · intro h c hc
    simpa only [toPairing_next_task q c hc] using h c hc

/-- Normalizing the depot during a round trip does not affect any rank step. -/
theorem descendingRank_roundtrip_iff (p : Pairing C depot) (rank : C → ℕ) :
    DescendingRank (toPairing (ofPairing p)) rank ↔ DescendingRank p rank := by
  constructor
  · intro h c hc
    simpa only [toPairing_ofPairing_next_task p c hc] using h c hc
  · intro h c hc
    rw [toPairing_ofPairing_next_task p c hc]
    exact h c hc

theorem nextDescendingRank_ofPairing_iff (p : Pairing C depot) (rank : C → ℕ) :
    NextDescendingRank (ofPairing p) rank ↔ DescendingRank p rank :=
  (nextDescendingRank_iff (ofPairing p) rank).trans (descendingRank_roundtrip_iff p rank)

end Generic

section Certificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Complete sparse certificate with no supplied predecessor data. The flow
used for exact projection is derived from next by classical reconstruction. -/
def HasNextCertificate (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ) : Prop :=
  ∃ (q : NextPairing (VisitCopy depot required) none) (rank : VisitCopy depot required → ℕ),
    NextDescendingRank q rank ∧
    (∀ u v, projectFlow (project depot required) (pairedFlow (toPairing q)) u v = x u v) ∧
    Nonempty (NextBudgetPotential q (copyService depot required service) T)

/-- Pure representation equivalence: no sign or physical no-loop assumptions.
Both directions retain the same rank and potential values, and every flow entry. -/
theorem hasNextCertificate_iff_hasLocalCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (service : V → ℚ) (T : ℚ) :
    HasNextCertificate depot required x service T ↔
      HasLocalCertificate depot required x service T := by
  constructor
  · rintro ⟨q, rank, hrank, hproject, ⟨cert⟩⟩
    exact ⟨toPairing q, rank, (nextDescendingRank_iff q rank).1 hrank,
      hproject, ⟨nextBudgetToBudget cert⟩⟩
  · rintro ⟨p, rank, hrank, hproject, ⟨cert⟩⟩
    refine ⟨ofPairing p, rank, (nextDescendingRank_ofPairing_iff p rank).2 hrank,
      ?_, ⟨budgetOfPairingToNext cert⟩⟩
    simpa only [pairedFlow_toPairing_ofPairing] using hproject

/-- Canonical fleet size: reuse the existing feasibility theorem unchanged. -/
theorem exactFeasible_iff_hasNextCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ)
    (hloop : ∀ v, x v v = 0) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T) :
    ExactFeasible depot x required (outFlow Finset.univ x depot) service T ↔
      HasNextCertificate depot required x service T :=
  (exactFeasible_iff_hasLocalCertificate depot required x service T hloop hservice hT).trans
    (hasNextCertificate_iff_hasLocalCertificate depot required x service T).symm

/-- Fixed fleet size retains exactly the depot-outflow condition. No positive
fleet size, nonempty task set, or distinct-route hypothesis is imposed. -/
theorem exactFeasible_iff_count_and_hasNextCertificate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (m : ℕ)
    (service : V → ℚ) (T : ℚ)
    (hloop : ∀ v, x v v = 0) (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T) :
    ExactFeasible depot x required m service T ↔
      m = outFlow Finset.univ x depot ∧ HasNextCertificate depot required x service T := by
  rw [hasNextCertificate_iff_hasLocalCertificate]
  exact exactFeasible_iff_count_and_hasLocalCertificate depot required x m service T
    hloop hservice hT

/-- Empty tasks and zero flow admit a complete next-only certificate for any
service function and any budget, even without the final theorem's sign assumptions. -/
theorem zero_hasNextCertificate (depot : V) (service : V → ℚ) (T : ℚ) :
    HasNextCertificate depot (fun _ => 0) (fun _ _ => 0) service T :=
  (hasNextCertificate_iff_hasLocalCertificate depot _ _ service T).2
    (zero_hasLocalCertificate depot service T)

end Certificate

namespace Examples

/-- Zero service on a task cycle satisfies all budget inequalities, including
with zero budget. Thus budget data must not silently serve as cycle exclusion. -/
def taskCycle_zero_budget :
    NextBudgetPotential LocalVisitPairingNext.Examples.taskCycle (fun _ => 0) 0 where
  value := fun _ => 0
  depot_zero := rfl
  step := by intros; simp
  start := by intros; exact le_rfl

/-- The allowed structural cycle cannot supply the rank of a full certificate. -/
theorem taskCycle_has_no_nextDescendingRank :
    ¬ ∃ rank : Fin 3 → ℕ,
      NextDescendingRank LocalVisitPairingNext.Examples.taskCycle rank := by
  rintro ⟨rank, hrank⟩
  exact LocalVisitPairingNext.Examples.taskCycle_has_no_descending_rank
    ⟨rank, (nextDescendingRank_iff _ rank).1 hrank⟩

end Examples

end UAVProof.LocalVisitPairingNextCertificate

#check UAVProof.LocalVisitPairingNextCertificate.NextBudgetPotential
#print UAVProof.LocalVisitPairingNextCertificate.NextBudgetPotential
#check UAVProof.LocalVisitPairingNextCertificate.nextBudgetToBudget
#check UAVProof.LocalVisitPairingNextCertificate.budgetToNextBudget
#check UAVProof.LocalVisitPairingNextCertificate.budgetOfPairingToNext
#check UAVProof.LocalVisitPairingNextCertificate.nonempty_nextBudgetPotential_iff
#check UAVProof.LocalVisitPairingNextCertificate.nextDescendingRank_iff
#check UAVProof.LocalVisitPairingNextCertificate.HasNextCertificate
#print UAVProof.LocalVisitPairingNextCertificate.HasNextCertificate
#check UAVProof.LocalVisitPairingNextCertificate.hasNextCertificate_iff_hasLocalCertificate
#check UAVProof.LocalVisitPairingNextCertificate.exactFeasible_iff_hasNextCertificate
#check UAVProof.LocalVisitPairingNextCertificate.exactFeasible_iff_count_and_hasNextCertificate
#check UAVProof.LocalVisitPairingNextCertificate.zero_hasNextCertificate

#print axioms UAVProof.LocalVisitPairingNextCertificate.nextBudgetToBudget
#print axioms UAVProof.LocalVisitPairingNextCertificate.budgetToNextBudget
#print axioms UAVProof.LocalVisitPairingNextCertificate.budgetOfPairingToNext
#print axioms UAVProof.LocalVisitPairingNextCertificate.nextBudgetToBudget_value
#print axioms UAVProof.LocalVisitPairingNextCertificate.budgetToNextBudget_value
#print axioms UAVProof.LocalVisitPairingNextCertificate.budgetOfPairingToNext_value
#print axioms UAVProof.LocalVisitPairingNextCertificate.nonempty_nextBudgetPotential_iff
#print axioms UAVProof.LocalVisitPairingNextCertificate.nextDescendingRank_iff
#print axioms UAVProof.LocalVisitPairingNextCertificate.descendingRank_roundtrip_iff
#print axioms UAVProof.LocalVisitPairingNextCertificate.nextDescendingRank_ofPairing_iff
#print axioms UAVProof.LocalVisitPairingNextCertificate.hasNextCertificate_iff_hasLocalCertificate
#print axioms UAVProof.LocalVisitPairingNextCertificate.exactFeasible_iff_hasNextCertificate
#print axioms
  UAVProof.LocalVisitPairingNextCertificate.exactFeasible_iff_count_and_hasNextCertificate
#print axioms UAVProof.LocalVisitPairingNextCertificate.zero_hasNextCertificate
#print axioms UAVProof.LocalVisitPairingNextCertificate.Examples.taskCycle_zero_budget
#print axioms UAVProof.LocalVisitPairingNextCertificate.Examples.taskCycle_has_no_nextDescendingRank
