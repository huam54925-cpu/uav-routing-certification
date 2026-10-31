import LeanCompletion.UAV.LocalVisitPairingFiniteCertificate

/-!
# Executable validation of one finite candidate

Each task contributes its successor edge. A task with no task predecessor also
contributes a depot departure. The depot's stored successor is ignored. These
counts use finite enumeration, decidable equality and natural arithmetic only.
Classical pairing reconstruction occurs solely in the correctness proofs.

The checker uses exact rational arithmetic and does not enumerate candidates.
Rejecting one candidate says nothing about the existence of another certificate.
-/

namespace UAVProof.LocalVisitPairingFiniteChecker

open ResourceCuts VisitCopyLift SupportExactFeasibility
open LocalVisitPairing LocalVisitPairingNext LocalVisitPairingFiniteCertificate

section DirectFlow

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Each task supplies its successor edge; each start supplies a depot edge.
In particular `next depot` never supplies an edge. -/
def directCopyFlow (depot : C) (next : C → C) (a b : C) : ℕ :=
  if a = depot then
    if b ≠ depot ∧ ¬ ∃ c, c ≠ depot ∧ next c = b then 1 else 0
  else if next a = b then 1 else 0

/-- Predecessor uniqueness suffices; no rank or cost hypotheses are needed. -/
theorem directCopyFlow_eq_pairedFlow (depot : C) (q : NextPairing C depot) :
    directCopyFlow depot q.next = pairedFlow (toPairing q) := by
  funext a b
  by_cases ha : a = depot
  · subst a
    by_cases hb : b = depot
    · subst b
      simp [directCopyFlow, pairedFlow]
    · simp [directCopyFlow, pairedFlow, hb, toPairing_prev_task,
        prevOfNext_eq_depot_iff q b hb]
  · simp [directCopyFlow, pairedFlow, ha, toPairing_next_task q a ha]

end DirectFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Accumulate direct copy-edge counts over both physical endpoint fibers.
Only the finite copy space is enumerated, never the candidate space. -/
def directProjectedFlow (depot : V) (required : V → ℕ)
    (next : VisitCopy depot required → VisitCopy depot required) : V → V → ℕ :=
  projectFlow (project depot required) (directCopyFlow none next)

theorem directProjectedFlow_eq_projectFlow (depot : V) (required : V → ℕ)
    (q : NextPairing (VisitCopy depot required) none) :
    directProjectedFlow depot required q.next =
      projectFlow (project depot required) (pairedFlow (toPairing q)) := by
  unfold directProjectedFlow
  rw [directCopyFlow_eq_pairedFlow]

/-- A computable conjunction of checks on the supplied candidate. This does
not invoke a decidability instance for the classical validity proposition. -/
def checkCandidate (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ) (code : FiniteCandidate depot required service T) : Bool :=
  decide (0 ≤ T) &&
    (decide (∀ a b, a ≠ none → b ≠ none → code.next a = code.next b →
      code.next a ≠ none → a = b) &&
    (decide ((code.rank none).val = 0) &&
    (decide (∀ c, c ≠ none → (code.rank (code.next c)).val < (code.rank c).val) &&
    (decide (∀ c, c ≠ none → 1 ≤ (code.rank c).val) &&
    (decide ((code.potential none).val = 0) &&
    (decide (∀ c, c ≠ none → copyService depot required service c +
      decodedPotential code (code.next c) ≤ decodedPotential code c) &&
    (decide (∀ c, c ≠ none → (¬ ∃ a, a ≠ none ∧ code.next a = c) →
      decodedPotential code c ≤ T) &&
    decide (∀ u v, directProjectedFlow depot required code.next u v = x u v))))))))

/-- Exact correspondence with the existing validity definition, without
service-sign, physical no-loop, or positive-budget assumptions. -/
theorem checkCandidate_eq_true_iff (depot : V) (required : V → ℕ)
    (x : V → V → ℕ) (service : V → ℚ) (T : ℚ)
    (code : FiniteCandidate depot required service T) :
    checkCandidate depot required x service T code = true ↔
      ValidFiniteCertificate depot required x service T code := by
  simp only [checkCandidate, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hT, hu, hr0, hrd, hrp, hp0, hs, ht, hx⟩
    refine ⟨hT, hu, hr0, hrd, hrp, hp0, hs, ht, ?_⟩
    intro u v
    rw [← directProjectedFlow_eq_projectFlow depot required ⟨code.next, hu⟩]
    exact hx u v
  · intro h
    refine ⟨h.budget_nonneg, h.predecessor_unique, h.rank_zero, h.rank_descending,
      h.rank_positive, h.potential_zero, h.step, h.start, ?_⟩
    intro u v
    rw [directProjectedFlow_eq_projectFlow depot required
      ⟨code.next, h.predecessor_unique⟩]
    exact h.project_exact u v

theorem exactFeasible_iff_count_and_exists_checkedCandidate
    (depot : V) (required : V → ℕ) (x : V → V → ℕ) (m : ℕ)
    (service : V → ℚ) (T : ℚ) (hloop : ∀ v, x v v = 0)
    (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T) :
    ExactFeasible depot x required m service T ↔
      m = outFlow Finset.univ x depot ∧
        ∃ code : FiniteCandidate depot required service T,
          checkCandidate depot required x service T code = true := by
  simp_rw [checkCandidate_eq_true_iff]
  exact exactFeasible_iff_count_and_exists_validFiniteCertificate
    depot required x m service T hloop hservice hT

namespace Examples

/-- Explicit empty data, including the negative-budget test case. -/
def emptyCandidate (T : ℚ) :
    FiniteCandidate (0 : Fin 1) (fun _ => 0) (fun _ => 0) T where
  next := fun _ => none
  rank := fun _ => 0
  potential := fun _ => 0

def singleCandidate :
    FiniteCandidate (0 : Fin 2) (fun _ => 1) (fun _ => 1) 1 where
  next := fun _ => none
  rank := fun c => if c = none then 0 else ⟨1, by decide +kernel⟩
  potential := fun c => if c = none then 0 else ⟨1, by decide +kernel⟩

/-- The arbitrary depot demand is ignored, as in the general definitions. -/
def starFlow {n : ℕ} (u v : Fin (n + 1)) : ℕ :=
  if (u = 0 ∧ v ≠ 0) ∨ (u ≠ 0 ∧ v = 0) then 1 else 0

def firstTask : VisitCopy (0 : Fin 3) (fun _ => 1) :=
  some ⟨⟨1, by decide⟩, 0⟩

def secondTask : VisitCopy (0 : Fin 3) (fun _ => 1) :=
  some ⟨⟨2, by decide⟩, 0⟩

/-- Both tasks return to the depot. The depot successor is deliberately a
task: it must not be counted as an additional physical departure. -/
def twoRoutesCandidate :
    FiniteCandidate (0 : Fin 3) (fun _ => 1) (fun _ => 1) 1 where
  next := fun c => if c = none then firstTask else none
  rank := fun c => if c = none then 0 else ⟨1, by decide +kernel⟩
  potential := fun c => if c = none then 0 else ⟨1, by decide +kernel⟩

def cycleCandidate :
    FiniteCandidate (0 : Fin 3) (fun _ => 1) (fun _ => 0) 0 where
  next := fun c => if c = firstTask then secondTask else
    if c = secondTask then firstTask else none
  rank := fun c => if c = none then 0 else ⟨1, by decide +kernel⟩
  potential := fun _ => 0

def cycleFlow (u v : Fin 3) : ℕ :=
  if (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) then 1 else 0

def badPotentialCandidate :
    FiniteCandidate (0 : Fin 2) (fun _ => 1) (fun _ => 1) 1 :=
  { singleCandidate with potential := fun _ => 0 }

#eval ("empty, T=0", checkCandidate 0 (fun _ => 0) (fun _ _ => 0)
  (fun _ => 0) 0 (emptyCandidate 0))
#eval ("empty, T=-1", checkCandidate 0 (fun _ => 0) (fun _ _ => 0)
  (fun _ => 0) (-1) (emptyCandidate (-1)))
#eval ("single task", checkCandidate 0 (fun _ => 1) starFlow
  (fun _ => 1) 1 singleCandidate)
#eval ("two depot returns", checkCandidate 0 (fun _ => 1) starFlow
  (fun _ => 1) 1 twoRoutesCandidate)
#eval ("zero-fee cycle", checkCandidate 0 (fun _ => 1) cycleFlow
  (fun _ => 0) 0 cycleCandidate)
#eval ("wrong edge counts", checkCandidate 0 (fun _ => 1) (fun _ _ => 0)
  (fun _ => 1) 1 singleCandidate)
#eval ("failed potential step", checkCandidate 0 (fun _ => 1) starFlow
  (fun _ => 1) 1 badPotentialCandidate)

theorem empty_accept : checkCandidate 0 (fun _ => 0) (fun _ _ => 0)
    (fun _ => 0) 0 (emptyCandidate 0) = true := by decide +kernel

theorem negative_empty_reject : checkCandidate 0 (fun _ => 0) (fun _ _ => 0)
    (fun _ => 0) (-1) (emptyCandidate (-1)) = false := by decide +kernel

theorem single_accept : checkCandidate 0 (fun _ => 1) starFlow
    (fun _ => 1) 1 singleCandidate = true := by decide +kernel

theorem two_returns_accept : checkCandidate 0 (fun _ => 1) starFlow
    (fun _ => 1) 1 twoRoutesCandidate = true := by decide +kernel

theorem cycle_reject : checkCandidate 0 (fun _ => 1) cycleFlow
    (fun _ => 0) 0 cycleCandidate = false := by decide +kernel

theorem wrong_flow_reject : checkCandidate 0 (fun _ => 1) (fun _ _ => 0)
    (fun _ => 1) 1 singleCandidate = false := by decide +kernel

theorem bad_potential_reject : checkCandidate 0 (fun _ => 1) starFlow
    (fun _ => 1) 1 badPotentialCandidate = false := by decide +kernel

end Examples

#check directCopyFlow_eq_pairedFlow
#print axioms directCopyFlow_eq_pairedFlow
#check directProjectedFlow_eq_projectFlow
#print axioms directProjectedFlow_eq_projectFlow
#check checkCandidate_eq_true_iff
#print axioms checkCandidate_eq_true_iff
#check exactFeasible_iff_count_and_exists_checkedCandidate
#print axioms exactFeasible_iff_count_and_exists_checkedCandidate
#print axioms Examples.empty_accept
#print axioms Examples.negative_empty_reject
#print axioms Examples.single_accept
#print axioms Examples.two_returns_accept
#print axioms Examples.cycle_reject
#print axioms Examples.wrong_flow_reject
#print axioms Examples.bad_potential_reject

end UAVProof.LocalVisitPairingFiniteChecker
