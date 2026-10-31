import LeanCompletion.UAV.LocalVisitPairing

/-!
# Next-only representation of local visit pairings

Only task-to-task predecessors must be unique. Arbitrarily many task copies
may return to the depot, and the stored successor of the depot is ignored.
Reconstruction normalizes both depot entries to the depot. Round trips preserve
task entries and every edge multiplicity, not arbitrary depot entries.

The predecessor construction uses classical choice; no executable recovery
algorithm is claimed. This is only structural equivalence: isolated task cycles
are allowed. Rank, budget potential and physical projection transport are left
to the next stage.
-/

namespace UAVProof.LocalVisitPairingNext

open LocalVisitPairing

/-- Sparse successor data. Injectivity is required only between task sources
with a common task target; depot returns need not be injective. -/
structure NextPairing (C : Type*) (depot : C) where
  next : C → C
  task_predecessor_unique : ∀ a b, a ≠ depot → b ≠ depot →
    next a = next b → next a ≠ depot → a = b

section Generic

variable {C : Type*} {depot : C}

/-- Choose a task predecessor if one exists, otherwise use the depot.
The depot itself always has predecessor depot, regardless of return edges. -/
noncomputable def prevOfNext (q : NextPairing C depot) (c : C) : C := by
  classical
  exact if c = depot then depot else
    if h : ∃ a, a ≠ depot ∧ q.next a = c then h.choose else depot

@[simp] theorem prevOfNext_depot (q : NextPairing C depot) :
    prevOfNext q depot = depot := by
  classical
  simp [prevOfNext]

/-- Any task predecessor of a task is the chosen predecessor. -/
theorem prevOfNext_eq_of_next (q : NextPairing C depot) (a c : C)
    (ha : a ≠ depot) (hc : c ≠ depot) (hn : q.next a = c) :
    prevOfNext q c = a := by
  classical
  have hex : ∃ b, b ≠ depot ∧ q.next b = c := ⟨a, ha, hn⟩
  rw [prevOfNext, if_neg hc, dif_pos hex]
  exact q.task_predecessor_unique _ a hex.choose_spec.1 ha
    (hex.choose_spec.2.trans hn.symm) (fun h => hc (hex.choose_spec.2.symm.trans h))

theorem prevOfNext_eq_depot_iff (q : NextPairing C depot) (c : C)
    (hc : c ≠ depot) :
    prevOfNext q c = depot ↔ ¬ ∃ a, a ≠ depot ∧ q.next a = c := by
  classical
  by_cases hex : ∃ a, a ≠ depot ∧ q.next a = c
  · rw [prevOfNext, if_neg hc, dif_pos hex]
    exact iff_of_false hex.choose_spec.1 (fun h => h hex)
  · simp [prevOfNext, hc, hex]

theorem prevOfNext_next (q : NextPairing C depot) (c : C)
    (hc : c ≠ depot) (hn : q.next c ≠ depot) :
    prevOfNext q (q.next c) = c :=
  prevOfNext_eq_of_next q c (q.next c) hc hn rfl

theorem next_prevOfNext (q : NextPairing C depot) (c : C)
    (hc : c ≠ depot) (hp : prevOfNext q c ≠ depot) :
    q.next (prevOfNext q c) = c := by
  classical
  by_cases hex : ∃ a, a ≠ depot ∧ q.next a = c
  · rw [prevOfNext, if_neg hc, dif_pos hex]
    exact hex.choose_spec.2
  · exact (hp ((prevOfNext_eq_depot_iff q c hc).2 hex)).elim

/-- Recover the existing pairing, normalizing both irrelevant depot entries. -/
noncomputable def toPairing (q : NextPairing C depot) : Pairing C depot := by
  classical
  exact {
    next := fun c => if c = depot then depot else q.next c
    prev := prevOfNext q
    prev_next := by
      intro c hc hn
      simp only [if_neg hc] at hn ⊢
      exact prevOfNext_next q c hc hn
    next_prev := by
      intro c hc hp
      rw [if_neg hp]
      exact next_prevOfNext q c hc hp
  }

@[simp] theorem toPairing_next_depot (q : NextPairing C depot) :
    (toPairing q).next depot = depot := by
  classical
  simp [toPairing]

@[simp] theorem toPairing_prev_depot (q : NextPairing C depot) :
    (toPairing q).prev depot = depot := prevOfNext_depot q

theorem toPairing_next_task (q : NextPairing C depot) (c : C) (hc : c ≠ depot) :
    (toPairing q).next c = q.next c := by
  classical
  simp [toPairing, hc]

theorem toPairing_prev_task (q : NextPairing C depot) (c : C) :
    (toPairing q).prev c = prevOfNext q c := rfl

/-- Existing local consistency already forces uniqueness of task predecessors. -/
theorem pairing_task_predecessor_unique (p : Pairing C depot)
    (a b : C) (ha : a ≠ depot) (hb : b ≠ depot)
    (heq : p.next a = p.next b) (hn : p.next a ≠ depot) : a = b := by
  have hbn : p.next b ≠ depot := heq ▸ hn
  calc
    a = p.prev (p.next a) := (p.prev_next a ha hn).symm
    _ = p.prev (p.next b) := congrArg p.prev heq
    _ = b := p.prev_next b hb hbn

/-- Extract successors without imposing a convention at the depot. -/
def ofPairing (p : Pairing C depot) : NextPairing C depot where
  next := p.next
  task_predecessor_unique := pairing_task_predecessor_unique p

/-- Recovered predecessors agree at every task, including route starts. -/
theorem prevOfNext_ofPairing_task (p : Pairing C depot) (c : C) (hc : c ≠ depot) :
    prevOfNext (ofPairing p) c = p.prev c := by
  by_cases hp : p.prev c = depot
  · rw [hp]
    apply (prevOfNext_eq_depot_iff (ofPairing p) c hc).2
    rintro ⟨a, ha, hn⟩
    change p.next a = c at hn
    have hnd : p.next a ≠ depot := hn ▸ hc
    have hprev := p.prev_next a ha hnd
    rw [hn, hp] at hprev
    exact ha hprev.symm
  · exact prevOfNext_eq_of_next (ofPairing p) (p.prev c) c hp hc
      (p.next_prev c hc hp)

theorem toPairing_ofPairing_next_task (p : Pairing C depot) (c : C) (hc : c ≠ depot) :
    (toPairing (ofPairing p)).next c = p.next c :=
  toPairing_next_task (ofPairing p) c hc

theorem toPairing_ofPairing_prev_task (p : Pairing C depot) (c : C) (hc : c ≠ depot) :
    (toPairing (ofPairing p)).prev c = p.prev c :=
  prevOfNext_ofPairing_task p c hc

/-- Edge multiplicities only depend on task entries of the two functions. -/
theorem pairedFlow_eq_of_task_eq [DecidableEq C]
    (p q : Pairing C depot)
    (hn : ∀ c, c ≠ depot → p.next c = q.next c)
    (hp : ∀ c, c ≠ depot → p.prev c = q.prev c) (a b : C) :
    pairedFlow p a b = pairedFlow q a b := by
  by_cases ha : a = depot
  · subst a
    by_cases hb : b = depot
    · subst b
      simp [pairedFlow]
    · simp [pairedFlow, hb, hp b hb]
  · simp [pairedFlow, ha, hn a ha]

/-- The round trip preserves every edge, including departures and returns. -/
theorem pairedFlow_toPairing_ofPairing_apply [DecidableEq C]
    (p : Pairing C depot) (a b : C) :
    pairedFlow (toPairing (ofPairing p)) a b = pairedFlow p a b :=
  pairedFlow_eq_of_task_eq _ p (toPairing_ofPairing_next_task p)
    (toPairing_ofPairing_prev_task p) a b

theorem pairedFlow_toPairing_ofPairing [DecidableEq C]
    (p : Pairing C depot) :
    pairedFlow (toPairing (ofPairing p)) = pairedFlow p := by
  funext a b
  exact pairedFlow_toPairing_ofPairing_apply p a b

/-- The uniqueness condition is exactly what is needed to complete task successors
to a pairing. No finite-type or cycle-exclusion hypothesis is needed. -/
theorem exists_pairing_iff (next : C → C) :
    (∃ p : Pairing C depot, ∀ c, c ≠ depot → p.next c = next c) ↔
      (∀ a b, a ≠ depot → b ≠ depot →
        next a = next b → next a ≠ depot → a = b) := by
  constructor
  · rintro ⟨p, hp⟩ a b ha hb heq hn
    apply pairing_task_predecessor_unique p a b ha hb
    · simpa only [hp a ha, hp b hb] using heq
    · simpa only [hp a ha] using hn
  · intro h
    exact ⟨toPairing ⟨next, h⟩, toPairing_next_task ⟨next, h⟩⟩

end Generic

namespace Examples

variable {C : Type*}

/-- Every task is a singleton route. Any number of returns to the depot is allowed. -/
def allReturn (C : Type*) (depot : C) : NextPairing C depot where
  next := fun _ => depot
  task_predecessor_unique := by
    intro _ _ _ _ _ hn
    exact (hn rfl).elim

theorem allReturn_prev (C : Type*) (depot c : C) :
    prevOfNext (allReturn C depot) c = depot := by
  by_cases hc : c = depot
  · subst c
    exact prevOfNext_depot _
  · apply (prevOfNext_eq_depot_iff _ c hc).2
    rintro ⟨a, _, ha⟩
    exact hc ha.symm

theorem allReturn_flow [DecidableEq C] (depot a b : C) :
    pairedFlow (toPairing (allReturn C depot)) a b =
      if (a = depot ∧ b ≠ depot) ∨ (a ≠ depot ∧ b = depot) then 1 else 0 := by
  by_cases ha : a = depot
  · subst a
    simp [pairedFlow, toPairing_prev_task, allReturn_prev]
  · simp [pairedFlow, ha, toPairing_next_task _ a ha, allReturn, eq_comm]

/-- One visit gives exactly the departure and return edges. -/
theorem single_visit_flow :
    pairedFlow (toPairing (allReturn (Fin 2) 0)) =
      fun a b => if a ≠ b then 1 else 0 := by
  funext a b
  rw [allReturn_flow]
  fin_cases a <;> fin_cases b <;> decide

/-- Distinct tasks can both return to the same depot. -/
theorem multiple_returns :
    (allReturn (Fin 3) 0).next 1 = 0 ∧
    (allReturn (Fin 3) 0).next 2 = 0 ∧
    ¬ Function.Injective (allReturn (Fin 3) 0).next := by
  refine ⟨rfl, rfl, ?_⟩
  intro hinj
  have h : (1 : Fin 3) = 2 := hinj rfl
  exact (by decide : (1 : Fin 3) ≠ 2) h

/-- In a depot-only type every reconstructed pairing has zero flow. -/
theorem depot_only_flow (q : NextPairing (Fin 1) 0) :
    pairedFlow (toPairing q) = fun _ _ => 0 := by
  funext a b
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst a
  subst b
  simp [pairedFlow]

/-- An explicit isolated two-task cycle satisfies predecessor uniqueness. -/
def taskCycle : NextPairing (Fin 3) 0 where
  next := ![0, 2, 1]
  task_predecessor_unique := by decide +kernel

theorem taskCycle_has_no_descending_rank :
    ¬ ∃ rank : Fin 3 → ℕ, DescendingRank (toPairing taskCycle) rank := by
  rintro ⟨rank, hrank⟩
  have h1 := hrank 1 (by decide)
  have h2 := hrank 2 (by decide)
  rw [toPairing_next_task _ 1 (by decide)] at h1
  rw [toPairing_next_task _ 2 (by decide)] at h2
  change rank 2 < rank 1 at h1
  change rank 1 < rank 2 at h2
  omega

/-- Arbitrary depot entries need not survive normalization. -/
def unnormalizedSingle : Pairing (Fin 2) 0 where
  next := ![1, 0]
  prev := ![1, 0]
  prev_next := by decide +kernel
  next_prev := by decide +kernel

theorem roundtrip_need_not_eq :
    toPairing (ofPairing unnormalizedSingle) ≠ unnormalizedSingle := by
  intro h
  have hn := congrArg (fun p : Pairing (Fin 2) 0 => p.next 0) h
  change (toPairing (ofPairing unnormalizedSingle)).next 0 =
    unnormalizedSingle.next 0 at hn
  rw [toPairing_next_depot] at hn
  exact (by decide : (0 : Fin 2) ≠ 1) hn

end Examples

end UAVProof.LocalVisitPairingNext

#print axioms UAVProof.LocalVisitPairingNext.prevOfNext
#print axioms UAVProof.LocalVisitPairingNext.prevOfNext_eq_of_next
#print axioms UAVProof.LocalVisitPairingNext.prevOfNext_eq_depot_iff
#print axioms UAVProof.LocalVisitPairingNext.prevOfNext_next
#print axioms UAVProof.LocalVisitPairingNext.next_prevOfNext
#print axioms UAVProof.LocalVisitPairingNext.toPairing
#print axioms UAVProof.LocalVisitPairingNext.pairing_task_predecessor_unique
#print axioms UAVProof.LocalVisitPairingNext.prevOfNext_ofPairing_task
#print axioms UAVProof.LocalVisitPairingNext.toPairing_ofPairing_next_task
#print axioms UAVProof.LocalVisitPairingNext.toPairing_ofPairing_prev_task
#print axioms UAVProof.LocalVisitPairingNext.pairedFlow_toPairing_ofPairing_apply
#print axioms UAVProof.LocalVisitPairingNext.pairedFlow_toPairing_ofPairing
#print axioms UAVProof.LocalVisitPairingNext.exists_pairing_iff
#print axioms UAVProof.LocalVisitPairingNext.Examples.single_visit_flow
#print axioms UAVProof.LocalVisitPairingNext.Examples.multiple_returns
#print axioms UAVProof.LocalVisitPairingNext.Examples.depot_only_flow
#print axioms UAVProof.LocalVisitPairingNext.Examples.taskCycle_has_no_descending_rank
#print axioms UAVProof.LocalVisitPairingNext.Examples.roundtrip_need_not_eq
