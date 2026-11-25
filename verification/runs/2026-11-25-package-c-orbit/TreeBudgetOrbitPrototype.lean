import LeanCompletion.UAV.TreeBudgetSubtreeCompact

/-!
# Package C (Issue #26) Prototype: C0 Permutation Invariance & C1 Orbit Representation

Exploratory prototype in `verification/runs/2026-11-25-package-c-orbit`.
Read-only imports from `LeanCompletion.UAV.TreeBudgetSubtreeCompact`.

Unified reindexing convention for `σ : Equiv.Perm (Fin m)`:
- Matrix rows: `reindexMatrix σ n i v = n (σ i) v`
- Compact state: `(reindex σ z).active = z.active.preimage σ σ.injective.injOn`
  (so `i ∈ (reindex σ z).active ↔ σ i ∈ z.active`),
  `(reindex σ z).cost i = z.cost (σ i)`.
-/

namespace UAVProof.TreeBudgetOrbitPrototype

open UAVProof.TreeFlowExistence UAVProof.TreeBudgetRow UAVProof.TreeBudgetSubtreeState

section ReindexAndC0

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Row-reindexing of a route-by-vertex matrix by a route permutation `σ`. -/
def reindexMatrix {m : ℕ} (σ : Equiv.Perm (Fin m)) (n : Fin m → V → ℕ) :
    Fin m → V → ℕ :=
  fun i v => n (σ i) v

/-- Unified reindexing of `CompactState m` by `σ : Equiv.Perm (Fin m)`.
At index `i`, `reindex σ z` reads the active flag and cost of `z` at `σ i`. -/
def reindex {m : ℕ} (σ : Equiv.Perm (Fin m)) (z : CompactState m) : CompactState m where
  active := Finset.univ.filter (fun i => σ i ∈ z.active)
  cost := fun i => z.cost (σ i)

@[simp]
theorem mem_reindex_active {m : ℕ} (σ : Equiv.Perm (Fin m)) (z : CompactState m) (i : Fin m) :
    i ∈ (reindex σ z).active ↔ σ i ∈ z.active := by
  simp [reindex]

@[simp]
theorem reindex_cost {m : ℕ} (σ : Equiv.Perm (Fin m)) (z : CompactState m) (i : Fin m) :
    (reindex σ z).cost i = z.cost (σ i) :=
  rfl

theorem compactState_ext {m : ℕ} {y z : CompactState m}
    (ha : y.active = z.active) (hc : y.cost = z.cost) : y = z := by
  cases y
  cases z
  simp_all

/-- C0 (Permutation invariance of `CompactRep` with explicit reindexed witness). -/
theorem compactRep_reindex (R : RootedTree V) (H : V → ℕ) {m : ℕ}
    (s : V → ℚ) (v : V) (σ : Equiv.Perm (Fin m)) (z : CompactState m)
    (hz : CompactRep R H m s v z) :
    CompactRep R H m s v (reindex σ z) := by
  rcases hz with ⟨n, hn, hcap, ha, hc⟩
  refine ⟨reindexMatrix σ n, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro i x hx
      exact hn.outside (σ i) x hx
    · intro x hx
      simpa [reindexMatrix] using (Equiv.sum_comp σ (fun j => n j x)).trans (hn.column x hx)
    · intro i x hx hne hp
      exact hn.ancestor (σ i) x hx hne hp
  · intro hr i
    exact hcap hr (σ i)
  · intro i
    simpa [reindexMatrix] using ha (σ i)
  · intro i
    exact hc (σ i)

end ReindexAndC0

section JointHistAndC1

/-- Joint route type binding structural activity and signed rational linear cost. -/
abbrev JointType := Bool × ℚ

/-- Joint type of route `i` in compact state `z`. -/
def jointType {m : ℕ} (z : CompactState m) (i : Fin m) : JointType :=
  (decide (i ∈ z.active), z.cost i)

/-- Joint-type histogram (multiset) of a compact state `z`. -/
def jointHist {m : ℕ} (z : CompactState m) : Multiset JointType :=
  (Finset.univ : Finset (Fin m)).val.map (jointType z)

@[simp]
theorem jointType_reindex {m : ℕ} (σ : Equiv.Perm (Fin m)) (z : CompactState m) (i : Fin m) :
    jointType (reindex σ z) i = jointType z (σ i) := by
  simp [jointType]

theorem eq_reindex_iff_jointType {m : ℕ} (σ : Equiv.Perm (Fin m)) (y z : CompactState m) :
    y = reindex σ z ↔ ∀ i : Fin m, jointType y i = jointType z (σ i) := by
  constructor
  · intro h i
    rw [h]
    exact jointType_reindex σ z i
  · intro h
    apply compactState_ext
    · ext i
      have h1 := congrArg Prod.fst (h i)
      simp only [jointType, mem_reindex_active] at h1 ⊢
      constructor
      · intro hi
        have : decide (σ i ∈ z.active) = true := h1.symm.trans (decide_eq_true hi)
        exact of_decide_eq_true this
      · intro hi
        have : decide (i ∈ y.active) = true := h1.trans (decide_eq_true hi)
        exact of_decide_eq_true this
    · funext i
      exact congrArg Prod.snd (h i)

theorem count_jointHist_eq_card_fiber {m : ℕ} (z : CompactState m) (t : JointType) :
    Multiset.count t (jointHist z) = Fintype.card {i : Fin m // jointType z i = t} := by
  classical
  unfold jointHist
  rw [Multiset.count_map]
  have hfilter :
      (Multiset.filter (fun a : Fin m => t = jointType z a) (Finset.univ : Finset (Fin m)).val).card =
      ((Finset.univ : Finset (Fin m)).filter (fun a => jointType z a = t)).card := by
    have hEq :
        Multiset.filter (fun a : Fin m => t = jointType z a) (Finset.univ : Finset (Fin m)).val =
        ((Finset.univ : Finset (Fin m)).filter (fun a => jointType z a = t)).val := by
      rw [Finset.filter_val]
      congr 1
      funext a
      exact propext eq_comm
    rw [hEq]
    rfl
  rw [hfilter, Fintype.card_subtype]

/-- C1 (Orbit characterization): two compact states have the same joint-type histogram
iff they differ by a single route permutation under the unified `reindex`. -/
theorem jointHist_eq_iff_reindex {m : ℕ} (y z : CompactState m) :
    jointHist y = jointHist z ↔ ∃ σ : Equiv.Perm (Fin m), y = reindex σ z := by
  classical
  constructor
  · intro h
    have hcard : ∀ t : JointType,
        Fintype.card {i : Fin m // jointType y i = t} =
        Fintype.card {j : Fin m // jointType z j = t} := by
      intro t
      rw [← count_jointHist_eq_card_fiber y t, ← count_jointHist_eq_card_fiber z t, h]
    let e : ∀ t : JointType,
        {i : Fin m // jointType y i = t} ≃ {j : Fin m // jointType z j = t} :=
      fun t => Fintype.equivOfCardEq (hcard t)
    let σ : Equiv.Perm (Fin m) :=
      (Equiv.sigmaFiberEquiv (jointType y)).symm.trans
        ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv (jointType z)))
    refine ⟨σ, (eq_reindex_iff_jointType σ y z).mpr ?_⟩
    intro i
    have hσ : σ i = (e (jointType y i) ⟨i, rfl⟩).1 := rfl
    rw [hσ]
    exact (e (jointType y i) ⟨i, rfl⟩).2.symm
  · rintro ⟨σ, rfl⟩
    rw [Multiset.ext]
    intro t
    rw [count_jointHist_eq_card_fiber, count_jointHist_eq_card_fiber]
    refine Fintype.card_congr ?_
    exact
      { toFun := fun ⟨i, hi⟩ => ⟨σ i, by simpa [jointType_reindex] using hi⟩
        invFun := fun ⟨j, hj⟩ => ⟨σ.symm j, by simpa [jointType_reindex] using hj⟩
        left_inv := fun ⟨i, _⟩ => by ext; simp
        right_inv := fun ⟨j, _⟩ => by ext; simp }

end JointHistAndC1

section VerificationExamples

/-! ### Example 1: `m = 0` (empty route index set) -/

theorem example_m_zero_hist_eq (y z : CompactState 0) :
    jointHist y = jointHist z := by
  apply (jointHist_eq_iff_reindex y z).mpr
  refine ⟨Equiv.refl (Fin 0), ?_⟩
  apply compactState_ext
  · ext i; exact Fin.elim0 i
  · funext i; exact Fin.elim0 i

theorem example_m_zero_exists_reindex (y z : CompactState 0) :
    ∃ σ : Equiv.Perm (Fin 0), y = reindex σ z :=
  (jointHist_eq_iff_reindex y z).mp (example_m_zero_hist_eq y z)

theorem example_m_zero_compactRep_reindex {V : Type*} [Fintype V] [DecidableEq V]
    (R : RootedTree V) (H : V → ℕ) (s : V → ℚ) (v : V) (z : CompactState 0)
    (hz : CompactRep R H 0 s v z) :
    CompactRep R H 0 s v (reindex (Equiv.refl (Fin 0)) z) :=
  compactRep_reindex R H s v (Equiv.refl (Fin 0)) z hz

/-! ### Example 2: Repeated joint types with negative rational costs (`m = 3`) -/

def ex2_z : CompactState 3 where
  active := {0, 2}
  cost := ![(-3 : ℚ) / 2, (5 : ℚ) / 4, (-3 : ℚ) / 2]

def ex2_y : CompactState 3 where
  active := {1, 2}
  cost := ![(5 : ℚ) / 4, (-3 : ℚ) / 2, (-3 : ℚ) / 2]

theorem example_repeated_negative_hist_eq :
    jointHist ex2_y = jointHist ex2_z := by
  have hswap : ex2_y = reindex (Equiv.swap (0 : Fin 3) 1) ex2_z := by
    apply compactState_ext
    · ext i
      fin_cases i <;> simp [ex2_y, ex2_z, Equiv.swap_apply_def]
    · funext i
      fin_cases i <;> simp [ex2_y, ex2_z, Equiv.swap_apply_def]
  exact (jointHist_eq_iff_reindex ex2_y ex2_z).mpr ⟨Equiv.swap 0 1, hswap⟩

theorem example_repeated_negative_exists_reindex :
    ∃ σ : Equiv.Perm (Fin 3), ex2_y = reindex σ ex2_z :=
  (jointHist_eq_iff_reindex ex2_y ex2_z).mp example_repeated_negative_hist_eq

/-! ### Example 3: Same active count & same cost multiset, but different joint histograms
`y = [(true, 0), (false, 1)]` vs `z = [(true, 1), (false, 0)]`. -/

def ex3_y : CompactState 2 where
  active := {0}
  cost := ![(0 : ℚ), 1]

def ex3_z : CompactState 2 where
  active := {0}
  cost := ![(1 : ℚ), 0]

theorem example_split_loss_active_card :
    ex3_y.active.card = ex3_z.active.card := by
  decide

theorem example_split_loss_cost_multiset :
    (Finset.univ : Finset (Fin 2)).val.map ex3_y.cost =
    (Finset.univ : Finset (Fin 2)).val.map ex3_z.cost := by
  have hu : (Finset.univ : Finset (Fin 2)).val = (0 : Fin 2) ::ₘ (1 : Fin 2) ::ₘ 0 := by decide
  rw [hu]
  simp only [ex3_y, ex3_z, Multiset.map_cons, Multiset.map_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact Multiset.cons_swap (0 : ℚ) (1 : ℚ) 0

theorem example_split_loss_jointHist_ne :
    jointHist ex3_y ≠ jointHist ex3_z := by
  intro h
  have hc := congrArg (Multiset.count (true, (0 : ℚ))) h
  have hu : (Finset.univ : Finset (Fin 2)).val = (0 : Fin 2) ::ₘ (1 : Fin 2) ::ₘ 0 := by decide
  simp [jointHist, hu, jointType, ex3_y, ex3_z] at hc

theorem example_split_loss_not_reindex :
    ¬ ∃ σ : Equiv.Perm (Fin 2), ex3_y = reindex σ ex3_z := by
  rw [← jointHist_eq_iff_reindex]
  exact example_split_loss_jointHist_ne

end VerificationExamples

/-! `inducedTable`, `LegalTable`, and `TransportRealizeExactSpec` are now defined
exclusively in `TreeBudgetTransportExact.lean` (C2) so C0/C1 and C2 can be imported
together without duplicate declarations. -/

end UAVProof.TreeBudgetOrbitPrototype

#print axioms UAVProof.TreeBudgetOrbitPrototype.compactRep_reindex
#print axioms UAVProof.TreeBudgetOrbitPrototype.jointHist_eq_iff_reindex
