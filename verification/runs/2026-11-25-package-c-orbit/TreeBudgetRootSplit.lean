import TreeBudgetPrefixMerge

/-!
# Package C (Issue #26) — Root Branch Decomposition (`root_split_iff`)

Working directory: `verification/runs/2026-11-25-package-c-orbit`.
Imports `TreeBudgetPrefixMerge`.

Contents:
1. Local lemmas:
   - `compactRep_cost_zero_of_not_active`: inactive routes have zero subtree linear cost.
   - `compactRep_rootChild_active_card`: at a root child `u`, `z.active.card = H u`.
2. Main theorem `root_split_iff`:
   `CompactRootAccept R H m s T ↔ (∑ u ∈ R.children R.root, H u) = m ∧`
   `  ∀ u ∈ R.children R.root, ∃ h : OrbitHist, ChildHist R H m s u h ∧ ∀ c, (true, c) ∈ h → c ≤ T`.
3. Direct bridge `matrixFeasible_iff_root_split` via `compactRootAccept_iff_matrixFeasible`.
4. Negative-budget regression (`ex_root_split_negative_budget`): root `0` with two leaf
   children `1, 2`, `m = 2`, `H = ![0, 1, 1]`, `s = ![0, -3, -2]`, `T = -1`.
-/

namespace UAVProof.TreeBudgetOrbitPrototype

open UAVProof.TreeFlowExistence UAVProof.TreeBudgetRow UAVProof.TreeBudgetSubtreeState

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Local lemma 1: under `CompactRep`, any inactive route has zero count across the
entire subtree and hence zero subtree linear cost. -/
theorem compactRep_cost_zero_of_not_active
    (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (v : V) (z : CompactState m) (hz : CompactRep R H m s v z)
    {i : Fin m} (hi : i ∉ z.active) :
    z.cost i = 0 := by
  rcases hz with ⟨n, hn, _, ha, hc⟩
  have htop : n i v = 0 := by
    have hnotpos : ¬ 0 < n i v := mt (ha i).mpr hi
    omega
  rw [← hc i, subtreeLinearCost]
  apply Finset.sum_eq_zero
  intro x _
  rw [hn.zero_of_top_zero i htop x]
  simp

/-- Local lemma 2: at any root child `u`, `RootChildCap` and the top-edge column sum
force `z.active.card = H u`. -/
theorem compactRep_rootChild_active_card
    (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (u : V) (hu : u ∈ R.children R.root) (z : CompactState m)
    (hz : CompactRep R H m s u z) :
    z.active.card = H u := by
  rcases hz with ⟨n, hn, hcap, ha, _⟩
  have hparent : R.parent u = R.root := ((R.mem_children R.root u).mp hu).2
  have hcap1 : ∀ i : Fin m, n i u ≤ 1 := hcap hparent
  have hsum : (∑ i : Fin m, n i u) = H u := hn.column u .self
  rw [← hsum]
  have hcard : z.active.card = ∑ i : Fin m, if i ∈ z.active then (1 : ℕ) else 0 := by
    simp
  rw [hcard]
  apply Finset.sum_congr rfl
  intro i _
  exact (capped_eq_indicator (fun j => n j u) z.active hcap1 ha i).symm

/-- Helper: given two subsets `A, B : Finset (Fin m)` of equal cardinality, construct
a permutation `σ : Equiv.Perm (Fin m)` such that `i ∈ A ↔ σ i ∈ B`. -/
theorem exists_perm_map_finset {m : ℕ} (A B : Finset (Fin m)) (hcard : A.card = B.card) :
    ∃ σ : Equiv.Perm (Fin m), ∀ i : Fin m, i ∈ A ↔ σ i ∈ B := by
  classical
  have hInCard : Fintype.card {i : Fin m // i ∈ A} = Fintype.card {j : Fin m // j ∈ B} := by
    simp [Fintype.card_coe, hcard]
  have hOutCard : Fintype.card {i : Fin m // i ∉ A} = Fintype.card {j : Fin m // j ∉ B} := by
    have hA : (Finset.univ.filter (fun i : Fin m => i ∉ A)).card = m - A.card := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
        (p := fun i => i ∈ A)
      have h1 : (Finset.univ.filter (fun i : Fin m => i ∈ A)).card = A.card := by
        have : Finset.univ.filter (fun i : Fin m => i ∈ A) = A := by ext i; simp
        rw [this]
      rw [h1, Finset.card_univ, Fintype.card_fin] at this
      omega
    have hB : (Finset.univ.filter (fun j : Fin m => j ∉ B)).card = m - B.card := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
        (p := fun j => j ∈ B)
      have h1 : (Finset.univ.filter (fun j : Fin m => j ∈ B)).card = B.card := by
        have : Finset.univ.filter (fun j : Fin m => j ∈ B) = B := by ext j; simp
        rw [this]
      rw [h1, Finset.card_univ, Fintype.card_fin] at this
      omega
    rw [Fintype.card_subtype, Fintype.card_subtype, hA, hB, hcard]
  let eIn : {i : Fin m // i ∈ A} ≃ {j : Fin m // j ∈ B} := Fintype.equivOfCardEq hInCard
  let eOut : {i : Fin m // i ∉ A} ≃ {j : Fin m // j ∉ B} := Fintype.equivOfCardEq hOutCard
  let σ : Equiv.Perm (Fin m) :=
    { toFun := fun i => if hi : i ∈ A then (eIn ⟨i, hi⟩).1 else (eOut ⟨i, hi⟩).1
      invFun := fun j => if hj : j ∈ B then (eIn.symm ⟨j, hj⟩).1 else (eOut.symm ⟨j, hj⟩).1
      left_inv := by
        intro i
        by_cases hi : i ∈ A
        · simp [hi, (eIn ⟨i, hi⟩).2]
        · simp [hi, (eOut ⟨i, hi⟩).2]
      right_inv := by
        intro j
        by_cases hj : j ∈ B
        · simp [hj, (eIn.symm ⟨j, hj⟩).2]
        · simp [hj, (eOut.symm ⟨j, hj⟩).2] }
  refine ⟨σ, ?_⟩
  intro i
  by_cases hi : i ∈ A
  · simp [σ, hi, (eIn ⟨i, hi⟩).2]
  · simp [σ, hi, (eOut ⟨i, hi⟩).2]

/-- Main Theorem (`root_split_iff`): root acceptance decomposes independently across
root children, checking the budget `c ≤ T` only on active routes `(true, c) ∈ h`
(so negative budgets `T < 0` are handled accurately). -/
theorem root_split_iff (R : RootedTree V) (H : V → ℕ) (m : ℕ) (s : V → ℚ) (T : ℚ) :
    CompactRootAccept R H m s T ↔
      (∑ u ∈ R.children R.root, H u) = m ∧
      ∀ u ∈ R.children R.root,
        ∃ h : OrbitHist, ChildHist R H m s u h ∧
          ∀ c : ℚ, (true, c) ∈ h → c ≤ T := by
  classical
  constructor
  · rintro ⟨zs, hzsRep, hdeg, hbud⟩
    refine ⟨?_, ?_⟩
    · calc
        (∑ u ∈ R.children R.root, H u) =
            ∑ u ∈ R.children R.root, (zs u).active.card := by
          apply Finset.sum_congr rfl
          intro u hu
          exact (compactRep_rootChild_active_card R H s u hu (zs u) (hzsRep u hu)).symm
        _ = ∑ u ∈ R.children R.root, ∑ i : Fin m, if i ∈ (zs u).active then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro u _
          simp
        _ = ∑ i : Fin m, ∑ u ∈ R.children R.root, if i ∈ (zs u).active then (1 : ℕ) else 0 :=
          Finset.sum_comm
        _ = ∑ _i : Fin m, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hdeg i
        _ = m := by simp
    · intro u hu
      refine ⟨jointHist (zs u), ⟨zs u, hzsRep u hu, rfl⟩, ?_⟩
      intro c hc
      simp only [jointHist, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hc
      rcases hc with ⟨i, hi⟩
      have hact : i ∈ (zs u).active := by
        have h1 := congrArg Prod.fst hi
        simp only [jointType, decide_eq_true_eq] at h1
        exact h1
      have hcost : (zs u).cost i = c := congrArg Prod.snd hi
      have hother_inactive : ∀ w ∈ R.children R.root, w ≠ u → i ∉ (zs w).active := by
        intro w hw hwu hiw
        have hsub : ({u, w} : Finset V) ⊆ R.children R.root := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hu
          · exact hw
        have hle := Finset.sum_le_sum_of_subset (f := fun x => if i ∈ (zs x).active then (1 : ℕ) else 0) hsub
        rw [Finset.sum_pair hwu.symm, if_pos hact, if_pos hiw, hdeg i] at hle
        omega
      have hsum_cost : (∑ w ∈ R.children R.root, (zs w).cost i) = (zs u).cost i := by
        apply Finset.sum_eq_single u
        · intro w hw hwu
          exact compactRep_cost_zero_of_not_active R H s w (zs w) (hzsRep w hw)
            (hother_inactive w hw hwu)
        · intro hnu
          exact (hnu hu).elim
      rw [← hcost, ← hsum_cost]
      exact hbud i
  · rintro ⟨hsum, hbranch⟩
    have hcard : Fintype.card (Fin m) = Fintype.card (Σ u : R.children R.root, Fin (H u.1)) := by
      rw [Fintype.card_fin, Fintype.card_sigma]
      simp only [Fintype.card_fin]
      rw [Finset.sum_coe_sort (R.children R.root) H]
      exact hsum.symm
    let e : Fin m ≃ Σ u : R.children R.root, Fin (H u.1) := Fintype.equivOfCardEq hcard
    let block : V → Finset (Fin m) := fun u => Finset.univ.filter (fun i => (e i).1.1 = u)
    have hblock_card : ∀ u ∈ R.children R.root, (block u).card = H u := by
      intro u hu
      have hsub : (block u).card = Fintype.card {i : Fin m // (e i).1.1 = u} := by
        rw [Fintype.card_subtype]
      rw [hsub, ← Fintype.card_fin (H u)]
      let f : Fin (H u) → {i : Fin m // (e i).1.1 = u} := fun k =>
        ⟨e.symm ⟨⟨u, hu⟩, k⟩, by simp⟩
      have hbij : Function.Bijective f := by
        constructor
        · intro k₁ k₂ hk
          have h1 : e.symm ⟨⟨u, hu⟩, k₁⟩ = e.symm ⟨⟨u, hu⟩, k₂⟩ := Subtype.mk.inj hk
          have h2 : (⟨⟨u, hu⟩, k₁⟩ : Σ w : R.children R.root, Fin (H w.1)) = ⟨⟨u, hu⟩, k₂⟩ :=
            e.symm.injective h1
          exact eq_of_heq (Sigma.mk.inj h2).2
        · rintro ⟨i, hi⟩
          cases h : e i with
          | mk w k =>
            have hwu : w = ⟨u, hu⟩ := Subtype.ext (by simpa [h] using hi)
            subst hwu
            refine ⟨k, Subtype.ext ?_⟩
            dsimp [f]
            rw [← h, e.symm_apply_apply]
      exact (Fintype.card_congr (Equiv.ofBijective f hbij)).symm
    have hw : ∀ u : V, ∃ z : CompactState m, u ∈ R.children R.root →
        CompactRep R H m s u z ∧
        (∀ i : Fin m, i ∈ z.active ↔ i ∈ block u) ∧
        (∀ i : Fin m, i ∈ z.active → z.cost i ≤ T) := by
      intro u
      by_cases hu : u ∈ R.children R.root
      · obtain ⟨h, ⟨z₀, hz₀Rep, hz₀Hist⟩, hbud⟩ := hbranch u hu
        have hactCard : (block u).card = z₀.active.card :=
          (hblock_card u hu).trans
            (compactRep_rootChild_active_card R H s u hu z₀ hz₀Rep).symm
        obtain ⟨σ, hσ⟩ := exists_perm_map_finset (block u) z₀.active hactCard
        refine ⟨reindex σ z₀, fun _ => ⟨compactRep_reindex R H s u σ z₀ hz₀Rep, ?_, ?_⟩⟩
        · intro i
          rw [mem_reindex_active]
          exact (hσ i).symm
        · intro i hi
          rw [mem_reindex_active] at hi
          have hmem : (true, z₀.cost (σ i)) ∈ h := by
            rw [← hz₀Hist]
            simp only [jointHist, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
            refine ⟨σ i, ?_⟩
            simp [jointType, hi]
          exact hbud (z₀.cost (σ i)) hmem
      · exact ⟨default, fun h => (hu h).elim⟩
    choose zs hzs using hw
    refine ⟨zs, fun u hu => (hzs u hu).1, ?_, ?_⟩
    · intro i
      let u₀ : V := (e i).1.1
      have hu₀ : u₀ ∈ R.children R.root := (e i).1.2
      have h1 : (∑ u ∈ R.children R.root, if i ∈ (zs u).active then (1 : ℕ) else 0) =
          if i ∈ (zs u₀).active then 1 else 0 := by
        apply Finset.sum_eq_single u₀
        · intro w hw hwu
          have hnot : i ∉ (zs w).active := by
            rw [(hzs w hw).2.1 i]
            simp [block, u₀, hwu.symm]
          simp [hnot]
        · intro hnu; exact (hnu hu₀).elim
      rw [h1]
      have hin : i ∈ (zs u₀).active := ((hzs u₀ hu₀).2.1 i).mpr (by simp [block, u₀])
      simp [hin]
    · intro i
      let u₀ : V := (e i).1.1
      have hu₀ : u₀ ∈ R.children R.root := (e i).1.2
      have hsum_i : (∑ u ∈ R.children R.root, (zs u).cost i) = (zs u₀).cost i := by
        apply Finset.sum_eq_single u₀
        · intro w hw hwu
          have hnot : i ∉ (zs w).active := by
            rw [(hzs w hw).2.1 i]
            simp [block, u₀, hwu.symm]
          exact compactRep_cost_zero_of_not_active R H s w (zs w) (hzs w hw).1 hnot
        · intro hnu; exact (hnu hu₀).elim
      rw [hsum_i]
      have hin : i ∈ (zs u₀).active := ((hzs u₀ hu₀).2.1 i).mpr (by simp [block, u₀])
      exact (hzs u₀ hu₀).2.2 i hin

/-- Direct bridge from the root orbit criterion to original `MatrixFeasible`. -/
theorem matrixFeasible_iff_root_split
    (R : RootedTree V) (H : V → ℕ) (m : ℕ) (s : V → ℚ) (T : ℚ) :
    TreeBudgetMatrix.MatrixFeasible R H m s T ↔
      (∑ u ∈ R.children R.root, H u) = m ∧
      ∀ u ∈ R.children R.root,
        ∃ h : OrbitHist, ChildHist R H m s u h ∧
          ∀ c : ℚ, (true, c) ∈ h → c ≤ T :=
  (compactRootAccept_iff_matrixFeasible R H m s T).symm.trans (root_split_iff R H m s T)

/-- Negative-budget regression: root `0` with two leaf children `1, 2`, `m = 2`,
`H = ![0, 1, 1]`, leaf costs `s = ![0, -3, -2]`, budget `T = -1`.
Inactive routes have cost `0 > -1`, yet `MatrixFeasible` holds because each route
uses one active leaf and pays `-3 ≤ -1` or `-2 ≤ -1`. -/
theorem ex_root_split_negative_budget
    (R : RootedTree (Fin 3))
    (hroot : R.root = 0)
    (hparent : R.parent = ![0, 0, 0]) :
    let H : Fin 3 → ℕ := ![0, 1, 1]
    let s : Fin 3 → ℚ := ![0, -3, -2]
    TreeBudgetMatrix.MatrixFeasible R H 2 s (-1) := by
  intro H s
  rw [matrixFeasible_iff_root_split]
  have hch : R.children R.root = {1, 2} := by
    ext u
    rw [R.mem_children, hroot, hparent]
    fin_cases u <;> decide
  have hleaf : ∀ u ∈ R.children R.root, R.children u = ∅ := by
    intro u hu
    rw [hch] at hu
    ext w
    simp only [R.mem_children, hroot, hparent, Finset.notMem_empty, iff_false, not_and]
    intro _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl <;> fin_cases w <;> decide
  refine ⟨?_, ?_⟩
  · rw [hch, Finset.sum_pair (by decide)]
    simp [H]
  · intro u hu
    have h12 : u = 1 ∨ u = 2 := by
      rw [hch] at hu
      simpa using hu
    have huv : u ≠ R.root := ((R.mem_children R.root u).mp hu).1
    let q : Fin 2 → ℕ := ![1, 0]
    refine ⟨prefixSeed R s u q, ?_, ?_⟩
    · rw [childHist_leaf_iff R H s u huv (hleaf u hu)]
      refine ⟨q, ?_, ?_, rfl⟩
      · rcases h12 with rfl | rfl <;> simp [q, H]
      · intro _ i; fin_cases i <;> decide
    · intro c hc
      simp only [prefixSeed, jointHist, Multiset.mem_map, Finset.mem_val,
        Finset.mem_univ, true_and] at hc
      rcases hc with ⟨i, hi⟩
      have hact : 0 < q i := by
        have h1 := congrArg Prod.fst hi
        simp only [jointType, parentState, Finset.mem_filter, Finset.mem_univ,
          true_and, decide_eq_true_eq] at h1
        exact h1
      have hi0 : i = 0 := by
        fin_cases i
        · rfl
        · simp [q] at hact
      subst hi0
      have hcost : (parentState R s u q ∅ (fun _ _ _ => 0)).cost 0 = c := congrArg Prod.snd hi
      rw [parentState_empty_cost] at hcost
      rw [← hcost]
      have hpu : R.parent u = R.root := ((R.mem_children R.root u).mp hu).2
      rcases h12 with rfl | rfl <;>
        simp [linearWeight, parentCharge, hpu, s, q]

end

end UAVProof.TreeBudgetOrbitPrototype

#print axioms UAVProof.TreeBudgetOrbitPrototype.compactRep_cost_zero_of_not_active
#print axioms UAVProof.TreeBudgetOrbitPrototype.compactRep_rootChild_active_card
#print axioms UAVProof.TreeBudgetOrbitPrototype.root_split_iff
#print axioms UAVProof.TreeBudgetOrbitPrototype.matrixFeasible_iff_root_split
#print axioms UAVProof.TreeBudgetOrbitPrototype.ex_root_split_negative_budget
