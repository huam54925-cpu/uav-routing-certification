import TreeBudgetPrefixReach

/-!
# Issue #26, Multi-Child Fold, Item 3: Full-Node Orbit Equivalence

Working directory: `verification/runs/2026-11-25-package-c-orbit`.
Imports `TreeBudgetPrefixReach` (and transitively C0/C1, C2, C3, and Fold Step 1).

Proves `childHist_iff_fullPrefixReach`: for a non-root vertex `v` and any duplicate-free
list `us` covering `R.children v`, a target histogram `h` is realizable by `CompactRep`
(`ChildHist`) iff there exists a valid top-edge vector `q` (`∑ i, q i = H v` and
`RootChildCap R v q`) from which `PrefixReach` reaches `h`.
-/

namespace UAVProof.TreeBudgetOrbitPrototype

open UAVProof.TreeFlowExistence UAVProof.TreeBudgetRow UAVProof.TreeBudgetSubtreeState

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Full-node orbit equivalence at a non-root vertex `v`:
`h` is a `CompactRep`-realizable histogram at `v` iff some valid top-edge count vector `q`
reaches `h` by folding all children of `v` via `PrefixReach`. -/
theorem childHist_iff_fullPrefixReach
    (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (v : V) (hv : v ≠ R.root) (us : List V)
    (hd : us.Nodup) (hcover : us.toFinset = R.children v)
    (h : OrbitHist) :
    ChildHist R H m s v h ↔
      ∃ q : Fin m → ℕ, (∑ i, q i) = H v ∧
        RootChildCap R v q ∧ PrefixReach R H s v q us h := by
  classical
  have hall (u : V) (hu : u ∈ us) : u ∈ R.children v := by
    rw [← hcover]
    exact List.mem_toFinset.mpr hu
  have hfold (q : Fin m → ℕ) :
      PrefixReach R H s v q us h ↔
        PrefixWitnessHist R H s v q (R.children v) h := by
    simpa only [PrefixWitnessHist, hcover] using
      (prefixReach_iff_witness R H s v q us hd hall h)
  constructor
  · rintro ⟨z, hzRep, hzHist⟩
    obtain ⟨q, hq, hcap, hact, zs, hzsRep, hzsSub, hzCost⟩ :=
      (compactRep_merge_iff R H m s v hv z).mp hzRep
    have hw : ∀ u : V, ∃ n : Fin m → V → ℕ, u ∈ R.children v →
        PartialValid R H m u n ∧ RootChildCap R u (fun i => n i u) ∧
          (∀ i, i ∈ (zs u).active ↔ 0 < n i u) ∧
          ∀ i, subtreeLinearCost R s u (n i) = (zs u).cost i := by
      intro u
      by_cases hu : u ∈ R.children v
      · obtain ⟨n, hn⟩ := hzsRep u hu
        exact ⟨n, fun _ => hn⟩
      · exact ⟨fun _ _ => 0, fun h' => (hu h').elim⟩
    choose ns hns using hw
    refine ⟨q, hq, hcap, (hfold q).mpr ⟨ns, ?_, ?_⟩⟩
    · refine ⟨Finset.Subset.refl _, fun u hu => (hns u hu).1, fun u hu => (hns u hu).2.1, ?_⟩
      intro u hu i hp
      exact (hact i).mp (hzsSub u hu (((hns u hu).2.2.1 i).mpr hp))
    · have hpEq : parentState R s v q (R.children v) ns = z := by
        apply compactState_ext
        · ext i
          simp only [parentState, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (hact i).symm
        · funext i
          rw [hzCost i]
          simp only [parentState]
          congr 1
          apply Finset.sum_congr rfl
          intro u hu
          exact (hns u hu).2.2.2 i
      rw [hpEq, hzHist]
  · rintro ⟨q, hq, hcap, hreach⟩
    obtain ⟨ns, hP, hout⟩ := (hfold q).mp hreach
    let z : CompactState m := parentState R s v q (R.children v) ns
    let zs : V → CompactState m := fun u =>
      ⟨Finset.univ.filter (fun i => 0 < ns u i u), fun i => subtreeLinearCost R s u (ns u i)⟩
    refine ⟨z, (compactRep_merge_iff R H m s v hv z).mpr ?_, hout⟩
    refine ⟨q, hq, hcap, ?_, zs, ?_, ?_, ?_⟩
    · intro i
      simp [z, parentState]
    · intro u hu
      exact ⟨ns u, hP.valid u hu, hP.cap u hu, fun i => by simp [zs], fun _ => rfl⟩
    · intro u hu i hi
      simp only [zs, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [z, parentState, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hP.compat u hu i hi
    · intro i
      rfl

/-- Regression: lift `ex_prefixReach_two_child_hub` through `childHist_iff_fullPrefixReach`
to obtain `ChildHist` for the target histogram `{-1, 7}` at hub `v = 1`. -/
theorem ex_childHist_two_child_hub (R : RootedTree (Fin 4))
    (hroot : R.root = 0) (hparent : R.parent = ![0, 0, 1, 1]) :
    let s : Fin 4 → ℚ := ![0, 2, -5, 3]
    let H : Fin 4 → ℕ := ![0, 2, 1, 1]
    ChildHist R H 2 s 1
      (jointHist (⟨Finset.univ, ![-1, 7]⟩ : CompactState 2)) := by
  intro s H
  let q : Fin 2 → ℕ := ![1, 1]
  have hv : (1 : Fin 4) ≠ R.root := by rw [hroot]; decide
  have hcover : ([2, 3] : List (Fin 4)).toFinset = R.children 1 := by
    ext u
    rw [R.mem_children, hroot, hparent]
    fin_cases u <;> decide
  apply (childHist_iff_fullPrefixReach R H s 1 hv [2, 3] (by decide) hcover _).mpr
  refine ⟨q, ?_, ?_, ex_prefixReach_two_child_hub R hroot hparent⟩
  · simp [q, H]
  · intro _ i
    fin_cases i <;> decide

/-- Boundary regression 1 (non-root leaf): when `R.children v = ∅`, take `us = []`
and reduce `childHist_iff_fullPrefixReach` via `prefixReach_nil_iff`. -/
theorem childHist_leaf_iff
    (R : RootedTree V) (H : V → ℕ) {m : ℕ} (s : V → ℚ)
    (v : V) (hv : v ≠ R.root) (hleaf : R.children v = ∅)
    (h : OrbitHist) :
    ChildHist R H m s v h ↔
      ∃ q : Fin m → ℕ, (∑ i, q i) = H v ∧
        RootChildCap R v q ∧ prefixSeed R s v q = h := by
  have hcover : ([] : List V).toFinset = R.children v := by simp [hleaf]
  rw [childHist_iff_fullPrefixReach R H s v hv [] List.nodup_nil hcover h]
  simp only [prefixReach_nil_iff]

/-- Boundary regression 2 (zero routes, one-way implication): at any non-root vertex `v`,
`ChildHist R H 0 s v h` forces `H v = 0` (empty `Fin 0` sum) and `h = 0`
(`prefixReach_zero_routes_only_empty`). Kept one-way because descendants may still carry
positive demand. -/
theorem childHist_zero_routes_imp
    (R : RootedTree V) (H : V → ℕ) (s : V → ℚ)
    (v : V) (hv : v ≠ R.root) (h : OrbitHist)
    (hch : ChildHist R H 0 s v h) :
    H v = 0 ∧ h = 0 := by
  classical
  let us : List V := (R.children v).toList
  have hd : us.Nodup := Finset.nodup_toList (R.children v)
  have hcover : us.toFinset = R.children v := Finset.toList_toFinset (R.children v)
  have hall : ∀ u ∈ us, u ∈ R.children v := fun u hu => by
    rw [← hcover]; exact List.mem_toFinset.mpr hu
  obtain ⟨q, hq, _, hreach⟩ :=
    (childHist_iff_fullPrefixReach R H s v hv us hd hcover h).mp hch
  refine ⟨?_, prefixReach_zero_routes_only_empty R H s v q us hd hall h hreach⟩
  simpa using hq.symm

end

end UAVProof.TreeBudgetOrbitPrototype

#print axioms UAVProof.TreeBudgetOrbitPrototype.childHist_iff_fullPrefixReach
#print axioms UAVProof.TreeBudgetOrbitPrototype.ex_childHist_two_child_hub
#print axioms UAVProof.TreeBudgetOrbitPrototype.childHist_leaf_iff
#print axioms UAVProof.TreeBudgetOrbitPrototype.childHist_zero_routes_imp
