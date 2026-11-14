import LeanCompletion.UAV.TreeBudgetSubtreeStatsGlobalBounds

/-! Exact global candidate counts, including failed recursive branches. -/
namespace UAVProof.TreeBudgetSubtreeStats
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeState TreeFlowExistence
variable {N m : ℕ}

theorem insideProfile_candidates (a : Vector Bool m) (b : Vector ℚ m)
    (ts : List (List (ExecCompactState m))) :
    (insideProfile a b ts).compositionCalls = 0 ∧ (insideProfile a b ts).rangeChoices = 0 := by
  have hh := insideProfile_bounds a b ts
  simp only [Covers, insideEnvelope] at hh
  omega

theorem rootProfile_candidates (ts : List (List (ExecCompactState m))) :
    (rootProfile ts).compositionCalls = 0 ∧ (rootProfile ts).rangeChoices = 0 := by
  have hh := rootProfile_bounds ts
  simp only [Covers, rootEnvelope] at hh
  omega

theorem nodeProfile_candidates (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (v : Fin N) (ts : List (List (ExecCompactState m))) :
    (nodeProfile R H s m v ts).compositionCalls = (compositionProfile m (H v)).compositionCalls ∧
    (nodeProfile R H s m v ts).rangeChoices = (compositionProfile m (H v)).rangeChoices := by
  simp [nodeProfile, DPStats.add, sumStats_compositionCalls, sumStats_rangeChoices,
    dedupProfile, Function.comp_def, (insideProfile_candidates _ _ _).1,
    (insideProfile_candidates _ _ _).2, List.map_const']

theorem computeProfile_candidates (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (v : Fin N) :
    (computeProfile R H s m v).compositionCalls =
      ∑ x ∈ subtree R v, (compositionProfile m (H x)).compositionCalls ∧
    (computeProfile R H s m v).rangeChoices =
      ∑ x ∈ subtree R v, (compositionProfile m (H x)).rangeChoices := by
  rw [computeProfile]
  simp only [DPStats.add, Nat.zero_add, sumStats_compositionCalls, sumStats_rangeChoices,
    List.map_map, Function.comp_def, (nodeProfile_candidates _ _ _ _ _ _).1,
    (nodeProfile_candidates _ _ _ _ _ _).2]
  have hc := fun u (hu : u ∈ (childrenList R v).attach) =>
    computeProfile_candidates R H s m u.val
  constructor
  · rw [List.map_congr_left (fun u hu => (hc u hu).1)]
    rw [List.attach_map_val (f := fun u =>
      ∑ x ∈ subtree R u, (compositionProfile m (H x)).compositionCalls)]
    rw [childrenList_sum, sum_subtree]
    omega
  · rw [List.map_congr_left (fun u hu => (hc u hu).2)]
    rw [List.attach_map_val (f := fun u =>
      ∑ x ∈ subtree R u, (compositionProfile m (H x)).rangeChoices)]
    rw [childrenList_sum, sum_subtree]
    omega
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList _ _ _).mp u.property)

theorem root_children_sum (R : RootedTree (Fin N)) (f : Fin N → ℕ) :
    (∑ u ∈ R.children R.root, ∑ x ∈ subtree R u, f x) =
      ∑ x ∈ Finset.univ.erase R.root, f x := by
  have hh := sum_subtree R R.root f
  rw [subtree_root] at hh
  have he := Finset.sum_erase_add Finset.univ f (Finset.mem_univ R.root)
  omega

theorem checkCompactStats_candidates (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    (checkCompactStats R H s m T).stats.compositionCalls =
      ∑ x ∈ Finset.univ.erase R.root, (H x + m + 1).choose m ∧
    (checkCompactStats R H s m T).stats.rangeChoices + (N - 1) =
      (checkCompactStats R H s m T).stats.compositionCalls := by
  have hcard : (Finset.univ.erase R.root).card = N - 1 := by simp
  have hc : (checkCompactStats R H s m T).stats.compositionCalls =
      ∑ x ∈ Finset.univ.erase R.root, (compositionProfile m (H x)).compositionCalls := by
    rw [checkCompactStats_count]
    simp only [DPStats.add, (rootProfile_candidates _).1, Nat.add_zero,
      sumStats_compositionCalls, List.map_map, Function.comp_def,
      (computeProfile_candidates _ _ _ _ _).1, childrenList_sum, root_children_sum]
  have hr : (checkCompactStats R H s m T).stats.rangeChoices =
      ∑ x ∈ Finset.univ.erase R.root, (compositionProfile m (H x)).rangeChoices := by
    rw [checkCompactStats_count]
    simp only [DPStats.add, (rootProfile_candidates _).2, Nat.add_zero,
      sumStats_rangeChoices, List.map_map, Function.comp_def,
      (computeProfile_candidates _ _ _ _ _).2, childrenList_sum, root_children_sum]
  refine ⟨by simpa only [compositionProfile_calls] using hc, ?_⟩
  rw [hc, hr, ← hcard]
  have hh := Finset.sum_congr (s₁ := Finset.univ.erase R.root) rfl
    (fun x _ => compositionProfile_choices m (H x))
  simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] using hh

end UAVProof.TreeBudgetSubtreeStats
