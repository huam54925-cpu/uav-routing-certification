import LeanCompletion.UAV.TreeBudgetSubtreeTableBounds

/-! Root-child filtering counts binary columns exactly. This does not change
the cost of first enumerating all weak compositions. -/
namespace UAVProof.TreeBudgetSubtreeExecutable
open TreeFlowExistence TreeBudgetSubtreeState

theorem localCandidates_root_child_length {N : ℕ} (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (m : ℕ) (v : Fin N) (hp : R.parent v = R.root) :
    (localCandidates R H m v).length = m.choose (H v) := by
  classical
  let A : Vector ℕ m → Finset (Fin m) := fun q => Finset.univ.filter (fun i => 0 < val q i)
  have hcap : ∀ q ∈ localCandidates R H m v, ∀ i, val q i ≤ 1 := by
    intro q hq
    exact (localCandidates_spec R H v q).mp hq |>.2 hp
  have he : ∀ q ∈ localCandidates R H m v, ∀ i, val q i = if i ∈ A q then 1 else 0 := by
    intro q hq
    exact capped_eq_indicator (val q) (A q) (hcap q hq) (by intro i; simp [A])
  have hcard : ∀ q ∈ localCandidates R H m v, (A q).card = H v := by
    intro q hq
    have hh := (localCandidates_spec R H v q).mp hq |>.1
    simp_rw [he q hq] at hh
    simpa using hh
  have hn : (localCandidates R H m v).Nodup := (compositionsV_nodup m (H v)).filter _
  rw [← List.toFinset_card_of_nodup hn]
  have hh : (localCandidates R H m v).toFinset.card =
      ((Finset.univ : Finset (Fin m)).powersetCard (H v)).card := by
    apply Finset.card_bij (fun q _ => A q)
    · intro q hq
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard q (List.mem_toFinset.mp hq)⟩
    · intro q hq r hr hqr
      apply vector_ext
      intro i
      rw [he q (List.mem_toFinset.mp hq), he r (List.mem_toFinset.mp hr), hqr]
    · intro B hB
      let q : Vector ℕ m := Vector.ofFn fun i => if i ∈ B then 1 else 0
      have hq : q ∈ localCandidates R H m v := by
        apply (localCandidates_spec R H v q).mpr
        constructor
        · simpa [q] using (Finset.mem_powersetCard.mp hB).2
        · intro _ i
          simp only [q, val_ofFn]
          split_ifs <;> omega
      refine ⟨q, List.mem_toFinset.mpr hq, ?_⟩
      ext i; by_cases hi : i ∈ B <;> simp [A, q, hi]
  simpa [Finset.card_powersetCard] using hh

theorem localCandidates_root_child_empty {N : ℕ} (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (m : ℕ) (v : Fin N) (hp : R.parent v = R.root) (hm : m < H v) :
    localCandidates R H m v = [] := by
  apply List.length_eq_zero_iff.mp
  rw [localCandidates_root_child_length R H m v hp, Nat.choose_eq_zero_of_lt hm]

theorem computeCompact_root_child_empty {N : ℕ} (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (m : ℕ) (v : Fin N)
    (hp : R.parent v = R.root) (hm : m < H v) : computeCompact R H s m v = [] := by
  rw [computeCompact_eq]
  simp [nodeTable, localCandidates_root_child_empty R H m v hp hm]

end UAVProof.TreeBudgetSubtreeExecutable
