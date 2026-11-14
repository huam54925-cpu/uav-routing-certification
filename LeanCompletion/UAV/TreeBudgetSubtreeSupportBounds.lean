import LeanCompletion.UAV.TreeBudgetSubtreeGridBounds
import LeanCompletion.UAV.TreeBudgetSubtreeTableBounds

/-! Support-sensitive grid bounds. These only prove recoverability and counting;
the default executor continues to store every cost coordinate. -/
namespace UAVProof.TreeBudgetSubtreeExecutable
open TreeFlowExistence TreeBudgetSubtreeState
variable {N m D : ℕ}

theorem compact_finset_card_fixed_support (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ)
    (hscale : GridScale R s D w) (v : Fin N) (hv : v ≠ R.root)
    (S : Finset (ExecCompactState m)) (A : Finset (Fin m)) (hA : A.Nonempty)
    (hS : ∀ e ∈ S, CompactRep R H m s v (decodeState e))
    (hSA : ∀ e ∈ S, (decodeState e).active = A) :
    S.card ≤ (gridUpper (subtree R v) w H + 1 - gridLower (subtree R v) w H).toNat ^
      (A.card - 1) := by
  classical
  obtain ⟨p, hp⟩ := hA
  let L := gridLower (subtree R v) w H
  let U := gridUpper (subtree R v) w H
  have hg : ∀ e : S, ∃ b : Fin m → ℤ,
      (∀ i, (b i : ℚ) = (D : ℚ) * val e.val.cost i) ∧
      (∀ i, L ≤ b i ∧ b i ≤ U) := by
    intro e
    obtain ⟨b, hb, hi, _⟩ := compact_integer_grid hscale hv (hS e.val e.property)
    exact ⟨b, hb, hi⟩
  choose b hb hi using hg
  let code : S → (↥(A.erase p) → ↥(Finset.Icc L U)) :=
    fun e i => ⟨b e i.val, Finset.mem_Icc.mpr (hi e i.val)⟩
  have hinj : Function.Injective code := by
    intro e f hef
    have heA := hSA e.val e.property
    have hfA := hSA f.val f.property
    have he := hS e.val e.property
    have hf := hS f.val f.property
    have hc : ∀ i, i ≠ p → val e.val.cost i = val f.val.cost i := by
      intro i hip
      by_cases hiA : i ∈ A
      · have hh := congrArg Subtype.val (congrFun hef ⟨i, Finset.mem_erase.mpr ⟨hip, hiA⟩⟩)
        change b e i = b f i at hh
        have hs : (D : ℚ) * val e.val.cost i = (D : ℚ) * val f.val.cost i := by
          rw [← hb e, ← hb f]; exact_mod_cast hh
        exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hscale.1) hs
      · exact (compact_cost_zero_of_not_active he i (by simpa [heA] using hiA)).trans
          (compact_cost_zero_of_not_active hf i (by simpa [hfA] using hiA)).symm
    have hcp : val e.val.cost p = val f.val.cost p := by
      change (decodeState e.val).cost p = (decodeState f.val).cost p
      rw [compact_cost_recover he, compact_cost_recover hf]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact hc i (Finset.mem_erase.mp hi).1
    apply Subtype.ext
    apply state_ext
    · intro i
      have hh : (val e.val.active i = true) ↔ (val f.val.active i = true) := by
        rw [← mem_decodeState, ← mem_decodeState, heA, hfA]
      cases ha : val e.val.active i <;> cases hb : val f.val.active i <;> simp_all
    · intro i; by_cases hi : i = p
      · simpa [hi] using hcp
      · exact hc i hi
  have hh := Fintype.card_le_of_injective code hinj
  simpa [L, U, Fintype.card_coe, Int.card_Icc, Finset.card_erase_of_mem hp] using hh

theorem compact_active_nonempty (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (v : Fin N) (z : CompactState m)
    (hz : CompactRep R H m s v z) (hH : 0 < H v) : z.active.Nonempty := by
  obtain ⟨n, hn, _, ha, _⟩ := hz
  by_contra hempty
  have hz0 : ∀ i, n i v = 0 := by
    intro i
    have hh : ¬ 0 < n i v := by
      intro hi; exact hempty ⟨i, (ha i).mpr hi⟩
    omega
  have hh := hn.column v (.self)
  simp only [hz0, Finset.sum_const_zero] at hh
  omega

theorem compact_finset_card_supports (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ)
    (hscale : GridScale R s D w) (v : Fin N) (hv : v ≠ R.root)
    (S : Finset (ExecCompactState m)) (As : Finset (Finset (Fin m)))
    (hS : ∀ e ∈ S, CompactRep R H m s v (decodeState e))
    (hSA : ∀ e ∈ S, (decodeState e).active ∈ As)
    (hne : ∀ A ∈ As, A.Nonempty) :
    S.card ≤ ∑ A ∈ As,
      (gridUpper (subtree R v) w H + 1 - gridLower (subtree R v) w H).toNat ^ (A.card - 1) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise hSA]
  apply Finset.sum_le_sum
  intro A hA
  apply compact_finset_card_fixed_support R H s w hscale v hv _ A (hne A hA)
  · intro e he; exact hS e (Finset.mem_filter.mp he).1
  · intro e he; exact (Finset.mem_filter.mp he).2

theorem compact_finset_card_support_size (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ)
    (hscale : GridScale R s D w) (v : Fin N) (hv : v ≠ R.root)
    (S : Finset (ExecCompactState m)) (r : ℕ) (hr : 0 < r)
    (hS : ∀ e ∈ S, CompactRep R H m s v (decodeState e))
    (hcard : ∀ e ∈ S, (decodeState e).active.card = r) :
    S.card ≤ m.choose r *
      (gridUpper (subtree R v) w H + 1 - gridLower (subtree R v) w H).toNat ^ (r - 1) := by
  classical
  have hh := compact_finset_card_supports R H s w hscale v hv S
    (Finset.univ.powersetCard r) hS
    (fun e he => Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard e he⟩)
    (fun A hA => Finset.card_pos.mp (by rw [(Finset.mem_powersetCard.mp hA).2]; exact hr))
  have hs : (∑ A ∈ (Finset.univ : Finset (Fin m)).powersetCard r,
      (gridUpper (subtree R v) w H + 1 - gridLower (subtree R v) w H).toNat ^ (A.card - 1)) =
      m.choose r *
      (gridUpper (subtree R v) w H + 1 - gridLower (subtree R v) w H).toNat ^ (r - 1) := by
    simp_rw [Finset.sum_congr rfl (fun A hA => congrArg
      (fun n => (gridUpper (subtree R v) w H + 1 - gridLower (subtree R v) w H).toNat ^ (n - 1))
      (Finset.mem_powersetCard.mp hA).2)]
    simp [Finset.card_powersetCard]
  exact hs ▸ hh

theorem compact_finset_card_stratified (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ)
    (hscale : GridScale R s D w) (v : Fin N) (hv : v ≠ R.root) (hH : 0 < H v)
    (S : Finset (ExecCompactState m))
    (hS : ∀ e ∈ S, CompactRep R H m s v (decodeState e)) :
    S.card ≤ ∑ r ∈ Finset.Icc 1 (min m (H v)), m.choose r *
      (gridUpper (subtree R v) w H + 1 - gridLower (subtree R v) w H).toNat ^ (r - 1) := by
  classical
  have hmaps : ∀ e ∈ S, (decodeState e).active.card ∈ Finset.Icc 1 (min m (H v)) := by
    intro e he
    exact Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr (compact_active_nonempty R H s v _ (hS e he) hH),
      compact_active_card_le (hS e he)⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_le_sum
  intro r hr
  apply compact_finset_card_support_size R H s w hscale v hv _ r (Finset.mem_Icc.mp hr).1
  · intro e he; exact hS e (Finset.mem_filter.mp he).1
  · intro e he; exact (Finset.mem_filter.mp he).2

theorem root_child_finset_card_grid (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ)
    (hscale : GridScale R s D w) (v : Fin N) (hv : v ≠ R.root)
    (hp : R.parent v = R.root) (hH : 0 < H v) (S : Finset (ExecCompactState m))
    (hS : ∀ e ∈ S, CompactRep R H m s v (decodeState e)) :
    S.card ≤ m.choose (H v) *
      (gridUpper (subtree R v) w H + 1 - gridLower (subtree R v) w H).toNat ^ (H v - 1) :=
  compact_finset_card_support_size R H s w hscale v hv S (H v) hH hS
    (fun e he => compact_active_card_root_child (hS e he) hp)

theorem computeCompact_length_le_stratified (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ)
    (hscale : GridScale R s D w) (v : Fin N) (hv : v ≠ R.root) (hH : 0 < H v) :
    (computeCompact R H s m v).length ≤ ∑ r ∈ Finset.Icc 1 (min m (H v)), m.choose r *
      (gridUpper (subtree R v) w H + 1 - gridLower (subtree R v) w H).toNat ^ (r - 1) := by
  classical
  have hn : (computeCompact R H s m v).Nodup := by
    rw [computeCompact_eq]; exact List.nodup_dedup _
  rw [← List.toFinset_card_of_nodup hn]
  exact compact_finset_card_stratified R H s w hscale v hv hH _
    (fun e he => (computeCompact_spec R H s m v hv e).mp (List.mem_toFinset.mp he))

end UAVProof.TreeBudgetSubtreeExecutable
