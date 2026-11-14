import LeanCompletion.UAV.TreeBudgetSubtreeInvariants

/-! Signed integer intervals. The explicit scaling contract does not require
the budget to have an integral scaled value. -/
namespace UAVProof.TreeBudgetSubtreeState
open TreeFlowExistence
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : RootedTree V} {H : V → ℕ} {m : ℕ} {s : V → ℚ} {v : V}

def GridScale (R : RootedTree V) (s : V → ℚ) (D : ℕ) (w : V → ℤ) : Prop :=
  0 < D ∧ ∀ x, x ≠ R.root → (w x : ℚ) = (D : ℚ) * linearWeight R s x

def gridLower (X : Finset V) (w : V → ℤ) (H : V → ℕ) : ℤ :=
  ∑ x ∈ X, min 0 (w x * (H x : ℤ))

def gridUpper (X : Finset V) (w : V → ℤ) (H : V → ℕ) : ℤ :=
  ∑ x ∈ X, max 0 (w x * (H x : ℤ))

theorem signed_entry_bounds (w : ℤ) {a h : ℕ} (ha : a ≤ h) :
    min 0 (w * (h : ℤ)) ≤ w * (a : ℤ) ∧
      w * (a : ℤ) ≤ max 0 (w * (h : ℤ)) := by
  have hc : (a : ℤ) ≤ (h : ℤ) := by exact_mod_cast ha
  by_cases hw : 0 ≤ w
  · constructor
    · exact (min_le_left _ _).trans (mul_nonneg hw (Nat.cast_nonneg a))
    · exact (mul_le_mul_of_nonneg_left hc hw).trans (le_max_right _ _)
  · have hw' : w ≤ 0 := le_of_lt (lt_of_not_ge hw)
    constructor
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hc hw')
    · exact (mul_nonpos_of_nonpos_of_nonneg hw' (Nat.cast_nonneg a)).trans (le_max_left _ _)

theorem grid_width (X : Finset V) (w : V → ℤ) (H : V → ℕ) :
    gridUpper X w H - gridLower X w H = ∑ x ∈ X, |w x| * (H x : ℤ) := by
  rw [gridUpper, gridLower, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hh : |w x * (H x : ℤ)| = |w x| * (H x : ℤ) := by
    simp only [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ (H x : ℤ) from Int.natCast_nonneg _)]
  rw [← hh]
  by_cases hz : 0 ≤ w x * (H x : ℤ)
  · rw [max_eq_right hz, min_eq_left hz, abs_of_nonneg hz, sub_zero]
  · have hn : w x * (H x : ℤ) ≤ 0 := le_of_not_ge hz
    rw [max_eq_left hn, min_eq_right hn, abs_of_nonpos hn, zero_sub]

theorem compact_integer_grid {D : ℕ} {w : V → ℤ}
    (hscale : GridScale R s D w) (hv : v ≠ R.root)
    {z : CompactState m} (hz : CompactRep R H m s v z) :
    ∃ b : Fin m → ℤ,
      (∀ i, (b i : ℚ) = (D : ℚ) * z.cost i) ∧
      (∀ i, gridLower (subtree R v) w H ≤ b i ∧ b i ≤ gridUpper (subtree R v) w H) ∧
      (∑ i, b i) = ∑ x ∈ subtree R v, w x * (H x : ℤ) := by
  obtain ⟨n, hn, _, _, hc⟩ := hz
  let b : Fin m → ℤ := fun i => ∑ x ∈ subtree R v, w x * (n i x : ℤ)
  refine ⟨b, ?_, ?_, ?_⟩
  · intro i
    rw [← hc i, subtreeLinearCost, Finset.mul_sum]
    simp only [b, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hscale.2 x (subtree_ne_root hv ((mem_subtree _ _ _).mp hx)), mul_assoc]
  · intro i
    constructor
    · apply Finset.sum_le_sum
      intro x hx
      exact (signed_entry_bounds (w x) (hn.entry_le i x ((mem_subtree _ _ _).mp hx))).1
    · apply Finset.sum_le_sum
      intro x hx
      exact (signed_entry_bounds (w x) (hn.entry_le i x ((mem_subtree _ _ _).mp hx))).2
  · dsimp [b]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.mul_sum, ← Nat.cast_sum, hn.column x ((mem_subtree _ _ _).mp hx)]

theorem remaining_lower_bound (X Y : Finset V) (w : V → ℤ) (H : V → ℕ)
    (n : V → ℕ) (hn : ∀ x ∈ Y, n x ≤ H x) (B : ℤ)
    (hbudget : (∑ x ∈ X, w x * (n x : ℤ)) + (∑ x ∈ Y, w x * (n x : ℤ)) ≤ B) :
    (∑ x ∈ X, w x * (n x : ℤ)) + gridLower Y w H ≤ B := by
  have hl : gridLower Y w H ≤ ∑ x ∈ Y, w x * (n x : ℤ) := by
    apply Finset.sum_le_sum
    intro x hx
    exact (signed_entry_bounds (w x) (hn x hx)).1
  linarith

end UAVProof.TreeBudgetSubtreeState

namespace UAVProof.TreeBudgetSubtreeExecutable
open TreeFlowExistence TreeBudgetSubtreeState

theorem compact_finset_card_grid {N k D : ℕ} (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ)
    (hscale : GridScale R s D w) (v : Fin N) (hv : v ≠ R.root)
    (S : Finset (ExecCompactState (k + 1)))
    (hS : ∀ e ∈ S, CompactRep R H (k + 1) s v (decodeState e)) :
    S.card ≤ 2 ^ (k + 1) *
      (gridUpper (subtree R v) w H + 1 - gridLower (subtree R v) w H).toNat ^ k := by
  classical
  let L := gridLower (subtree R v) w H
  let U := gridUpper (subtree R v) w H
  have hg : ∀ e : S, ∃ b : Fin (k + 1) → ℤ,
      (∀ i, (b i : ℚ) = (D : ℚ) * val e.val.cost i) ∧
      (∀ i, L ≤ b i ∧ b i ≤ U) := by
    intro e
    obtain ⟨b, hb, hi, _⟩ := compact_integer_grid hscale hv (hS e.val e.property)
    exact ⟨b, hb, hi⟩
  choose b hb hi using hg
  let code : S → (Fin (k + 1) → Bool) × (Fin k → ↥(Finset.Icc L U)) :=
    fun e => ⟨val e.val.active, fun i => ⟨b e i.succ, Finset.mem_Icc.mpr (hi e i.succ)⟩⟩
  have hinj : Function.Injective code := by
    intro e f hef
    apply Subtype.ext
    apply state_ext
    · intro i
      exact congrFun (congrArg Prod.fst hef) i
    · have ht : ∀ i : Fin k, (decodeState e.val).cost i.succ =
          (decodeState f.val).cost i.succ := by
        intro i
        have heq : b e i.succ = b f i.succ :=
          congrArg Subtype.val (congrFun (congrArg Prod.snd hef) i)
        have heq' : (D : ℚ) * val e.val.cost i.succ = (D : ℚ) * val f.val.cost i.succ := by
          rw [← hb e, ← hb f, heq]
        exact (mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hscale.1)) heq'
      exact congrFun (compact_cost_eq_of_succ_eq (hS e.val e.property) (hS f.val f.property) ht)
  have hh := Fintype.card_le_of_injective code hinj
  simpa [L, U, Fintype.card_coe, Int.card_Icc] using hh

theorem computeCompact_length_le_grid {N k D : ℕ} (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (w : Fin N → ℤ)
    (hscale : GridScale R s D w) (v : Fin N) (hv : v ≠ R.root) :
    (computeCompact R H s (k + 1) v).length ≤ 2 ^ (k + 1) *
      (gridUpper (subtree R v) w H + 1 - gridLower (subtree R v) w H).toNat ^ k := by
  have hn : (computeCompact R H s (k + 1) v).Nodup := by
    rw [computeCompact_eq]
    exact List.nodup_dedup _
  rw [← List.toFinset_card_of_nodup hn]
  apply compact_finset_card_grid R H s w hscale v hv
  intro e he
  exact (computeCompact_spec R H s (k + 1) v hv e).mp (List.mem_toFinset.mp he)

end UAVProof.TreeBudgetSubtreeExecutable
