import LeanCompletion.UAV.TreeBudgetSubtreeResourceDenominators
import Mathlib.Data.Nat.Size

/-! Numerical magnitude bounds for exact preprocessing, including negative
floor budgets. These are not execution-time or representation-layout bounds. -/
namespace UAVProof.TreeBudgetSubtreeResource
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
open TreeBudgetSubtreeAutoScaleSeed
variable {N : ℕ}

theorem abs_rat_le_num (q : ℚ) : |q| ≤ (q.num.natAbs : ℚ) := by
  calc
    |q| = (q.num.natAbs : ℚ) / (q.den : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den q]
      simp [abs_div, Nat.cast_natAbs]
    _ ≤ _ := div_le_self (by positivity) (by exact_mod_cast q.pos)

theorem floorBudget_natAbs_le (D : ℕ) (T : ℚ) :
    (TreeBudgetSubtreeInteger.floorBudget D T).natAbs ≤ D * T.num.natAbs := by
  have ht := abs_le.mp (abs_rat_le_num T)
  have hlo : -((D * T.num.natAbs : ℕ) : ℚ) ≤ (D : ℚ) * T := by
    simpa [Nat.cast_mul] using mul_le_mul_of_nonneg_left ht.1 (Nat.cast_nonneg D)
  have hhi : (D : ℚ) * T ≤ ((D * T.num.natAbs : ℕ) : ℚ) := by
    simpa [Nat.cast_mul] using mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg D)
  have lo : -((D * T.num.natAbs : ℕ) : ℤ) ≤ ⌊(D : ℚ) * T⌋ :=
    Int.le_floor.mpr (by simpa using hlo)
  have hi : ⌊(D : ℚ) * T⌋ ≤ ((D * T.num.natAbs : ℕ) : ℤ) := by
    apply (Int.cast_le (R := ℚ)).mp
    simpa only [Int.cast_natCast] using (Int.floor_le ((D : ℚ) * T)).trans hhi
  have hh := abs_le.mpr ⟨lo, hi⟩
  simpa only [TreeBudgetSubtreeInteger.floorBudget, ← Int.natCast_natAbs,
    Int.ofNat_le] using hh

theorem prepare_budget_lt_pow (R : RootedTree (Fin N)) (s : Fin N → ℚ)
    (T : ℚ) (b : ℕ) (hs : ∀ v, v ≠ R.root → (s v).den < 2 ^ b)
    (hT : T.num.natAbs < 2 ^ b) :
    (prepare R s T).budget.natAbs < 2 ^ (((N - 1) + 1) * b) := by
  rw [prepare_budget]
  apply (floorBudget_natAbs_le _ _).trans_lt
  calc
    (prepare R s T).scale * T.num.natAbs < (prepare R s T).scale * 2 ^ b :=
      Nat.mul_lt_mul_of_pos_left hT (prepare_pos R s T)
    _ ≤ 2 ^ ((N - 1) * b) * 2 ^ b :=
      Nat.mul_le_mul_right _ (prepare_scale_le_pow R s T b hs)
    _ = _ := by rw [← pow_add]; congr 1; ring

theorem linearWeight_abs_lt_pow (R : RootedTree (Fin N)) (s : Fin N → ℚ)
    (b : ℕ) (hs : ∀ v, v ≠ R.root → (s v).num.natAbs < 2 ^ b)
    (v : Fin N) (hv : v ≠ R.root) : |linearWeight R s v| < (2 : ℚ) ^ (b + 1) := by
  have hservice (x : Fin N) (hx : x ≠ R.root) : |s x| < (2 : ℚ) ^ b :=
    (abs_rat_le_num _).trans_lt (by exact_mod_cast hs x hx)
  by_cases hp : R.parent v = R.root
  · simp only [linearWeight, parentCharge, if_pos hp, add_zero]
    have := hservice v hv
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℚ) < 2) b]
  · simp only [linearWeight, parentCharge, if_neg hp]
    have hv' := hservice v hv
    have hp' := hservice (R.parent v) hp
    have ha := abs_add_le (s v) (s (R.parent v))
    rw [pow_succ]
    linarith

theorem prepare_weight_lt_pow (R : RootedTree (Fin N)) (s : Fin N → ℚ)
    (T : ℚ) (b : ℕ)
    (hs : ∀ v, v ≠ R.root → (s v).num.natAbs < 2 ^ b ∧ (s v).den < 2 ^ b)
    (v : Fin N) :
    (val (prepare R s T).weight v).natAbs < 2 ^ ((((N - 1) + 1) * b) + 1) := by
  by_cases hv : v = R.root
  · subst v
    rw [prepare_root]
    simp
  · have hα := linearWeight_abs_lt_pow R s b (fun v hv => (hs v hv).1) v hv
    have hD := prepare_scale_le_pow R s T b (fun v hv => (hs v hv).2)
    have hd : (0 : ℚ) < (prepare R s T).scale := by exact_mod_cast prepare_pos R s T
    have hh : |((val (prepare R s T).weight v : ℤ) : ℚ)| <
        (2 : ℚ) ^ ((((N - 1) + 1) * b) + 1) := by
      calc
        _ = ((prepare R s T).scale : ℚ) * |linearWeight R s v| := by
          rw [prepare_weight R s T v hv, abs_mul, abs_of_pos hd]
        _ < ((prepare R s T).scale : ℚ) * 2 ^ (b + 1) :=
          mul_lt_mul_of_pos_left hα hd
        _ ≤ 2 ^ ((N - 1) * b) * 2 ^ (b + 1) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hD) (by positivity)
        _ = _ := by rw [← pow_add]; congr 1; ring
    have hc : ((val (prepare R s T).weight v).natAbs : ℚ) <
        (2 : ℚ) ^ ((((N - 1) + 1) * b) + 1) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
    exact_mod_cast hc

def coordBits (U : ℕ) : ℕ := max 1 (Nat.size U)

theorem coordBits_pos (U : ℕ) : 0 < coordBits U := by unfold coordBits; omega

theorem coordinate_lt_pow (U x : ℕ) (hx : x ≤ U) : x < 2 ^ coordBits U := by
  apply hx.trans_lt
  exact (Nat.lt_size_self U).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))

end UAVProof.TreeBudgetSubtreeResource
