import LeanCompletion.UAV.TreeBudgetSubtreeIntegerDP
import Mathlib.Data.Nat.GCD.Basic

/-!
Automatic LCM preprocessing for the integer subtree solver. The root coefficient
is normalized to zero; signed coefficients and floor budgets are exact.
The Seed module name is retained for compatibility with the supplied interface.
-/
namespace UAVProof.TreeBudgetSubtreeAutoScaleSeed
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable

def denLCM : List ℚ → ℕ
  | [] => 1
  | a :: as => Nat.lcm a.den (denLCM as)

theorem denLCM_pos (as : List ℚ) : 0 < denLCM as := by
  induction as with
  | nil => decide
  | cons a as ih => exact Nat.lcm_pos (Rat.pos a) ih

theorem den_dvd_denLCM {a : ℚ} {as : List ℚ} (ha : a ∈ as) :
    a.den ∣ denLCM as := by
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Nat.dvd_lcm_left _ _
    · exact (ih ha).trans (Nat.dvd_lcm_right _ _)

theorem denLCM_le_product (as : List ℚ) :
    denLCM as ≤ (as.map Rat.den).prod := by
  induction as with
  | nil => simp [denLCM]
  | cons a as ih =>
    calc
      denLCM (a :: as) ≤ a.den * denLCM as :=
        Nat.lcm_le_mul (Rat.pos a) (denLCM_pos as)
      _ ≤ a.den * (as.map Rat.den).prod := Nat.mul_le_mul_left _ ih
      _ = ((a :: as).map Rat.den).prod := by simp

/-- Divide nonnegative integers exactly before multiplying by a signed numerator. -/
def scaleNum (D : ℕ) (a : ℚ) : ℤ :=
  ((D / a.den : ℕ) : ℤ) * a.num

theorem scaleNum_spec (D : ℕ) (a : ℚ) (h : a.den ∣ D) :
    (scaleNum D a : ℚ) = (D : ℚ) * a := by
  have hd : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hm : ((D / a.den : ℕ) : ℚ) * (a.den : ℚ) = (D : ℚ) := by
    exact_mod_cast (Nat.div_mul_cancel h)
  have ha : (a.num : ℚ) = (a.den : ℚ) * a := by
    simpa [mul_comm] using (div_eq_iff hd).mp (Rat.num_div_den a)
  calc
    (scaleNum D a : ℚ) = ((D / a.den : ℕ) : ℚ) * (a.num : ℚ) := by
      simp only [scaleNum, Int.cast_mul, Int.cast_natCast]
    _ = ((D / a.den : ℕ) : ℚ) * ((a.den : ℚ) * a) := by rw [ha]
    _ = (D : ℚ) * a := by rw [← mul_assoc, hm]

variable {N : ℕ}

/-- The root coordinate is irrelevant to the subtree solver and is normalized. -/
def normalizedWeight (R : RootedTree (Fin N)) (s : Fin N → ℚ) (v : Fin N) : ℚ :=
  if v = R.root then 0 else linearWeight R s v

def weightList (R : RootedTree (Fin N)) (s : Fin N → ℚ) : List ℚ :=
  (List.finRange N).map (normalizedWeight R s)

structure Prepared (N : ℕ) where
  scale : ℕ
  weight : Vector ℤ N
  budget : ℤ

/-- Materialize coefficients and the scale once. The root contributes denominator 1. -/
def prepare (R : RootedTree (Fin N)) (s : Fin N → ℚ) (T : ℚ) : Prepared N :=
  let as := weightList R s
  let D := denLCM as
  ⟨D, Vector.ofFn (fun v => scaleNum D (normalizedWeight R s v)),
    TreeBudgetSubtreeInteger.floorBudget D T⟩

theorem prepare_pos (R : RootedTree (Fin N)) (s : Fin N → ℚ) (T : ℚ) :
    0 < (prepare R s T).scale :=
  denLCM_pos (weightList R s)

theorem normalizedWeight_mem (R : RootedTree (Fin N)) (s : Fin N → ℚ) (v : Fin N) :
    normalizedWeight R s v ∈ weightList R s := by
  exact List.mem_map.mpr ⟨v, by simp, rfl⟩

theorem prepare_weight (R : RootedTree (Fin N)) (s : Fin N → ℚ) (T : ℚ)
    (v : Fin N) (hv : v ≠ R.root) :
    ((val (prepare R s T).weight v : ℤ) : ℚ) =
      ((prepare R s T).scale : ℚ) * linearWeight R s v := by
  have h := scaleNum_spec (denLCM (weightList R s)) (normalizedWeight R s v)
    (den_dvd_denLCM (normalizedWeight_mem R s v))
  simpa [prepare, normalizedWeight, hv] using h

@[simp] theorem prepare_root (R : RootedTree (Fin N)) (s : Fin N → ℚ) (T : ℚ) :
    val (prepare R s T).weight R.root = 0 := by
  simp [prepare, normalizedWeight, scaleNum]

@[simp] theorem prepare_budget (R : RootedTree (Fin N)) (s : Fin N → ℚ) (T : ℚ) :
    (prepare R s T).budget =
      TreeBudgetSubtreeInteger.floorBudget (prepare R s T).scale T := rfl

def checkAuto (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) : Bool :=
  let p := prepare R s T
  TreeBudgetSubtreeInteger.check R H (val p.weight) m p.budget

theorem checkAuto_eq (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    checkAuto R H s m T = checkCompact R H s m T := by
  unfold checkAuto
  change TreeBudgetSubtreeInteger.check R H (val (prepare R s T).weight) m
    (prepare R s T).budget = checkCompact R H s m T
  rw [prepare_budget]
  exact TreeBudgetSubtreeInteger.check_eq (prepare_pos R s T)
    R H s (val (prepare R s T).weight) m T (prepare_weight R s T)

/-- Changing to another valid positive scale does not change the decision. -/
theorem check_scale_independent (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) (D₁ D₂ : ℕ)
    (w₁ w₂ : Fin N → ℤ) (h₁ : 0 < D₁) (h₂ : 0 < D₂)
    (hw₁ : ∀ x, x ≠ R.root → (w₁ x : ℚ) = (D₁ : ℚ) * linearWeight R s x)
    (hw₂ : ∀ x, x ≠ R.root → (w₂ x : ℚ) = (D₂ : ℚ) * linearWeight R s x) :
    TreeBudgetSubtreeInteger.check R H w₁ m (TreeBudgetSubtreeInteger.floorBudget D₁ T) =
      TreeBudgetSubtreeInteger.check R H w₂ m (TreeBudgetSubtreeInteger.floorBudget D₂ T) := by
  rw [TreeBudgetSubtreeInteger.check_eq h₁ R H s w₁ m T hw₁,
    TreeBudgetSubtreeInteger.check_eq h₂ R H s w₂ m T hw₂]

example : denLCM ([] : List ℚ) = 1 := rfl
example : denLCM [(2 : ℚ) / 3, (-5 : ℚ) / 6] = 6 := by decide +kernel
example : scaleNum 6 ((-5 : ℚ) / 6) = -5 := by decide +kernel
example : TreeBudgetSubtreeInteger.floorBudget 3 ((-1 : ℚ) / 2) = -2 := by decide +kernel

#print axioms denLCM_pos
#print axioms den_dvd_denLCM
#print axioms denLCM_le_product
#print axioms scaleNum_spec
#print axioms prepare_pos
#print axioms prepare_weight
#print axioms prepare_root
#print axioms checkAuto_eq
#print axioms check_scale_independent

end UAVProof.TreeBudgetSubtreeAutoScaleSeed
