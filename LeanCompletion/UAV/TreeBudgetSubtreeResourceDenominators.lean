import LeanCompletion.UAV.TreeBudgetSubtreeAutoScaleSeed
import Mathlib.Data.Rat.Lemmas

/-! The linear coefficient transform preserves the common denominator of all
nonroot services. Parent induction uses the opposite direction from subtree DP. -/
namespace UAVProof.TreeBudgetSubtreeResource
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
open TreeBudgetSubtreeAutoScaleSeed
variable {N : ℕ}

def integralRat (q : ℚ) : Prop := ∃ z : ℤ, (z : ℚ) = q

theorem integral_scaled_iff_den_dvd (D : ℕ) (q : ℚ) :
    integralRat ((D : ℚ) * q) ↔ q.den ∣ D := by
  constructor
  · rintro ⟨z, hz⟩
    by_cases hD : D = 0
    · simp [hD]
    · have hd : (D : ℚ) ≠ 0 := by exact_mod_cast hD
      have hq : q = Rat.divInt z (D : ℤ) := by
        rw [Rat.divInt_eq_div]
        apply (eq_div_iff (by simpa using hd)).2
        simpa [mul_comm] using hz.symm
      have hh : (q.den : ℤ) ∣ (D : ℤ) := by rw [hq]; exact Rat.den_dvd _ _
      exact_mod_cast hh
  · intro h
    exact ⟨scaleNum D q, scaleNum_spec D q h⟩

theorem denLCM_dvd_iff (qs : List ℚ) (D : ℕ) :
    denLCM qs ∣ D ↔ ∀ q ∈ qs, q.den ∣ D := by
  induction qs with
  | nil => simp [denLCM]
  | cons q qs ih => simp [denLCM, Nat.lcm_dvd_iff, ih]

def serviceDenLCM (R : RootedTree (Fin N)) (s : Fin N → ℚ) : ℕ :=
  denLCM ((List.finRange N).map fun v => if v = R.root then 0 else s v)

theorem normalized_denLCM_dvd_iff (R : RootedTree (Fin N)) (f : Fin N → ℚ) (D : ℕ) :
    denLCM ((List.finRange N).map fun v => if v = R.root then 0 else f v) ∣ D ↔
      ∀ v, v ≠ R.root → (f v).den ∣ D := by
  rw [denLCM_dvd_iff]
  simp only [List.forall_mem_map, List.mem_finRange, forall_true_left]
  constructor
  · intro h v hv
    simpa [hv] using h v
  · intro h v
    by_cases hv : v = R.root
    · simp [hv]
    · simpa [hv] using h v hv

theorem serviceDenLCM_dvd_iff (R : RootedTree (Fin N)) (s : Fin N → ℚ) (D : ℕ) :
    serviceDenLCM R s ∣ D ↔ ∀ v, v ≠ R.root → (s v).den ∣ D :=
  normalized_denLCM_dvd_iff R s D

theorem prepare_scale_dvd_iff (R : RootedTree (Fin N)) (s : Fin N → ℚ)
    (T : ℚ) (D : ℕ) :
    (prepare R s T).scale ∣ D ↔ ∀ v, v ≠ R.root → (linearWeight R s v).den ∣ D :=
  normalized_denLCM_dvd_iff R (linearWeight R s) D

theorem linear_den_dvd (R : RootedTree (Fin N)) (s : Fin N → ℚ) (D : ℕ)
    (h : ∀ v, v ≠ R.root → (s v).den ∣ D) (v : Fin N) (hv : v ≠ R.root) :
    (linearWeight R s v).den ∣ D := by
  by_cases hp : R.parent v = R.root
  · simpa [linearWeight, parentCharge, hp] using h v hv
  · simpa [linearWeight, parentCharge, hp] using
      (Rat.add_den_dvd_lcm (s v) (s (R.parent v))).trans (Nat.lcm_dvd (h v hv) (h _ hp))

theorem service_den_dvd (R : RootedTree (Fin N)) (s : Fin N → ℚ) (D : ℕ)
    (h : ∀ v, v ≠ R.root → (linearWeight R s v).den ∣ D)
    (v : Fin N) (hv : v ≠ R.root) : (s v).den ∣ D := by
  by_cases hp : R.parent v = R.root
  · simpa [linearWeight, parentCharge, hp] using h v hv
  · have hs : s v = linearWeight R s v - s (R.parent v) := by
      simp [linearWeight, parentCharge, hp]
    rw [hs]
    exact (Rat.sub_den_dvd_lcm _ _).trans
      (Nat.lcm_dvd (h v hv) (service_den_dvd R s D h (R.parent v) hp))
termination_by (∑ x : Fin N, R.rank x) - R.rank v
decreasing_by
  have hbound : R.rank (R.parent v) ≤ ∑ x : Fin N, R.rank x :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hlt := R.parent_rank v hv
  omega

theorem prepare_scale_eq_serviceDenLCM (R : RootedTree (Fin N))
    (s : Fin N → ℚ) (T : ℚ) : (prepare R s T).scale = serviceDenLCM R s := by
  apply Nat.dvd_antisymm
  · apply (prepare_scale_dvd_iff R s T _).2
    exact linear_den_dvd R s _ ((serviceDenLCM_dvd_iff R s _).1 (dvd_refl _))
  · apply (serviceDenLCM_dvd_iff R s _).2
    exact service_den_dvd R s _ ((prepare_scale_dvd_iff R s T _).1 (dvd_refl _))

theorem common_integrality_iff (R : RootedTree (Fin N)) (s : Fin N → ℚ) (D : ℕ) :
    (∀ v, v ≠ R.root → integralRat ((D : ℚ) * s v)) ↔
      ∀ v, v ≠ R.root → integralRat ((D : ℚ) * linearWeight R s v) := by
  simp only [integral_scaled_iff_den_dvd]
  exact ⟨linear_den_dvd R s D, service_den_dvd R s D⟩

theorem prepare_scale_le_service_product (R : RootedTree (Fin N))
    (s : Fin N → ℚ) (T : ℚ) :
    (prepare R s T).scale ≤ ∏ v ∈ Finset.univ.erase R.root, (s v).den := by
  classical
  rw [prepare_scale_eq_serviceDenLCM]
  apply Nat.le_of_dvd (Finset.prod_pos fun v _ => Rat.pos (s v))
  apply (serviceDenLCM_dvd_iff R s _).2
  intro v hv
  exact Finset.dvd_prod_of_mem (fun v => (s v).den)
    (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩)

theorem prepare_scale_eq_of_same_root (R Q : RootedTree (Fin N))
    (s : Fin N → ℚ) (T T' : ℚ) (hr : R.root = Q.root) :
    (prepare R s T).scale = (prepare Q s T').scale := by
  rw [prepare_scale_eq_serviceDenLCM, prepare_scale_eq_serviceDenLCM]
  simp only [serviceDenLCM, hr]

theorem prepare_scale_le_pow (R : RootedTree (Fin N)) (s : Fin N → ℚ)
    (T : ℚ) (b : ℕ) (hb : ∀ v, v ≠ R.root → (s v).den < 2 ^ b) :
    (prepare R s T).scale ≤ 2 ^ ((N - 1) * b) := by
  classical
  apply (prepare_scale_le_service_product R s T).trans
  calc
    (∏ v ∈ Finset.univ.erase R.root, (s v).den) ≤
        ∏ _v ∈ Finset.univ.erase R.root, 2 ^ b :=
      Finset.prod_le_prod' fun v hv => (hb v (Finset.mem_erase.mp hv).1).le
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

end UAVProof.TreeBudgetSubtreeResource
