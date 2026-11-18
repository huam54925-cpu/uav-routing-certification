import LeanCompletion.UAV.TreeBudgetSparseGeometry
import LeanCompletion.UAV.SparseNaturalCombination

/-! A0–A2: simultaneous box, input-bit and parity support bounds, connected
to the original certificate and its original Boolean checker. -/
namespace UAVProof.TreeBudgetSparse

open TreeFlowExistence TreeBudgetRow TreeBudgetPatterns TreeBudgetMatrix TreeBudgetCertificate
open SparseNaturalCombination
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Nonroot (R : RootedTree V) := {v : V // v ≠ R.root}

def augmented (R : RootedTree V) (H : V → ℕ) (s : V → ℚ) (T : ℚ)
    (p : Pattern R H s T) : Option (Nonroot R) → ℕ
  | none => 1
  | some v => values p.val v.val

def target (R : RootedTree V) (H : V → ℕ) (m : ℕ) : Option (Nonroot R) → ℕ
  | none => m
  | some v => H v.val

theorem matrix_iff_augmented_counts (R : RootedTree V) (H : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) : MatrixFeasible R H m s T ↔
      ∃ z, Feasible (augmented R H s T) (target R H m) z := by
  rw [matrix_iff_pattern_rows,
    family_iff_counts (fun p : Pattern R H s T => values p.val) H (fun v => v ≠ R.root) m]
  constructor
  · rintro ⟨z, hz, hc⟩
    refine ⟨z, ?_⟩
    rintro (_ | v)
    · simpa [augmented, target] using hz
    · exact hc v.val v.property
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa [augmented, target] using hz none, fun v hv => hz (some ⟨v, hv⟩)⟩

def parity (R : RootedTree V) (H : V → ℕ) (s : V → ℚ) (T : ℚ)
    (p : Pattern R H s T) (v : Nonroot R) : Fin 2 :=
  ⟨values p.val v.val % 2, Nat.mod_lt _ (by decide)⟩

def energy (R : RootedTree V) (H : V → ℕ) (s : V → ℚ) (T : ℚ)
    (p : Pattern R H s T) : ℕ := ∑ v : Nonroot R, (values p.val v.val) ^ 2

theorem midpoint_square_le (a b r : ℕ) (hr : 2 * r = a + b) :
    2 * r ^ 2 ≤ a ^ 2 + b ^ 2 := by
  have hr' : (2 : ℤ) * r = a + b := by exact_mod_cast hr
  have h : (2 : ℤ) * (r : ℤ) ^ 2 ≤ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℤ) - b)]
  exact_mod_cast h

theorem midpoint_square_lt (a b r : ℕ) (hr : 2 * r = a + b) (hne : a ≠ b) :
    2 * r ^ 2 < a ^ 2 + b ^ 2 := by
  have hr' : (2 : ℤ) * r = a + b := by exact_mod_cast hr
  have hn : (a : ℤ) - b ≠ 0 := by exact sub_ne_zero.mpr (by exact_mod_cast hne)
  have h : (2 : ℤ) * (r : ℤ) ^ 2 < (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hn]
  exact_mod_cast h

theorem patterns_differ_nonroot (R : RootedTree V) (H : V → ℕ) (s : V → ℚ) (T : ℚ)
    (p q : Pattern R H s T) (hne : p ≠ q) :
    ∃ v : Nonroot R, values p.val v.val ≠ values q.val v.val := by
  by_contra! h
  apply hne
  apply Subtype.ext
  funext v
  apply Fin.ext
  by_cases hv : v = R.root
  · subst v; exact (values_root p.val).trans (values_root q.val).symm
  · exact h ⟨v, hv⟩

theorem parity_midpoint_descent (R : RootedTree V) (H : V → ℕ) (s : V → ℚ) (T : ℚ)
    (p q : Pattern R H s T) (hne : p ≠ q) (he : parity R H s T p = parity R H s T q) :
    ∃ r, (∀ v, augmented R H s T p v + augmented R H s T q v =
      2 * augmented R H s T r v) ∧ 2 * energy R H s T r < energy R H s T p + energy R H s T q := by
  have hpar (v : V) : values p.val v % 2 = values q.val v % 2 := by
    by_cases hv : v = R.root
    · simp [hv]
    · exact congrArg Fin.val (congrFun he ⟨v, hv⟩)
  let r := midpointPattern R H s T p q hpar
  have hd (v : V) : 2 * values r.val v = values p.val v + values q.val v := by
    rw [midpointPattern_values]
    exact midpoint_double _ _ (hpar v)
  refine ⟨r, ?_, ?_⟩
  · rintro (_ | v)
    · simp [augmented]
    · exact (hd v.val).symm
  · simp only [energy, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_lt_sum
    · intro v _; exact midpoint_square_le _ _ _ (hd v.val)
    · obtain ⟨v, hv⟩ := patterns_differ_nonroot R H s T p q hne
      exact ⟨v, Finset.mem_univ _, midpoint_square_lt _ _ _ (hd v.val) hv⟩

theorem exists_parity_counts (R : RootedTree V) (H : V → ℕ) (m : ℕ) (s : V → ℚ) (T : ℚ)
    (hm : MatrixFeasible R H m s T) :
    ∃ z, Feasible (augmented R H s T) (target R H m) z ∧
      (support z).card ≤ 2 ^ Fintype.card (Nonroot R) := by
  obtain ⟨z, hz, hc⟩ := exists_key_bound (augmented R H s T) (target R H m)
    (parity R H s T) (energy R H s T) (parity_midpoint_descent R H s T)
    ((matrix_iff_augmented_counts R H m s T).mp hm)
  exact ⟨z, hz, by simpa using hc⟩

/-- Reselect a globally support-minimal representation after proving the parity
bound with a separate energy-minimal representation. -/
theorem exists_simultaneous_counts (R : RootedTree V) (H : V → ℕ) (m : ℕ) (s : V → ℚ) (T : ℚ)
    (hm : MatrixFeasible R H m s T) :
    ∃ z, Feasible (augmented R H s T) (target R H m) z ∧
      2 ^ (support z).card ≤ (m + 1) * ∏ v : Nonroot R, (H v.val + 1) ∧
      (support z).card ≤ Nat.size m + ∑ v : Nonroot R, Nat.size (H v.val) ∧
      (support z).card ≤ 2 ^ Fintype.card (Nonroot R) := by
  obtain ⟨z, hz, hmin⟩ := exists_minimizer (Feasible (augmented R H s T) (target R H m))
    (fun z => (support z).card) ((matrix_iff_augmented_counts R H m s T).mp hm)
  obtain ⟨w, hw, hpar⟩ := exists_parity_counts R H m s T hm
  refine ⟨z, hz, ?_, ?_, (hmin w hw).trans hpar⟩
  · simpa [target, Fintype.prod_option] using
      minimal_box_bound (augmented R H s T) (target R H m) z hz hmin none (fun _ => rfl)
  · simpa [target, Fintype.sum_option] using
      minimal_bits_bound (augmented R H s T) (target R H m) z hz hmin none (fun _ => rfl)

theorem sum_on_support {A : Type*} [Fintype A] [DecidableEq A] (z f : A → ℕ) :
    (∑ p : support z, z p.val * f p.val) = ∑ p, z p * f p := by
  rw [Finset.sum_coe_sort (support z) (fun p => z p * f p)]
  simp only [support, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : 0 < z p
  · simp [hp]
  · have hz : z p = 0 := by omega
    simp [hz]

theorem counts_to_reduced_certificate (R : RootedTree V) (H : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (z : Pattern R H s T → ℕ)
    (hz : Feasible (augmented R H s T) (target R H m) z) :
    ∃ C : Certificate V, C.size = (support z).card ∧
      checkCertificate R H m s T C = true ∧
      Function.Injective C.row ∧ (∀ i, 0 < C.count i) := by
  classical
  let e : Fin (support z).card ≃ support z :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_coe])
  let C : Certificate V := ⟨(support z).card, fun i => values (e i).val.val,
    fun i => z (e i).val⟩
  have hs (f : Pattern R H s T → ℕ) :
      (∑ i, z (e i).val * f (e i).val) = ∑ p, z p * f p := by
    exact (Equiv.sum_comp e (fun p : support z => z p.val * f p.val)).trans (sum_on_support z f)
  refine ⟨C, rfl, ?_, ?_, ?_⟩
  · rw [checkCertificate_eq_true_iff]
    refine ⟨fun i => ⟨values_root _, fun _ hv => values_le _ hv, (e i).val.property⟩, ?_, ?_⟩
    · have ht := hs (fun _ => 1)
      simpa [C, augmented, target] using ht.trans (hz none)
    · intro v hv
      exact (hs (fun p => values p.val v)).trans (hz (some ⟨v, hv⟩))
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    apply Subtype.ext
    funext v
    exact Fin.ext (congrFun hij v)
  · intro i
    exact (mem_support z (e i).val).mp (e i).property

/-- The first A-package deliverable: one reduced witness, the original checker,
and all three support bounds. No sign condition or positive-route assumption. -/
theorem exists_sparse_certificate (R : RootedTree V) (H : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hm : MatrixFeasible R H m s T) :
    ∃ C : Certificate V, checkCertificate R H m s T C = true ∧
      Function.Injective C.row ∧ (∀ i, 0 < C.count i) ∧
      2 ^ C.size ≤ (m + 1) * ∏ v : Nonroot R, (H v.val + 1) ∧
      C.size ≤ Nat.size m + ∑ v : Nonroot R, Nat.size (H v.val) ∧
      C.size ≤ 2 ^ Fintype.card (Nonroot R) := by
  obtain ⟨z, hz, hbox, hbits, hpar⟩ := exists_simultaneous_counts R H m s T hm
  obtain ⟨C, hc, hv, hi, hp⟩ := counts_to_reduced_certificate R H m s T z hz
  refine ⟨C, hv, hi, hp, ?_, ?_, ?_⟩
  · simpa only [hc] using hbox
  · simpa only [hc] using hbits
  · simpa only [hc] using hpar

theorem sparse_checker_complete (R : RootedTree V) (H : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) : MatrixFeasible R H m s T ↔
    ∃ C : Certificate V, checkCertificate R H m s T C = true ∧
      Function.Injective C.row ∧ (∀ i, 0 < C.count i) ∧
      2 ^ C.size ≤ (m + 1) * ∏ v : Nonroot R, (H v.val + 1) ∧
      C.size ≤ Nat.size m + ∑ v : Nonroot R, Nat.size (H v.val) ∧
      C.size ≤ 2 ^ Fintype.card (Nonroot R) := by
  constructor
  · exact exists_sparse_certificate R H m s T
  · rintro ⟨C, hc, _⟩
    exact valid_implies_matrix R H m s T C ((checkCertificate_eq_true_iff ..).mp hc)

end UAVProof.TreeBudgetSparse
