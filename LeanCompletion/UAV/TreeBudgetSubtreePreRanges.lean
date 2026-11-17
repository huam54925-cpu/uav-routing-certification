import LeanCompletion.UAV.TreeBudgetSubtreePreBounds
import LeanCompletion.UAV.TreeBudgetSubtreePreCounts

/-! Exposed intermediate-range contracts for the charged scalar instructions.
Normalization never substitutes the final reduced size for raw products. -/
namespace UAVProof.TreeBudgetSubtreePre

theorem scaleNumC_erase (D : ℕ) (a : ℚ) :
    (scaleNumC D a).value = TreeBudgetSubtreeAutoScaleSeed.scaleNum D a := rfl

theorem floorBudgetC_erase (D : ℕ) (T : ℚ) :
    (floorBudgetC D T).value = TreeBudgetSubtreeInteger.floorBudget D T :=
  floorBudgetC_value D T

theorem index_size {N : ℕ} (v : Fin N) : v.val.size ≤ N :=
  (size_self_le v.val).trans v.isLt.le

theorem ratAddC_intermediates (a b : ℚ) :
    (a.num * (b.den : ℤ)).natAbs.size ≤ (ratAddC a b).width ∧
    (b.num * (a.den : ℤ)).natAbs.size ≤ (ratAddC a b).width ∧
    (a.num * b.den + b.num * a.den).natAbs.size ≤ (ratAddC a b).width ∧
    (a.den*b.den).size ≤ (ratAddC a b).width ∧
    (euclid (a.num * b.den + b.num * a.den).natAbs (a.den*b.den)).width ≤
      (ratAddC a b).width := by
  have hx := size_mul a.num.natAbs b.den
  have hy := size_mul b.num.natAbs a.den
  have hn := size_int_add (a.num * b.den) (b.num * a.den)
  have hd := size_mul a.den b.den
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at *
  rw [euclid_width]
  dsimp [ratAddC]
  omega

theorem lcmC_intermediates (a b : ℕ) :
    (a*b).size ≤ (lcmC a b).width ∧
    (euclid a b).width ≤ (lcmC a b).width ∧
    (a*b / (euclid a b).value).size ≤ (lcmC a b).width := by
  have hm := size_mul a b
  have hq := Nat.size_le_size (Nat.div_le_self (a*b) (euclid a b).value)
  rw [euclid_width]
  dsimp [lcmC]
  omega

theorem normalization_intermediates (n : ℤ) (d : ℕ) (hd : d ≠ 0) :
    (euclid n.natAbs d).width = (normalizeC n d hd).width ∧
    (normalizeC n d hd).value.num.natAbs.size ≤ (normalizeC n d hd).width ∧
    (normalizeC n d hd).value.den.size ≤ (normalizeC n d hd).width := by
  have hr := normalizeC_ranges n d hd
  have hn := Nat.size_le_size hr.1
  have hd' := Nat.size_le_size hr.2
  rw [euclid_width]
  exact ⟨rfl, hn.trans (le_max_left _ _), hd'.trans (le_max_right _ _)⟩

theorem negative_floor_correction (a d : ℕ) (hd : 0 < d) :
    (-(a : ℤ)) / (d : ℤ) = -((a / d : ℕ) : ℤ) -
      if a % d = 0 then 0 else 1 := by
  have hdi : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  rw [Int.neg_ediv]
  simp only [Int.natCast_ediv, Int.natCast_dvd_natCast,
    Int.sign_eq_one_of_pos hdi, Nat.dvd_iff_mod_eq_zero]

theorem floorBudgetC_intermediates (D : ℕ) (T : ℚ) :
    ((D : ℤ)*T.num).natAbs.size ≤ (floorBudgetC D T).width ∧
    (floorBudgetC D T).value.natAbs.size ≤ (floorBudgetC D T).width ∧
    (((D : ℤ)*T.num).natAbs / T.den + 1).size ≤ (floorBudgetC D T).width ∧
    ((D : ℤ)*T.num).natAbs % T.den < T.den := by
  have hp : ((D : ℤ)*T.num).natAbs.size ≤ D.size+T.num.natAbs.size := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using size_mul D T.num.natAbs
  have hq := Nat.size_le_size (Int.natAbs_ediv_le_natAbs ((D : ℤ)*T.num) (T.den : ℤ))
  have hqn := (Nat.size_le_size (Nat.div_le_self ((D : ℤ)*T.num).natAbs T.den)).trans hp
  have hc := size_add (((D : ℤ)*T.num).natAbs / T.den) 1
  have hcorr : (((D : ℤ)*T.num).natAbs / T.den + 1).size ≤
      D.size+T.num.natAbs.size+1 := by
    by_cases hz : ((D : ℤ)*T.num).natAbs / T.den = 0
    · simp [hz]
    · have hpos := Nat.size_pos.mpr (Nat.pos_of_ne_zero hz)
      simp only [Nat.size_one] at hc
      omega
  exact ⟨hp.trans (by dsimp [floorBudgetC]; omega),
    hq.trans (hp.trans (by dsimp [floorBudgetC]; omega)),
    hcorr.trans (le_max_left _ _), Nat.mod_lt _ T.pos⟩

/-- Elementary scalar instructions use the same padded tariff. Their values
are the specified mathematical operations; no runtime for Lean builtins is
assumed. A read returns an already materialized scalar, with index bits charged. -/
def compareC (a b : ℕ) : Run Bool := ⟨decide (a = b), 1, max a.size b.size⟩
def addC (a b : ℤ) : Run ℤ := ⟨a+b, 1, max a.natAbs.size b.natAbs.size+1⟩
def subC (a b : ℤ) : Run ℤ := ⟨a-b, 1, max a.natAbs.size b.natAbs.size+1⟩
def mulC (a b : ℤ) : Run ℤ := ⟨a*b, 1, a.natAbs.size+b.natAbs.size⟩
def divModC (a b : ℕ) : Run (ℕ × ℕ) := ⟨(a/b, a%b), 1, max a.size b.size⟩
def readC (index value : ℕ) : Run ℕ := ⟨value, 1, max index.size value.size⟩

theorem scalar_values (a b : ℤ) (x y : ℕ) :
    (compareC x y).value = decide (x=y) ∧ (addC a b).value = a+b ∧
    (subC a b).value = a-b ∧ (mulC a b).value = a*b ∧
    (divModC x y).value = (x/y, x%y) ∧ (readC x y).value = y := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scalar_ranges (a b : ℤ) (x y : ℕ) :
    (addC a b).value.natAbs.size ≤ (addC a b).width ∧
    (subC a b).value.natAbs.size ≤ (subC a b).width ∧
    (mulC a b).value.natAbs.size ≤ (mulC a b).width ∧
    (divModC x y).value.1.size ≤ (divModC x y).width ∧
    (divModC x y).value.2.size ≤ (divModC x y).width := by
  refine ⟨size_int_add a b, ?_, ?_, ?_, ?_⟩
  · simpa [subC, sub_eq_add_neg] using size_int_add a (-b)
  · simpa [mulC, Int.natAbs_mul] using size_mul a.natAbs b.natAbs
  · exact (Nat.size_le_size (Nat.div_le_self x y)).trans (le_max_left _ _)
  · exact (Nat.size_le_size (Nat.mod_le x y)).trans (le_max_left _ _)

theorem scalar_bitWork {α : Type} (value : α) (w : ℕ) :
    bitWork (charge value 1 w) = 32*(w+1)^2 := by simp [bitWork, charge]

theorem euclid_bitWork_le (a b : ℕ) :
    bitWork (euclid a b) ≤ 32*(max a.size b.size+1)^2*(8*a.size+1) :=
  bitWork_le _ _ _ (euclid_width a b).le (euclid_ops a b)

theorem normalizeC_bitWork_le (n : ℤ) (d : ℕ) (hd : d ≠ 0) :
    bitWork (normalizeC n d hd) ≤
      32*(max n.natAbs.size d.size+1)^2*(8*n.natAbs.size+5) := by
  apply bitWork_le _ _ _ le_rfl
  have h := euclid_ops n.natAbs d
  dsimp [normalizeC]
  omega

theorem ratAddC_bitWork_le (a c : ℚ) (b : ℕ) (ha : RatFits a b) (hc : RatFits c b) :
    bitWork (ratAddC a c) ≤ 32*(2*b+2)^2*(16*b+21) := by
  have h := ratAddC_bounds a c b ha hc
  simpa [Nat.add_assoc] using bitWork_le _ _ _ h.1 h.2.1

theorem lcmC_bitWork_le (a b : ℕ) :
    bitWork (lcmC a b) ≤ 32*(a.size+b.size+1)^2*(8*a.size+4) :=
  bitWork_le _ _ _ (lcmC_bounds a b).2.1.le (lcmC_bounds a b).1

theorem scaleNumC_bitWork (D : ℕ) (a : ℚ) :
    bitWork (scaleNumC D a) = 128*(max (D.size+a.num.natAbs.size) a.den.size+1)^2 := by
  simp only [bitWork, scaleNumC]
  ring

theorem floorBudgetC_bitWork (D : ℕ) (T : ℚ) :
    bitWork (floorBudgetC D T) =
      256*(max (D.size+T.num.natAbs.size+1) T.den.size+1)^2 := by
  simp only [bitWork, floorBudgetC]
  ring

end UAVProof.TreeBudgetSubtreePre
