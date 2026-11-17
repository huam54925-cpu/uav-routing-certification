import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
H arithmetic reference and its explicitly padded charging semantics.
`Run.ops` counts scalar instructions, reads/copies and list control; `width`
is a conservative operand/result width. Every instruction in one run is charged
32*(width+1)^2 bit units. This is a mathematical charging model, NOT a claim
about Lean's built-in arithmetic, allocation, or compiled elapsed time.
The two observation fields are ghost instrumentation, not executable counters
whose implementation is silently being included in the bound.
-/
namespace UAVProof.TreeBudgetSubtreePre

structure Run (α : Type) where
  value : α
  ops : ℕ
  width : ℕ

def bitWork {α : Type} (r : Run α) : ℕ := 32 * (r.width + 1)^2 * r.ops

def charge {α : Type} (value : α) (ops width : ℕ) : Run α := ⟨value, ops, width⟩

def after {α β : Type} (a : Run α) (b : Run β) : Run β :=
  ⟨b.value, a.ops + b.ops, max a.width b.width⟩

theorem bitWork_le {α : Type} (r : Run α) (W C : ℕ)
    (hw : r.width ≤ W) (hc : r.ops ≤ C) : bitWork r ≤ 32 * (W + 1)^2 * C := by
  unfold bitWork
  gcongr

theorem size_mul (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem size_add (a b : ℕ) : (a + b).size ≤ max a.size b.size + 1 := by
  apply Nat.size_le.mpr
  have ha := Nat.size_le.mp (le_max_left a.size b.size)
  have hb := Nat.size_le.mp (le_max_right a.size b.size)
  rw [pow_succ]
  omega

theorem size_int_add (a b : ℤ) : (a + b).natAbs.size ≤ max a.natAbs.size b.natAbs.size + 1 :=
  (Nat.size_le_size (Int.natAbs_add_le a b)).trans (size_add _ _)

theorem size_self_le (n : ℕ) : n.size ≤ n := by
  apply Nat.size_le.mpr
  exact Nat.lt_two_pow_self

/-- A single Euclidean execution: comparison, divmod and two scalar moves per
nonterminal iteration, one final zero comparison. The quotient is part of the
divmod primitive even though only the remainder is retained. -/
def euclid (a b : ℕ) : Run ℕ :=
  if h : a = 0 then ⟨b, 1, b.size⟩
  else
    let r := euclid (b % a) a
    ⟨r.value, r.ops + 4, max a.size (max b.size r.width)⟩
termination_by a
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

@[simp] theorem euclid_value (a b : ℕ) : (euclid a b).value = a.gcd b := by
  rw [euclid]
  split
  · rename_i h; simp [h]
  · dsimp only
    rw [euclid_value]
    exact (Nat.gcd_rec a b).symm
termination_by a
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by assumption))

theorem euclid_width (a b : ℕ) : (euclid a b).width = max a.size b.size := by
  rw [euclid]
  split
  · rename_i h; simp [h]
  · dsimp only
    rw [euclid_width]
    have hr := Nat.size_le_size (Nat.mod_le b a)
    omega
termination_by a
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by assumption))

theorem euclid_step_ranges (a b : ℕ) (ha : 0 < a) :
    b % a < a ∧ b % a ≤ b ∧ b / a ≤ b ∧ (b / a) * a + b % a = b := by
  exact ⟨Nat.mod_lt _ ha, Nat.mod_le _ _, Nat.div_le_self _ _, Nat.div_add_mod' _ _⟩

/-- In two Euclidean steps the first operand loses at least one bit. -/
theorem two_remainders_lt (a b k : ℕ) (ha : a < 2 ^ (k + 1))
    (hr : 0 < b % a) : a % (b % a) < 2^k := by
  by_cases hz : a = 0
  · simp [hz]
  let r := b % a
  have hrem : a % r < r := Nat.mod_lt _ hr
  by_cases hsmall : r ≤ 2^k
  · exact hrem.trans_le hsmall
  · have har : r ≤ a := (Nat.mod_lt b (Nat.pos_of_ne_zero hz)).le
    have hs : a - r < 2^k := by rw [pow_succ] at ha; omega
    rw [Nat.mod_eq_sub_mod har, Nat.mod_eq_of_lt (by omega : a - r < r)]
    exact hs

theorem euclid_ops_pow (k a b : ℕ) (ha : a < 2 ^ k) : (euclid a b).ops ≤ 8*k+1 := by
  induction k generalizing a b with
  | zero =>
    have hz : a = 0 := by simpa using ha
    simp [hz, euclid]
  | succ k ih =>
    by_cases hz : a = 0
    · simp [hz, euclid]
    · rw [euclid, dif_neg hz]
      by_cases hr : b % a = 0
      · simp [hr, euclid]; omega
      · rw [euclid, dif_neg hr]
        have hh := ih (a % (b % a)) (b % a) (two_remainders_lt a b k ha (by omega))
        dsimp only
        omega

theorem euclid_ops (a b : ℕ) : (euclid a b).ops ≤ 8*a.size+1 :=
  euclid_ops_pow a.size a b (Nat.lt_size_self a)

/-- Reuses the computed gcd in the canonical constructor. Proof arguments are
erased; there is no second gcd computation to obtain the normalized value. -/
def normalizeC (n : ℤ) (d : ℕ) (hd : d ≠ 0) : Run ℚ :=
  let g := euclid n.natAbs d
  let q : ℚ := ⟨n / g.value, d / g.value,
    Rat.normalize.den_nz hd (euclid_value _ _),
    Rat.normalize.reduced hd (euclid_value _ _)⟩
  ⟨q, g.ops + 4, max n.natAbs.size d.size⟩

@[simp] theorem normalizeC_value (n : ℤ) (d : ℕ) (hd : d ≠ 0) :
    (normalizeC n d hd).value = Rat.normalize n d hd := by
  simp [normalizeC, Rat.normalize_eq]

theorem normalizeC_ranges (n : ℤ) (d : ℕ) (hd : d ≠ 0) :
    (normalizeC n d hd).value.num.natAbs ≤ n.natAbs ∧
    (normalizeC n d hd).value.den ≤ d := by
  rw [normalizeC_value, Rat.num_normalize, Rat.den_normalize]
  rw [Int.natAbs_ediv_of_dvd (Rat.normalize.dvd_num rfl), Int.natAbs_natCast]
  exact ⟨Nat.div_le_self _ _, Nat.div_le_self _ _⟩

def ratAddC (a b : ℚ) : Run ℚ :=
  let x := a.num * (b.den : ℤ)
  let y := b.num * (a.den : ℤ)
  let n := x + y
  let d := a.den * b.den
  let q := normalizeC n d (Nat.mul_ne_zero a.den_nz b.den_nz)
  ⟨q.value, q.ops + 8,
    max (max (a.num.natAbs.size + b.den.size) (b.num.natAbs.size + a.den.size) + 1)
      (a.den.size + b.den.size)⟩

@[simp] theorem ratAddC_value (a b : ℚ) : (ratAddC a b).value = a + b := by
  simp only [ratAddC, normalizeC_value, Rat.add_def]

def RatFits (q : ℚ) (b : ℕ) : Prop := q.num.natAbs.size ≤ b ∧ q.den.size ≤ b

theorem ratAddC_bounds (a c : ℚ) (b : ℕ) (ha : RatFits a b) (hc : RatFits c b) :
    (ratAddC a c).width ≤ 2*b+1 ∧ (ratAddC a c).ops ≤ 16*b+21 ∧
    RatFits (ratAddC a c).value (2*b+1) := by
  have hx : (a.num * (c.den : ℤ)).natAbs.size ≤ 2*b := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      (size_mul a.num.natAbs c.den).trans (by dsimp [RatFits] at ha hc; omega)
  have hy : (c.num * (a.den : ℤ)).natAbs.size ≤ 2*b := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      (size_mul c.num.natAbs a.den).trans (by dsimp [RatFits] at ha hc; omega)
  have hn := (size_int_add (a.num * c.den) (c.num * a.den)).trans
    (by omega : max (a.num * (c.den : ℤ)).natAbs.size (c.num * (a.den : ℤ)).natAbs.size + 1 ≤ 2*b+1)
  have hd := (size_mul a.den c.den).trans
    (by dsimp [RatFits] at ha hc; omega : a.den.size + c.den.size ≤ 2*b+1)
  have hg := euclid_ops (a.num * c.den + c.num * a.den).natAbs (a.den*c.den)
  have hr := normalizeC_ranges (a.num * c.den + c.num * a.den) (a.den*c.den)
    (Nat.mul_ne_zero a.den_nz c.den_nz)
  have hn' := (Nat.size_le_size hr.1).trans hn
  have hd' := (Nat.size_le_size hr.2).trans hd
  dsimp only [ratAddC, normalizeC, RatFits] at *
  omega

def lcmC (a b : ℕ) : Run ℕ :=
  let g := euclid a b
  ⟨a * b / g.value, g.ops + 3, a.size + b.size⟩

@[simp] theorem lcmC_value (a b : ℕ) : (lcmC a b).value = a.lcm b := by
  simp [lcmC, Nat.lcm]

theorem lcmC_bounds (a b : ℕ) :
    (lcmC a b).ops ≤ 8*a.size+4 ∧ (lcmC a b).width = a.size+b.size ∧
    (lcmC a b).value.size ≤ a.size+b.size := by
  have he := euclid_ops a b
  exact ⟨by dsimp [lcmC]; omega, rfl,
    (Nat.size_le_size (Nat.div_le_self _ _)).trans (size_mul _ _)⟩

def scaleNumC (D : ℕ) (a : ℚ) : Run ℤ :=
  let q := D / a.den
  ⟨(q : ℤ) * a.num, 4, max (D.size + a.num.natAbs.size) a.den.size⟩

theorem scaleNumC_ranges (D : ℕ) (a : ℚ) :
    D / a.den ≤ D ∧ (scaleNumC D a).value.natAbs.size ≤ D.size + a.num.natAbs.size := by
  refine ⟨Nat.div_le_self _ _, ?_⟩
  change (((D / a.den : ℕ) : ℤ) * a.num).natAbs.size ≤ _
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  exact (size_mul _ _).trans (Nat.add_le_add_right (Nat.size_le_size (Nat.div_le_self _ _)) _)

/-- Signed Euclidean division is a charged primitive. It includes the sign,
nonzero-remainder test and negative-floor correction in its eight instructions.
This avoids constructing/normalizing the rational product D*T. -/
def floorBudgetC (D : ℕ) (T : ℚ) : Run ℤ :=
  let n := (D : ℤ) * T.num
  ⟨n / (T.den : ℤ), 8, max (D.size + T.num.natAbs.size + 1) T.den.size⟩

theorem floorBudgetC_value (D : ℕ) (T : ℚ) :
    (floorBudgetC D T).value = ⌊(D : ℚ) * T⌋ := by
  change ((D : ℤ) * T.num) / (T.den : ℤ) = _
  rw [← Rat.floor_intCast_div_natCast]
  congr 1
  simp only [Int.cast_mul, Int.cast_natCast, mul_div_assoc, Rat.num_div_den]

theorem floorBudgetC_range (D : ℕ) (T : ℚ) :
    (floorBudgetC D T).value.natAbs ≤ D * T.num.natAbs + 1 := by
  have h := Int.natAbs_ediv_le_natAbs ((D : ℤ) * T.num) (T.den : ℤ)
  have hh : (floorBudgetC D T).value.natAbs ≤ D * T.num.natAbs := by
    simpa only [floorBudgetC, Int.natAbs_mul, Int.natAbs_natCast] using h
  omega

end UAVProof.TreeBudgetSubtreePre
