import LeanCompletion.UAV.TreeBudgetCertificate
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Integer linear description and midpoint closure of bounded route patterns.
Service fees and budgets are arbitrary rationals. The root is not assumed to be
the first vertex, and its coordinate is normalized to zero. -/
namespace UAVProof.TreeBudgetSparse

open TreeFlowExistence TreeBudgetRow TreeBudgetPatterns TreeBudgetCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem parent_guard_iff (x y cap : ℕ) (hx : x ≤ cap) :
    x ≤ cap * y ↔ (0 < x → 0 < y) := by
  constructor
  · intro hxy hpos
    by_contra hnot
    have hy : y = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hy, Nat.mul_zero] at hxy
    omega
  · intro h
    by_cases hz : x = 0
    · simp [hz]
    · exact hx.trans (by simpa using Nat.mul_le_mul_left cap (h (Nat.pos_of_ne_zero hz)))

theorem ancestorClosed_iff_linear (R : RootedTree V) (H p : V → ℕ)
    (hp : ∀ v, v ≠ R.root → p v ≤ H v) :
    AncestorClosed R p ↔ ∀ v, v ≠ R.root → R.parent v ≠ R.root →
      p v ≤ H v * p (R.parent v) := by
  constructor
  · intro ha v hv hparent
    exact (parent_guard_iff _ _ _ (hp v hv)).mpr (fun hpos => ha v hv hpos hparent)
  · intro hl v hv hpos hparent
    exact (parent_guard_iff _ _ _ (hp v hv)).mp (hl v hv hparent) hpos

/-- Rational linear constraints, evaluated on an arbitrary rational vector. -/
def InPolytope (R : RootedTree V) (H : V → ℕ) (s : V → ℚ) (T : ℚ)
    (p : V → ℚ) : Prop :=
  p R.root = 0 ∧
  (∀ v, v ≠ R.root → 0 ≤ p v ∧ p v ≤ H v) ∧
  (∑ v ∈ children R R.root, p v) = 1 ∧
  (∀ v, v ≠ R.root → R.parent v ≠ R.root → p v ≤ (H v : ℚ) * p (R.parent v)) ∧
  (∑ v, if v = R.root then 0 else
    (s v + if R.parent v = R.root then 0 else s (R.parent v)) * p v) ≤ T

theorem rowValid_iff_polytope_integer (R : RootedTree V) (H p : V → ℕ)
    (s : V → ℚ) (T : ℚ) :
    RowValid R H s T p ↔ InPolytope R H s T (fun v => (p v : ℚ)) := by
  unfold RowValid InPolytope
  dsimp only
  constructor
  · rintro ⟨hr, hb, hk, ha, hc⟩
    refine ⟨by exact_mod_cast hr, fun v hv => ⟨by positivity, by exact_mod_cast hb v hv⟩,
      ?_, ?_, hc⟩
    · simp only [rootCount] at hk
      exact_mod_cast hk
    · intro v hv hp
      exact_mod_cast (ancestorClosed_iff_linear R H p hb).mp ha v hv hp
  · rintro ⟨hr, hb, hk, ha, hc⟩
    have hb' : ∀ v, v ≠ R.root → p v ≤ H v := fun v hv => by exact_mod_cast (hb v hv).2
    refine ⟨by exact_mod_cast hr, hb', ?_, (ancestorClosed_iff_linear R H p hb').mpr ?_, hc⟩
    · unfold rootCount
      exact_mod_cast hk
    · intro v hv hp
      exact_mod_cast ha v hv hp

theorem pattern_iff_polytope_integer (R : RootedTree V) (H : V → ℕ)
    (s : V → ℚ) (T : ℚ) (p : BoundedRow R H) :
    ValidPattern R H s T p ↔ InPolytope R H s T (fun v => (values p v : ℚ)) := by
  rw [← rowValid_iff_polytope_integer]
  exact ⟨fun hp => ⟨values_root p, fun _ hv => values_le p hv, hp⟩, fun hp => hp.2.2⟩

theorem midpoint_double (a b : ℕ) (hparity : a % 2 = b % 2) :
    2 * ((a + b) / 2) = a + b := by omega

theorem midpoint_le (a b cap : ℕ) (ha : a ≤ cap) (hb : b ≤ cap) :
    (a + b) / 2 ≤ cap := by omega

def midpoint (p q : V → ℕ) (v : V) : ℕ := (p v + q v) / 2

theorem midpoint_cost (R : RootedTree V) (p q : V → ℕ) (s : V → ℚ)
    (he : ∀ v, p v % 2 = q v % 2) :
    2 * cost R (midpoint p q) s = cost R p s + cost R q s := by
  unfold cost
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = R.root
  · simp [hv]
  · simp only [hv, if_false]
    have hm : (2 : ℚ) * midpoint p q v = (p v : ℚ) + q v := by
      exact_mod_cast midpoint_double (p v) (q v) (he v)
    linear_combination (s v + if R.parent v = R.root then 0 else s (R.parent v)) * hm

theorem midpoint_rowValid (R : RootedTree V) (H p q : V → ℕ) (s : V → ℚ) (T : ℚ)
    (hp : RowValid R H s T p) (hq : RowValid R H s T q)
    (he : ∀ v, p v % 2 = q v % 2) : RowValid R H s T (midpoint p q) := by
  have hd (v : V) : 2 * midpoint p q v = p v + q v := midpoint_double _ _ (he v)
  have hb (v : V) (hv : v ≠ R.root) : midpoint p q v ≤ H v :=
    midpoint_le _ _ _ (hp.2.1 v hv) (hq.2.1 v hv)
  refine ⟨by simp [midpoint, hp.1, hq.1], hb, ?_, ?_, ?_⟩
  · have hs : 2 * rootCount R (midpoint p q) = rootCount R p + rootCount R q := by
      simp only [rootCount, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun v _ => hd v)
    rw [hp.2.2.1, hq.2.2.1] at hs
    omega
  · apply (ancestorClosed_iff_linear R H _ hb).mpr
    intro v hv hpar
    have h1 := (ancestorClosed_iff_linear R H p hp.2.1).mp hp.2.2.2.1 v hv hpar
    have h2 := (ancestorClosed_iff_linear R H q hq.2.1).mp hq.2.2.2.1 v hv hpar
    have h3 := hd v
    have h4 := hd (R.parent v)
    nlinarith
  · have hc := midpoint_cost R p q s he
    linarith [hp.2.2.2.2, hq.2.2.2.2]

def midpointPattern (R : RootedTree V) (H : V → ℕ) (s : V → ℚ) (T : ℚ)
    (p q : Pattern R H s T) (he : ∀ v, values p.val v % 2 = values q.val v % 2) :
    Pattern R H s T := by
  let r := midpoint (values p.val) (values q.val)
  have hr : RowValid R H s T r := midpoint_rowValid R H _ _ s T
    ⟨values_root _, fun _ hv => values_le _ hv, p.property⟩
    ⟨values_root _, fun _ hv => values_le _ hv, q.property⟩ he
  refine ⟨packRow R H r hr.2.1, ?_⟩
  simpa only [ValidPattern, values_packRow, normalize_rootCount, normalize_ancestor,
    normalize_cost] using hr.2.2

@[simp] theorem midpointPattern_values (R : RootedTree V) (H : V → ℕ) (s : V → ℚ) (T : ℚ)
    (p q : Pattern R H s T) (he : ∀ v, values p.val v % 2 = values q.val v % 2) (v : V) :
    values (midpointPattern R H s T p q he).val v = midpoint (values p.val) (values q.val) v := by
  change TreeBudgetPatterns.normalize R _ v = _
  by_cases hv : v = R.root <;> simp [TreeBudgetPatterns.normalize, hv, midpoint]

theorem square_identity (a b : ℤ) :
    2 * (a * a + b * b) = (a + b) * (a + b) + (a - b) * (a - b) := by ring

end UAVProof.TreeBudgetSparse
