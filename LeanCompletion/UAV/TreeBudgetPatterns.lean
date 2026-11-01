import LeanCompletion.UAV.TreeBudgetMatrix

/-! Finite, root-normalized route patterns and their multiplicities.
The executable definitions use the supplied finite enumeration and parent function.
No sign assumption is imposed on service fees or the budget. -/
namespace UAVProof.TreeBudgetPatterns

open TreeFlowExistence TreeBudgetRow TreeBudgetMatrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def children (R : RootedTree V) (v : V) : Finset V :=
  Finset.univ.filter (fun w => w ≠ R.root ∧ R.parent w = v)

theorem children_eq (R : RootedTree V) (v : V) : children R v = R.children v := by
  ext w
  simp [children, RootedTree.mem_children]

def rootCount (R : RootedTree V) (n : V → ℕ) : ℕ :=
  ∑ w ∈ children R R.root, n w

def cost (R : RootedTree V) (n : V → ℕ) (s : V → ℚ) : ℚ :=
  ∑ v, if v = R.root then 0 else
    (s v + if R.parent v = R.root then 0 else s (R.parent v)) * (n v : ℚ)

theorem rootCount_eq (R : RootedTree V) (n : V → ℕ) :
    rootCount R n = rootDegree R n := by simp [rootCount, rootDegree, children_eq]

theorem cost_eq (R : RootedTree V) (n : V → ℕ) (s : V → ℚ) :
    cost R n s = rowCost R n s := (rowCost_linear R n s).symm

def normalize (R : RootedTree V) (n : V → ℕ) (v : V) : ℕ :=
  if v = R.root then 0 else n v

omit [Fintype V] in
@[simp] theorem normalize_root (R : RootedTree V) (n : V → ℕ) :
    normalize R n R.root = 0 := by simp [normalize]

omit [Fintype V] in
theorem normalize_nonroot (R : RootedTree V) (n : V → ℕ) {v : V}
    (hv : v ≠ R.root) : normalize R n v = n v := by simp [normalize, hv]

@[simp] theorem normalize_rootCount (R : RootedTree V) (n : V → ℕ) :
    rootCount R (normalize R n) = rootCount R n := by
  apply Finset.sum_congr rfl
  intro w hw
  exact normalize_nonroot R n (by simpa [children] using (Finset.mem_filter.mp hw).2.1)

@[simp] theorem normalize_cost (R : RootedTree V) (n : V → ℕ) (s : V → ℚ) :
    cost R (normalize R n) s = cost R n s := by
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = R.root <;> simp [normalize, hv]

omit [Fintype V] in
@[simp] theorem normalize_ancestor (R : RootedTree V) (n : V → ℕ) :
    AncestorClosed R (normalize R n) ↔ AncestorClosed R n := by
  simp only [AncestorClosed]
  constructor <;> intro h v hv hn hp
  · simpa [normalize, hp] using h v hv (by simpa [normalize, hv] using hn) hp
  · simpa [normalize, hp] using h v hv (by simpa [normalize, hv] using hn) hp

def bound (R : RootedTree V) (h : V → ℕ) (v : V) : ℕ :=
  if v = R.root then 0 else h v

abbrev BoundedRow (R : RootedTree V) (h : V → ℕ) := (v : V) → Fin (bound R h v + 1)

def values {R : RootedTree V} {h : V → ℕ} (p : BoundedRow R h) (v : V) : ℕ := p v

omit [Fintype V] in
@[simp] theorem values_root {R : RootedTree V} {h : V → ℕ} (p : BoundedRow R h) :
    values p R.root = 0 := by
  have hp := (p R.root).isLt
  simp only [bound] at hp
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hp)

omit [Fintype V] in
theorem values_le {R : RootedTree V} {h : V → ℕ} (p : BoundedRow R h)
    {v : V} (hv : v ≠ R.root) : values p v ≤ h v := by
  have hp := (p v).isLt
  simpa [bound, hv] using Nat.le_of_lt_succ hp

def ValidPattern (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (p : BoundedRow R h) : Prop :=
  rootCount R (values p) = 1 ∧ AncestorClosed R (values p) ∧ cost R (values p) s ≤ T

instance (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (p : BoundedRow R h) : Decidable (ValidPattern R h s T p) := by
  unfold ValidPattern AncestorClosed
  infer_instance

abbrev Pattern (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ) :=
  {p : BoundedRow R h // ValidPattern R h s T p}

theorem card_pattern_le (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ) :
    Fintype.card (Pattern R h s T) ≤ ∏ v, (bound R h v + 1) := by
  calc
    _ ≤ Fintype.card (BoundedRow R h) := Fintype.card_subtype_le _
    _ = _ := by
      change Fintype.card ((v : V) → Fin (bound R h v + 1)) = _
      simp only [Fintype.card_pi, Fintype.card_fin]

omit [Fintype V] [DecidableEq V] in
theorem row_le_column {m : ℕ} (n : Fin m → V → ℕ) (h : V → ℕ) (r : Fin m) (v : V)
    (hc : ∑ i, n i v = h v) : n r v ≤ h v := by
  rw [← hc]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (n i v)) (Finset.mem_univ r)

def packRow (R : RootedTree V) (h n : V → ℕ)
    (hn : ∀ v, v ≠ R.root → n v ≤ h v) : BoundedRow R h := fun v =>
  ⟨normalize R n v, by
    by_cases hv : v = R.root
    · simp [normalize, bound, hv]
    · simpa [normalize, bound, hv] using Nat.lt_succ_of_le (hn v hv)⟩

omit [Fintype V] in
@[simp] theorem values_packRow (R : RootedTree V) (h n : V → ℕ)
    (hn : ∀ v, v ≠ R.root → n v ≤ h v) : values (packRow R h n hn) = normalize R n := rfl

theorem matrix_iff_pattern_rows (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) : MatrixFeasible R h m s T ↔
      ∃ f : Fin m → Pattern R h s T,
        ∀ v, v ≠ R.root → ∑ r, values (f r).val v = h v := by
  constructor
  · rintro ⟨n, hc, hk, ha, hb⟩
    let p (r : Fin m) := packRow R h (n r) (fun v hv => row_le_column n h r v (hc v hv))
    have hp (r : Fin m) : ValidPattern R h s T (p r) := by
      change rootCount R (normalize R (n r)) = 1 ∧
        AncestorClosed R (normalize R (n r)) ∧ cost R (normalize R (n r)) s ≤ T
      rw [normalize_rootCount, normalize_ancestor, normalize_cost, rootCount_eq, cost_eq]
      exact ⟨hk r, ha r, hb r⟩
    refine ⟨fun r => ⟨p r, hp r⟩, ?_⟩
    intro v hv
    simpa [p, normalize, hv] using hc v hv
  · rintro ⟨f, hc⟩
    exact ⟨fun r => values (f r).val, hc,
      fun r => (rootCount_eq R _).symm.trans (f r).property.1,
      fun r => (f r).property.2.1,
      fun r => (cost_eq R _ s).symm.le.trans (f r).property.2.2⟩

omit [Fintype V] [DecidableEq V] in
/-- Count equal rows, or expand a count into a dependent family of copies. -/
theorem family_iff_counts {A : Type*} [Fintype A] [DecidableEq A]
    (a : A → V → ℕ) (h : V → ℕ) (P : V → Prop) (m : ℕ) :
    (∃ f : Fin m → A, ∀ v, P v → ∑ r, a (f r) v = h v) ↔
    ∃ z : A → ℕ, (∑ p, z p) = m ∧ ∀ v, P v → ∑ p, z p * a p v = h v := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    let z : A → ℕ := fun p => ∑ r : Fin m, if f r = p then 1 else 0
    refine ⟨z, ?_, ?_⟩
    · simp only [z]
      rw [Finset.sum_comm]
      simp
    · intro v hv
      calc
        ∑ p, z p * a p v = ∑ r : Fin m, ∑ p, (if f r = p then 1 else 0) * a p v := by
          simp only [z, Finset.sum_mul]
          rw [Finset.sum_comm]
        _ = ∑ r, a (f r) v := by simp
        _ = h v := hf v hv
  · rintro ⟨z, hz, hc⟩
    let I := (p : A) × Fin (z p)
    have hcard : Fintype.card I = m := by simp [I, hz]
    let e : Fin m ≃ I := Fintype.equivOfCardEq (by simpa using hcard.symm)
    refine ⟨fun r => (e r).1, ?_⟩
    intro v hv
    calc
      ∑ r, a (e r).1 v = ∑ i : I, a i.1 v := Equiv.sum_comp e (fun i : I => a i.1 v)
      _ = ∑ p, z p * a p v := by rw [Fintype.sum_sigma]; simp
      _ = h v := hc v hv

def PatternCountsFeasible (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ) : Prop :=
  ∃ z : Pattern R h s T → ℕ, ∀ v, v ≠ R.root → ∑ p, z p * values p.val v = h v

theorem pattern_count_total (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (z : Pattern R h s T → ℕ)
    (hz : ∀ v, v ≠ R.root → ∑ p, z p * values p.val v = h v) :
    (∑ p, z p) = rootCount R h := by
  calc
    ∑ p, z p = ∑ p, z p * rootCount R (values p.val) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [p.property.1, Nat.mul_one]
    _ = ∑ w ∈ children R R.root, ∑ p, z p * values p.val w := by
      simp only [rootCount, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = rootCount R h := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hz w (Finset.mem_filter.mp hw).2.1

theorem matrix_iff_pattern_counts (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hm : m = rootCount R h) :
    MatrixFeasible R h m s T ↔ PatternCountsFeasible R h s T := by
  rw [matrix_iff_pattern_rows,
    family_iff_counts (fun p : Pattern R h s T => values p.val) h (fun v => v ≠ R.root) m]
  constructor
  · rintro ⟨z, _, hz⟩; exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, (pattern_count_total R h s T z hz).trans hm.symm, hz⟩

theorem pattern_count_le (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (z : Pattern R h s T → ℕ)
    (hz : ∀ v, v ≠ R.root → ∑ p, z p * values p.val v = h v) (p : Pattern R h s T) :
    z p ≤ rootCount R h := by
  rw [← pattern_count_total R h s T z hz]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)

end UAVProof.TreeBudgetPatterns

#print axioms UAVProof.TreeBudgetPatterns.matrix_iff_pattern_counts
#print axioms UAVProof.TreeBudgetPatterns.pattern_count_total
#print axioms UAVProof.TreeBudgetPatterns.card_pattern_le
