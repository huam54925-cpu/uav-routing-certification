import LeanCompletion.UAV.TreeBudgetPatterns
import LeanCompletion.UAV.TreeBudgetCriterion

/-! Exact factorization at the depot, with the original vertex type and signed fees. -/
namespace UAVProof.TreeBudgetRootFactorization
open TreeFlowExistence TreeFlowConnectivity TreeBudgetRow TreeBudgetMatrix
open TreeBudgetPatterns TreeBudgetCriterion
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev RootChild (R : RootedTree V) := {c : V // c ∈ children R R.root}

theorem child_spec (R : RootedTree V) (c : RootChild R) :
    c.val ≠ R.root ∧ R.parent c.val = R.root := (Finset.mem_filter.mp c.property).2

/-- At the root this returns the root; elsewhere it returns the first root child. -/
def rootBranch {V : Type*} [Fintype V] [DecidableEq V] (R : RootedTree V) (v : V) : V :=
  if v = R.root then R.root else
    if R.parent v = R.root then v else rootBranch R (R.parent v)
termination_by (∑ w, R.rank w) - R.rank v
decreasing_by
  classical
  have := R.parent_rank v (by assumption)
  have := rank_le_sum R (R.parent v)
  omega

@[simp] theorem rootBranch_root (R : RootedTree V) : rootBranch R R.root = R.root := by
  rw [rootBranch]; simp

@[simp] theorem rootBranch_child (R : RootedTree V) (c : RootChild R) :
    rootBranch R c.val = c.val := by
  rw [rootBranch]; simp [(child_spec R c).1, (child_spec R c).2]

theorem rootBranch_mem (R : RootedTree V) (v : V) (hv : v ≠ R.root) :
    rootBranch R v ∈ children R R.root := by
  rw [rootBranch, if_neg hv]
  split_ifs with hp
  · simp [children, hv, hp]
  · exact rootBranch_mem R (R.parent v) hp
termination_by (∑ w, R.rank w) - R.rank v
decreasing_by
  have := R.parent_rank v hv
  have := rank_le_sum R (R.parent v)
  omega

def InRootSubtree (R : RootedTree V) (c : RootChild R) (v : V) : Prop :=
  v ≠ R.root ∧ rootBranch R v = c.val

instance (R : RootedTree V) (c : RootChild R) (v : V) :
    Decidable (InRootSubtree R c v) := inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem subtree_self (R : RootedTree V) (c : RootChild R) :
    InRootSubtree R c c.val := ⟨(child_spec R c).1, rootBranch_child R c⟩

@[simp] theorem root_not_subtree (R : RootedTree V) (c : RootChild R) :
    ¬ InRootSubtree R c R.root := by simp [InRootSubtree]

theorem subtree_partition (R : RootedTree V) (v : V) (hv : v ≠ R.root) :
    ∃! c : RootChild R, InRootSubtree R c v := by
  refine ⟨⟨rootBranch R v, rootBranch_mem R v hv⟩, ⟨hv, rfl⟩, ?_⟩
  intro c hc
  exact Subtype.ext hc.2.symm

theorem subtree_disjoint (R : RootedTree V) {c d : RootChild R} {v : V}
    (hc : InRootSubtree R c v) (hd : InRootSubtree R d v) : c = d :=
  Subtype.ext (hc.2.symm.trans hd.2)

@[simp] theorem child_in_subtree_iff (R : RootedTree V) (c d : RootChild R) :
    InRootSubtree R c d.val ↔ d = c := by
  constructor
  · intro hh
    exact Subtype.ext ((rootBranch_child R d).symm.trans hh.2)
  · rintro rfl; exact subtree_self R _

theorem subtree_parent (R : RootedTree V) {c : RootChild R} {v : V}
    (hv : InRootSubtree R c v) (hne : v ≠ c.val) :
    InRootSubtree R c (R.parent v) := by
  have hp : R.parent v ≠ R.root := by
    intro hp
    have hb := hv.2
    rw [rootBranch, if_neg hv.1, if_pos hp] at hb
    exact hne hb
  have hb := hv.2
  rw [rootBranch, if_neg hv.1, if_neg hp] at hb
  exact ⟨hp, hb⟩

theorem subtree_child (R : RootedTree V) {c : RootChild R} {v w : V}
    (hv : InRootSubtree R c v) (hw : w ∈ children R v) : InRootSubtree R c w := by
  obtain ⟨hwr, hwp⟩ := (Finset.mem_filter.mp hw).2
  refine ⟨hwr, ?_⟩
  rw [rootBranch, if_neg hwr, hwp, if_neg hv.1]
  exact hv.2

theorem positive_at_rootBranch (R : RootedTree V) (n : V → ℕ)
    (ha : AncestorClosed R n) (v : V) (hv : v ≠ R.root) (hn : 0 < n v) :
    0 < n (rootBranch R v) := by
  rw [rootBranch, if_neg hv]
  split_ifs with hp
  · exact hn
  · exact positive_at_rootBranch R n ha (R.parent v) hp (ha v hv hn hp)
termination_by (∑ w, R.rank w) - R.rank v
decreasing_by
  have := R.parent_rank v hv
  have := rank_le_sum R (R.parent v)
  omega

theorem rootBranch_reached (R : RootedTree V) (v : V) (hv : v ≠ R.root) :
    ∃ k : ℕ, R.parent^[k] v = rootBranch R v := by
  rw [rootBranch, if_neg hv]
  split_ifs with hp
  · exact ⟨0, rfl⟩
  · obtain ⟨k, hk⟩ := rootBranch_reached R (R.parent v) hp
    exact ⟨k + 1, by simpa only [Function.iterate_succ_apply] using hk⟩
termination_by (∑ w, R.rank w) - R.rank v
decreasing_by
  have := R.parent_rank v hv
  have := rank_le_sum R (R.parent v)
  omega

theorem subtree_iff_parent_iterate (R : RootedTree V) (c : RootChild R) (v : V) :
    InRootSubtree R c v ↔ ∃ k : ℕ, R.parent^[k] v = c.val := by
  constructor
  · intro hv
    obtain ⟨k, hk⟩ := rootBranch_reached R v hv.1
    exact ⟨k, hk.trans hv.2⟩
  · rintro ⟨k, hk⟩
    induction k generalizing v with
    | zero =>
      change v = c.val at hk
      subst v
      exact subtree_self R c
    | succ k ih =>
      rw [Function.iterate_succ_apply] at hk
      have hp := ih (R.parent v) hk
      have hv : v ≠ R.root := by
        intro he; subst v; exact hp.1 R.parent_root
      refine ⟨hv, ?_⟩
      rw [rootBranch, if_neg hv, if_neg hp.1]
      exact hp.2

theorem pattern_unique_root_child (R : RootedTree V) (h : V → ℕ) (s : V → ℚ)
    (T : ℚ) (p : Pattern R h s T) : ∃! c : RootChild R, values p.val c.val = 1 := by
  have hs : ∑ c : RootChild R, values p.val c.val = 1 := by
    rw [Finset.sum_coe_sort]
    exact p.property.1
  have hpos : 0 < ∑ c : RootChild R, values p.val c.val := by omega
  obtain ⟨c, _, hc⟩ := Finset.sum_pos_iff.mp hpos
  have hle : values p.val c.val ≤ 1 := hs ▸
    Finset.single_le_sum (fun i _ => Nat.zero_le (values p.val i.val)) (Finset.mem_univ c)
  refine ⟨c, by omega, ?_⟩
  intro d hd
  by_contra hdc
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (show ({c, d} : Finset (RootChild R)) ⊆ Finset.univ from Finset.subset_univ _)
    (fun i _ _ => Nat.zero_le (values p.val i.val))
  have hcd : c ≠ d := Ne.symm hdc
  rw [Finset.sum_pair hcd, hs, hd] at hh
  omega

abbrev BranchPattern (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (c : RootChild R) := {p : Pattern R h s T // values p.val c.val = 1}

theorem pattern_support (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (c : RootChild R) (p : BranchPattern R h s T c) {v : V}
    (hp : 0 < values p.val.val v) : InRootSubtree R c v := by
  have hv : v ≠ R.root := by intro he; subst v; simp at hp
  let d : RootChild R := ⟨rootBranch R v, rootBranch_mem R v hv⟩
  have hd := positive_at_rootBranch R (values p.val.val) p.val.property.2.1 v hv hp
  have hs : ∑ a : RootChild R, values p.val.val a.val = 1 := by
    rw [Finset.sum_coe_sort]
    exact p.val.property.1
  have hle : values p.val.val d.val ≤ 1 :=
    (Finset.single_le_sum (fun a _ => Nat.zero_le (values p.val.val a.val))
      (Finset.mem_univ d)).trans hs.le
  have hd1 : values p.val.val d.val = 1 := by change 0 < values p.val.val d.val at hd; omega
  have he := (pattern_unique_root_child R h s T p.val).unique hd1 p.property
  exact ⟨hv, congrArg Subtype.val he⟩

theorem pattern_zero_outside (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (c : RootChild R) (p : BranchPattern R h s T c) {v : V}
    (hv : ¬ InRootSubtree R c v) : values p.val.val v = 0 := by
  by_contra hn
  exact hv (pattern_support R h s T c p (Nat.pos_of_ne_zero hn))

noncomputable def pattern_branch_equiv (R : RootedTree V) (h : V → ℕ)
    (s : V → ℚ) (T : ℚ) :
    (Σ c : RootChild R, BranchPattern R h s T c) ≃ Pattern R h s T := by
  classical
  apply Equiv.ofBijective (fun q => q.2.val)
  constructor
  · rintro ⟨c, p⟩ ⟨d, q⟩ he
    change p.val = q.val at he
    have hd : values p.val.val d.val = 1 := by rw [he]; exact q.property
    have hcd := (pattern_unique_root_child R h s T p.val).unique p.property hd
    subst d
    have hpq : p = q := Subtype.ext he
    subst q
    rfl
  · intro p
    obtain ⟨c, hc, _⟩ := pattern_unique_root_child R h s T p
    exact ⟨⟨c, ⟨p, hc⟩⟩, rfl⟩

@[simp] theorem pattern_branch_equiv_apply (R : RootedTree V) (h : V → ℕ)
    (s : V → ℚ) (T : ℚ) (q : Σ c : RootChild R, BranchPattern R h s T c) :
    pattern_branch_equiv R h s T q = q.2.val := rfl

def LocalCountsFeasible (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (c : RootChild R) : Prop :=
  ∃ z : BranchPattern R h s T c → ℕ,
    ∀ v, InRootSubtree R c v → ∑ p, z p * values p.val.val v = h v

theorem local_count_total (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (c : RootChild R) (z : BranchPattern R h s T c → ℕ)
    (hz : ∀ v, InRootSubtree R c v → ∑ p, z p * values p.val.val v = h v) :
    ∑ p, z p = h c.val := by
  calc
    ∑ p, z p = ∑ p, z p * values p.val.val c.val := by
      apply Finset.sum_congr rfl
      intro p _
      rw [p.property, Nat.mul_one]
    _ = h c.val := hz c.val (subtree_self R c)

theorem sum_branch_column (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (z : (c : RootChild R) → BranchPattern R h s T c → ℕ)
    (c : RootChild R) {v : V} (hv : InRootSubtree R c v) :
    (∑ d, ∑ p, z d p * values p.val.val v) = ∑ p, z c p * values p.val.val v := by
  classical
  apply Finset.sum_eq_single c
  · intro d _ hdc
    apply Finset.sum_eq_zero
    intro p _
    rw [pattern_zero_outside R h s T d p (fun hd => hdc (subtree_disjoint R hd hv)),
      Nat.mul_zero]
  · simp

theorem pattern_counts_iff_local_counts (R : RootedTree V) (h : V → ℕ)
    (s : V → ℚ) (T : ℚ) : PatternCountsFeasible R h s T ↔
    ∀ c : RootChild R, LocalCountsFeasible R h s T c := by
  classical
  let e := pattern_branch_equiv R h s T
  constructor
  · rintro ⟨z, hz⟩ c
    refine ⟨fun p => z p.val, fun v hv => ?_⟩
    calc
      _ = ∑ d, ∑ p : BranchPattern R h s T d, z p.val * values p.val.val v :=
        (sum_branch_column R h s T (fun _ p => z p.val) c hv).symm
      _ = ∑ p, z p * values p.val v := by
        exact (Fintype.sum_sigma (fun q : Σ c : RootChild R, BranchPattern R h s T c =>
          z q.2.val * values q.2.val.val v)).symm.trans
          (Equiv.sum_comp e (fun p => z p * values p.val v))
      _ = h v := hz v hv.1
  · intro hl
    choose z hz using hl
    refine ⟨fun p => z (e.symm p).1 (e.symm p).2, fun v hv => ?_⟩
    obtain ⟨c, hc, _⟩ := subtree_partition R v hv
    calc
      _ = ∑ q : Σ c : RootChild R, BranchPattern R h s T c,
          z q.1 q.2 * values q.2.val.val v := by
        rw [← Equiv.sum_comp e]
        apply Finset.sum_congr rfl
        intro q _
        change z (e.symm (e q)).1 (e.symm (e q)).2 * values (e q).val v = _
        rw [e.symm_apply_apply q]
        rfl
      _ = ∑ d, ∑ p, z d p * values p.val.val v := Fintype.sum_sigma _
      _ = ∑ p, z c p * values p.val.val v := sum_branch_column R h s T z c hc
      _ = h v := hz c v hc

theorem matrix_root_count (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hm : MatrixFeasible R h m s T) : m = rootCount R h := by
  obtain ⟨f, hf⟩ := (matrix_iff_pattern_rows R h m s T).mp hm
  have hk (r : Fin m) : rootCount R (values (f r).val) = 1 := (f r).property.1
  calc
    m = ∑ r : Fin m, rootCount R (values (f r).val) := by simp [hk]
    _ = rootCount R h := by
      unfold rootCount
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      exact hf c (Finset.mem_filter.mp hc).2.1

theorem matrix_iff_root_local (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) : MatrixFeasible R h m s T ↔
    m = rootCount R h ∧ ∀ c : RootChild R, LocalCountsFeasible R h s T c := by
  constructor
  · intro hm
    have he := matrix_root_count R h m s T hm
    exact ⟨he, (pattern_counts_iff_local_counts R h s T).mp
      ((matrix_iff_pattern_counts R h m s T he).mp hm)⟩
  · rintro ⟨he, hl⟩
    exact (matrix_iff_pattern_counts R h m s T he).mpr
      ((pattern_counts_iff_local_counts R h s T).mpr hl)

theorem matrix_normalize (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) :
    MatrixFeasible R (normalize R h) m s T ↔ MatrixFeasible R h m s T := by
  constructor
  · rintro ⟨n, hc, hk, ha, hb⟩
    exact ⟨n, fun v hv => by simpa [TreeBudgetPatterns.normalize, hv] using hc v hv, hk, ha, hb⟩
  · rintro ⟨n, hc, hk, ha, hb⟩
    exact ⟨n, fun v hv => by simpa [TreeBudgetPatterns.normalize, hv] using hc v hv, hk, ha, hb⟩

theorem compatible_root_count (R : RootedTree V) (d : V → ℕ) (m : ℕ)
    (hc : FlowCompatible R d m) :
    m = rootCount R (normalize R (fun v => (requirement R d v).toNat)) := by
  rw [normalize_rootCount]
  apply Int.natCast_inj.mp
  rw [rootCount, Nat.cast_sum]
  have hs : ∀ c ∈ children R R.root,
      ((requirement R d c).toNat : ℤ) = requirement R d c := by
    intro c hc'
    exact Int.toNat_of_nonneg (hc.1 c (Finset.mem_filter.mp hc').2.1)
  calc
    (m : ℤ) = ∑ c ∈ children R R.root, requirement R d c := by
      simpa only [children_eq] using hc.2
    _ = ∑ c ∈ children R R.root, ((requirement R d c).toNat : ℤ) := by
      apply Finset.sum_congr rfl
      intro c hc'
      exact (hs c hc').symm

theorem budget_routes_iff_root_local (R : RootedTree V) (d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) : BudgetRoutes R d m s T ↔
    FlowCompatible R d m ∧ ∀ c : RootChild R,
      LocalCountsFeasible R (normalize R (fun v => (requirement R d v).toNat)) s T c := by
  rw [budget_routes_iff, ← matrix_normalize, matrix_iff_root_local]
  constructor
  · rintro ⟨hc, _, hl⟩; exact ⟨hc, hl⟩
  · rintro ⟨hc, hl⟩; exact ⟨hc, compatible_root_count R d m hc, hl⟩

def branchMultiplicity (R : RootedTree V) (h : V → ℕ) (c : RootChild R) (v : V) : ℕ :=
  if InRootSubtree R c v then h v else 0

theorem branchMultiplicity_le (R : RootedTree V) (h : V → ℕ) (c : RootChild R) (v : V) :
    branchMultiplicity R h c v ≤ h v := by
  unfold branchMultiplicity; split_ifs <;> omega

theorem branch_root_count (R : RootedTree V) (h : V → ℕ) (c : RootChild R) :
    rootCount R (branchMultiplicity R h c) = h c.val := by
  change (∑ a ∈ children R R.root, branchMultiplicity R h c a) = _
  rw [Finset.sum_eq_single c.val]
  · simp [branchMultiplicity]
  · intro b hb hbc
    have hn : ¬ InRootSubtree R c b := by
      intro hh
      have he := (child_in_subtree_iff R c ⟨b, hb⟩).mp hh
      exact hbc (congrArg Subtype.val he)
    simp [branchMultiplicity, hn]
  · exact fun hn => (hn c.property).elim

omit [Fintype V] in
theorem normalize_values (R : RootedTree V) (h : V → ℕ) (p : BoundedRow R h) :
    normalize R (values p) = values p := by
  funext v
  by_cases hv : v = R.root <;> simp [TreeBudgetPatterns.normalize, hv]

def rebindPattern (R : RootedTree V) (h k : V → ℕ) (s : V → ℚ) (T : ℚ)
    (p : Pattern R h s T) (hb : ∀ v, v ≠ R.root → values p.val v ≤ k v) :
    Pattern R k s T :=
  ⟨packRow R k (values p.val) hb, by
    simpa only [ValidPattern, values_packRow, normalize_values] using p.property⟩

@[simp] theorem values_rebindPattern (R : RootedTree V) (h k : V → ℕ)
    (s : V → ℚ) (T : ℚ) (p : Pattern R h s T)
    (hb : ∀ v, v ≠ R.root → values p.val v ≤ k v) :
    values (rebindPattern R h k s T p hb).val = values p.val := by
  exact normalize_values R h p.val

theorem pattern_ext (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    {p q : Pattern R h s T} (he : values p.val = values q.val) : p = q := by
  apply Subtype.ext
  funext v
  exact Fin.ext (congrFun he v)

theorem masked_pattern_child (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (c : RootChild R) (p : Pattern R (branchMultiplicity R h c) s T) :
    values p.val c.val = 1 := by
  obtain ⟨d, hd, _⟩ := pattern_unique_root_child R _ s T p
  by_cases he : d = c
  · simpa [he] using hd
  · have hb := values_le p.val (child_spec R d).1
    have hn : ¬ InRootSubtree R c d.val := by simpa using he
    simp [branchMultiplicity, hn, hd] at hb

noncomputable def branch_pattern_equiv (R : RootedTree V) (h : V → ℕ)
    (s : V → ℚ) (T : ℚ) (c : RootChild R) :
    BranchPattern R h s T c ≃ Pattern R (branchMultiplicity R h c) s T := by
  let f (p : BranchPattern R h s T c) :=
    rebindPattern R h (branchMultiplicity R h c) s T p.val (fun v hv => by
      by_cases hc : InRootSubtree R c v
      · simpa [branchMultiplicity, hc] using values_le p.val.val hv
      · simp [branchMultiplicity, hc, pattern_zero_outside R h s T c p hc])
  apply Equiv.ofBijective f
  constructor
  · intro p q he
    apply Subtype.ext
    apply pattern_ext R h s T
    have hh := congrArg (fun a => values a.val) he
    simpa only [f, values_rebindPattern] using hh
  · intro q
    let p := rebindPattern R (branchMultiplicity R h c) h s T q
      (fun v hv => (values_le q.val hv).trans (branchMultiplicity_le R h c v))
    have hp : values p.val c.val = 1 := by
      simpa only [p, values_rebindPattern] using masked_pattern_child R h s T c q
    refine ⟨⟨p, hp⟩, ?_⟩
    apply pattern_ext R _ s T
    simp only [f, p, values_rebindPattern]

@[simp] theorem branch_pattern_equiv_values (R : RootedTree V) (h : V → ℕ)
    (s : V → ℚ) (T : ℚ) (c : RootChild R) (p : BranchPattern R h s T c) :
    values (branch_pattern_equiv R h s T c p).val = values p.val.val := by
  exact values_rebindPattern R h _ s T p.val _

theorem local_counts_iff_masked_counts (R : RootedTree V) (h : V → ℕ)
    (s : V → ℚ) (T : ℚ) (c : RootChild R) : LocalCountsFeasible R h s T c ↔
    PatternCountsFeasible R (branchMultiplicity R h c) s T := by
  classical
  let e := branch_pattern_equiv R h s T c
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨fun p => z (e.symm p), fun v hv => ?_⟩
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply, e, branch_pattern_equiv_values]
    by_cases hc : InRootSubtree R c v
    · simpa [branchMultiplicity, hc] using hz v hc
    · simp [branchMultiplicity, hc, pattern_zero_outside R h s T c _ hc]
  · rintro ⟨z, hz⟩
    refine ⟨fun p => z (e p), fun v hv => ?_⟩
    calc
      _ = ∑ p, z p * values p.val v := by
        simpa only [e, branch_pattern_equiv_values] using
          Equiv.sum_comp e (fun p => z p * values p.val v)
      _ = h v := by simpa [branchMultiplicity, hv] using hz v hv.1

theorem local_counts_iff_matrix (R : RootedTree V) (h : V → ℕ)
    (s : V → ℚ) (T : ℚ) (c : RootChild R) : LocalCountsFeasible R h s T c ↔
    MatrixFeasible R (branchMultiplicity R h c) (h c.val) s T :=
  (local_counts_iff_masked_counts R h s T c).trans
    (matrix_iff_pattern_counts R _ _ s T (branch_root_count R h c).symm).symm

theorem matrix_iff_branch_matrices (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) : MatrixFeasible R h m s T ↔
    m = rootCount R h ∧ ∀ c : RootChild R,
      MatrixFeasible R (branchMultiplicity R h c) (h c.val) s T := by
  simp only [matrix_iff_root_local R h m s T, ← local_counts_iff_matrix]

theorem zero_branch_iff (R : RootedTree V) (h : V → ℕ) (s : V → ℚ) (T : ℚ)
    (c : RootChild R) (hc : h c.val = 0) : LocalCountsFeasible R h s T c ↔
    ∀ v, InRootSubtree R c v → h v = 0 := by
  have hn (p : BranchPattern R h s T c) : False := by
    have hp := values_le p.val.val (child_spec R c).1
    rw [p.property, hc] at hp
    omega
  constructor
  · rintro ⟨z, hz⟩ v hv
    rw [← hz v hv]
    exact Finset.sum_eq_zero (fun p _ => (hn p).elim)
  · intro hh
    exact ⟨fun _ => 0, fun v hv => by simp [hh v hv]⟩

theorem root_only_matrix_iff (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hr : ∀ v, v = R.root) :
    MatrixFeasible R h m s T ↔ m = 0 := by
  have he : children R R.root = ∅ := by
    ext v
    simp [children, hr v]
  have hn (c : RootChild R) : False := (child_spec R c).1 (hr c.val)
  rw [matrix_iff_root_local]
  simp only [rootCount, he, Finset.sum_empty]
  exact ⟨fun h => h.1, fun h => ⟨h, fun c => (hn c).elim⟩⟩

theorem single_branch_matrix_iff (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (c : RootChild R) (hu : ∀ d : RootChild R, d = c) :
    MatrixFeasible R h m s T ↔ m = h c.val ∧ LocalCountsFeasible R h s T c := by
  have he : children R R.root = {c.val} := by
    ext v
    constructor
    · intro hv
      exact Finset.mem_singleton.mpr (congrArg Subtype.val (hu ⟨v, hv⟩))
    · intro hv
      simpa only [Finset.mem_singleton.mp hv] using c.property
  rw [matrix_iff_root_local]
  simp only [rootCount, he, Finset.sum_singleton]
  exact ⟨fun h => ⟨h.1, h.2 c⟩, fun h => ⟨h.1, fun d => by rw [hu d]; exact h.2⟩⟩

end UAVProof.TreeBudgetRootFactorization

#print axioms UAVProof.TreeBudgetRootFactorization.subtree_partition
#print axioms UAVProof.TreeBudgetRootFactorization.pattern_unique_root_child
#print axioms UAVProof.TreeBudgetRootFactorization.pattern_support
#print axioms UAVProof.TreeBudgetRootFactorization.pattern_branch_equiv
#print axioms UAVProof.TreeBudgetRootFactorization.local_count_total
#print axioms UAVProof.TreeBudgetRootFactorization.pattern_counts_iff_local_counts
#print axioms UAVProof.TreeBudgetRootFactorization.local_counts_iff_matrix
#print axioms UAVProof.TreeBudgetRootFactorization.matrix_iff_branch_matrices
#print axioms UAVProof.TreeBudgetRootFactorization.budget_routes_iff_root_local
#print axioms UAVProof.TreeBudgetRootFactorization.zero_branch_iff
#print axioms UAVProof.TreeBudgetRootFactorization.subtree_iff_parent_iterate
#print axioms UAVProof.TreeBudgetRootFactorization.root_only_matrix_iff
#print axioms UAVProof.TreeBudgetRootFactorization.single_branch_matrix_iff
