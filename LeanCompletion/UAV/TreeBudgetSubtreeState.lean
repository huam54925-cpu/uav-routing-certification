import LeanCompletion.UAV.TreeBudgetMatrix

/-! Independent local matrix semantics for arbitrary internal subtrees.
Rows keep their global route labels. No budget or root-degree constraint is
imposed locally, and service costs may be signed. -/
namespace UAVProof.TreeBudgetSubtreeState
open TreeFlowExistence TreeBudgetRow
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Descendants, including the top vertex, defined without any DP state. -/
inductive InSubtree (R : RootedTree V) (v : V) : V → Prop
  | self : InSubtree R v v
  | step {x : V} : x ≠ R.root → InSubtree R v (R.parent x) → InSubtree R v x

omit [Fintype V] [DecidableEq V] in
theorem InSubtree.rank_le {R : RootedTree V} {v x : V}
    (hx : InSubtree R v x) : R.rank x ≤ R.rank v := by
  induction hx with
  | self => exact le_rfl
  | step hx hp ih => exact (R.parent_rank _ hx).le.trans ih

omit [Fintype V] [DecidableEq V] in
theorem InSubtree.trans {R : RootedTree V} {v u x : V}
    (hu : InSubtree R v u) (hx : InSubtree R u x) : InSubtree R v x := by
  induction hx with
  | self => exact hu
  | step hx hp ih => exact .step hx ih

omit [Fintype V] [DecidableEq V] in
theorem parent_mem_subtree_of_ne_top {R : RootedTree V} {v x : V}
    (hx : InSubtree R v x) (hne : x ≠ v) : InSubtree R v (R.parent x) := by
  cases hx with
  | self => exact (hne rfl).elim
  | step _ hp => exact hp

omit [Fintype V] [DecidableEq V] in
theorem subtree_ne_root {R : RootedTree V} {v x : V}
    (hv : v ≠ R.root) (hx : InSubtree R v x) : x ≠ R.root := by
  cases hx with
  | self => exact hv
  | step hx _ => exact hx

theorem child_mem_subtree {R : RootedTree V} {v u : V}
    (hu : u ∈ R.children v) : InSubtree R v u := by
  obtain ⟨hn, hp⟩ := (R.mem_children v u).mp hu
  exact .step hn (hp ▸ InSubtree.self)

theorem top_not_child_subtree {R : RootedTree V} {v u : V}
    (hu : u ∈ R.children v) : ¬ InSubtree R u v := by
  intro h
  have := R.child_rank hu
  have := h.rank_le
  omega

theorem child_subtrees_pairwise_disjoint {R : RootedTree V} {v u w x : V}
    (hu : u ∈ R.children v) (hw : w ∈ R.children v)
    (hx : InSubtree R u x) (hy : InSubtree R w x) : u = w := by
  induction hx with
  | self =>
    by_cases he : u = w
    · exact he
    · have hp := parent_mem_subtree_of_ne_top hy he
      rw [((R.mem_children v u).mp hu).2] at hp
      exact (top_not_child_subtree hw hp).elim
  | @step x hn hp ih =>
    by_cases he : x = w
    · subst x
      rw [((R.mem_children v w).mp hw).2] at hp
      exact (top_not_child_subtree hu hp).elim
    · exact ih (parent_mem_subtree_of_ne_top hy he)

theorem subtree_cases {R : RootedTree V} {v x : V} (hx : InSubtree R v x) :
    x = v ∨ ∃ u ∈ R.children v, InSubtree R u x := by
  induction hx with
  | self => exact Or.inl rfl
  | @step x hn hp ih =>
    rcases ih with he | ⟨u, hu, hx⟩
    · exact Or.inr ⟨x, (R.mem_children v x).mpr ⟨hn, he⟩, .self⟩
    · exact Or.inr ⟨u, hu, .step hn hx⟩

noncomputable def subtree (R : RootedTree V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (InSubtree R v)

omit [DecidableEq V] in
@[simp] theorem mem_subtree (R : RootedTree V) (v x : V) :
    x ∈ subtree R v ↔ InSubtree R v x := by
  classical
  simp [subtree]

theorem subtree_eq_insert_children_union (R : RootedTree V) (v : V) :
    subtree R v = insert v ((R.children v).biUnion (subtree R)) := by
  classical
  ext x
  simp only [mem_subtree, Finset.mem_insert, Finset.mem_biUnion]
  constructor
  · exact subtree_cases
  · rintro (rfl | ⟨u, hu, hx⟩)
    · exact .self
    · exact (child_mem_subtree hu).trans hx

theorem sum_subtree {M : Type*} [AddCommMonoid M] (R : RootedTree V)
    (v : V) (f : V → M) :
    ∑ x ∈ subtree R v, f x = f v + ∑ u ∈ R.children v, ∑ x ∈ subtree R u, f x := by
  classical
  rw [subtree_eq_insert_children_union, Finset.sum_insert]
  · congr 1
    apply Finset.sum_biUnion
    intro u hu w hw hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hne (child_subtrees_pairwise_disjoint hu hw
      ((mem_subtree _ _ _).mp hx) ((mem_subtree _ _ _).mp hy))
  · simp only [Finset.mem_biUnion, mem_subtree, not_exists, not_and]
    exact fun u hu => top_not_child_subtree hu

structure BoundaryState (m : ℕ) where
  q : Fin m → ℕ
  cost : Fin m → ℚ
  deriving Inhabited

/-- Outside entries are normalized to zero; ancestry stops at the local top. -/
structure PartialValid (R : RootedTree V) (H : V → ℕ) (m : ℕ)
    (v : V) (n : Fin m → V → ℕ) : Prop where
  outside : ∀ i x, ¬ InSubtree R v x → n i x = 0
  column : ∀ x, InSubtree R v x → ∑ i, n i x = H x
  ancestor : ∀ i x, InSubtree R v x → x ≠ v → 0 < n i x → 0 < n i (R.parent x)

noncomputable def subtreeCost (R : RootedTree V) (s : V → ℚ)
    (v : V) (n : V → ℕ) : ℚ :=
  ∑ x ∈ subtree R v, s x * ((n x + ∑ y ∈ R.children x, n y : ℕ) : ℚ)

def PartialRep (R : RootedTree V) (H : V → ℕ) (m : ℕ) (s : V → ℚ)
    (v : V) (z : BoundaryState m) : Prop :=
  ∃ n, PartialValid R H m v n ∧ (∀ i, n i v = z.q i) ∧
    ∀ i, subtreeCost R s v (n i) = z.cost i

omit [Fintype V] [DecidableEq V] in
theorem PartialValid.entry_le {R : RootedTree V} {H : V → ℕ} {m : ℕ}
    {v : V} {n : Fin m → V → ℕ} (hn : PartialValid R H m v n)
    (i : Fin m) (x : V) (hx : InSubtree R v x) : n i x ≤ H x := by
  rw [← hn.column x hx]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (n j x)) (Finset.mem_univ i)

omit [Fintype V] [DecidableEq V] in
theorem PartialValid.positive_top {R : RootedTree V} {H : V → ℕ} {m : ℕ}
    {v : V} {n : Fin m → V → ℕ} (hn : PartialValid R H m v n)
    (i : Fin m) {x : V} (hx : InSubtree R v x) (hp : 0 < n i x) : 0 < n i v := by
  classical
  induction hx with
  | self => exact hp
  | @step x hxr hparent ih =>
    by_cases he : x = v
    · simpa [he] using hp
    · exact ih (hn.ancestor i x (.step hxr hparent) he hp)

omit [Fintype V] [DecidableEq V] in
theorem PartialValid.zero_of_top_zero {R : RootedTree V} {H : V → ℕ} {m : ℕ}
    {v : V} {n : Fin m → V → ℕ} (hn : PartialValid R H m v n)
    (i : Fin m) (hz : n i v = 0) (x : V) : n i x = 0 := by
  classical
  by_cases hx : InSubtree R v x
  · by_contra hne
    have := hn.positive_top i hx (Nat.pos_of_ne_zero hne)
    omega
  · exact hn.outside i x hx

end UAVProof.TreeBudgetSubtreeState
