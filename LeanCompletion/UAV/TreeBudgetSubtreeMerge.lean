import LeanCompletion.UAV.TreeBudgetSubtreeState

/-! Restriction and gluing of independent local matrices, and the exact
leaf/internal-node recurrence. Multiple crossings remain unrestricted. -/
namespace UAVProof.TreeBudgetSubtreeState
open TreeFlowExistence TreeBudgetRow
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def restrictMatrix (R : RootedTree V) {m : ℕ}
    (u : V) (n : Fin m → V → ℕ) : Fin m → V → ℕ := by
  classical
  exact fun i x => if InSubtree R u x then n i x else 0

omit [Fintype V] [DecidableEq V] in
theorem restrictMatrix_eq {R : RootedTree V} {m : ℕ} {u x : V}
    (n : Fin m → V → ℕ) (i : Fin m) (hx : InSubtree R u x) :
    restrictMatrix R u n i x = n i x := by
  classical
  simp [restrictMatrix, hx]

theorem partial_restrict_valid {R : RootedTree V} {H : V → ℕ} {m : ℕ}
    {v u : V} {n : Fin m → V → ℕ} (hn : PartialValid R H m v n)
    (hu : u ∈ R.children v) : PartialValid R H m u (restrictMatrix R u n) := by
  classical
  constructor
  · intro i x hx; simp [restrictMatrix, hx]
  · intro x hx
    simpa [restrictMatrix, hx] using hn.column x ((child_mem_subtree hu).trans hx)
  · intro i x hx hne hp
    rw [restrictMatrix_eq n i (parent_mem_subtree_of_ne_top hx hne)]
    rw [restrictMatrix_eq n i hx] at hp
    apply hn.ancestor i x ((child_mem_subtree hu).trans hx) _ hp
    intro he; subst x
    exact top_not_child_subtree hu hx

theorem subtreeCost_congr (R : RootedTree V) (s : V → ℚ) (v : V)
    {n n' : V → ℕ} (he : ∀ x, InSubtree R v x → n x = n' x) :
    subtreeCost R s v n = subtreeCost R s v n' := by
  apply Finset.sum_congr rfl
  intro x hx
  have hxs := (mem_subtree R v x).mp hx
  rw [he x hxs]
  congr 3
  apply Finset.sum_congr rfl
  intro y hy
  exact he y (hxs.trans (child_mem_subtree hy))

theorem subtreeCost_restrict (R : RootedTree V) (s : V → ℚ) {m : ℕ}
    (u : V) (n : Fin m → V → ℕ) (i : Fin m) :
    subtreeCost R s u (restrictMatrix R u n i) = subtreeCost R s u (n i) :=
  subtreeCost_congr R s u (fun _ hx => restrictMatrix_eq n i hx)

theorem subtreeCost_split (R : RootedTree V) (s : V → ℚ) (v : V) (n : V → ℕ) :
    subtreeCost R s v n =
      s v * ((n v + ∑ u ∈ R.children v, n u : ℕ) : ℚ) +
        ∑ u ∈ R.children v, subtreeCost R s u n :=
  sum_subtree R v _

noncomputable def glueMatrix (R : RootedTree V) {m : ℕ} (v : V)
    (q : Fin m → ℕ) (ns : V → Fin m → V → ℕ) : Fin m → V → ℕ :=
  fun i x => if x = v then q i else ∑ u ∈ R.children v, ns u i x

@[simp] theorem glueMatrix_top (R : RootedTree V) {m : ℕ} (v : V)
    (q : Fin m → ℕ) (ns : V → Fin m → V → ℕ) (i : Fin m) :
    glueMatrix R v q ns i v = q i := by simp [glueMatrix]

theorem glueMatrix_child {R : RootedTree V} {H : V → ℕ} {m : ℕ}
    {v u x : V} (q : Fin m → ℕ) {ns : V → Fin m → V → ℕ}
    (hn : ∀ w ∈ R.children v, PartialValid R H m w (ns w))
    (hu : u ∈ R.children v) (hx : InSubtree R u x) (i : Fin m) :
    glueMatrix R v q ns i x = ns u i x := by
  classical
  have hne : x ≠ v := fun he => top_not_child_subtree hu (he ▸ hx)
  simp only [glueMatrix, if_neg hne]
  apply Finset.sum_eq_single u
  · intro w hw hwu
    apply (hn w hw).outside
    intro h
    exact hwu (child_subtrees_pairwise_disjoint hw hu h hx)
  · exact fun h => (h hu).elim

theorem partial_glue_valid {R : RootedTree V} {H : V → ℕ} {m : ℕ}
    {v : V} {q : Fin m → ℕ} {ns : V → Fin m → V → ℕ}
    (hq : ∑ i, q i = H v)
    (hn : ∀ u ∈ R.children v, PartialValid R H m u (ns u))
    (hs : ∀ u ∈ R.children v, ∀ i, 0 < ns u i u → 0 < q i) :
    PartialValid R H m v (glueMatrix R v q ns) := by
  classical
  constructor
  · intro i x hx
    have hne : x ≠ v := fun he => hx (he ▸ InSubtree.self)
    simp only [glueMatrix, if_neg hne]
    apply Finset.sum_eq_zero
    intro u hu
    exact (hn u hu).outside i x (fun h => hx ((child_mem_subtree hu).trans h))
  · intro x hx
    rcases subtree_cases hx with rfl | ⟨u, hu, hx⟩
    · simpa using hq
    · simpa only [glueMatrix_child q hn hu hx] using (hn u hu).column x hx
  · intro i x hx hne hp
    obtain ⟨u, hu, hxu⟩ := (subtree_cases hx).resolve_left hne
    rw [glueMatrix_child q hn hu hxu] at hp
    by_cases he : x = u
    · subst x
      rw [((R.mem_children v u).mp hu).2, glueMatrix_top]
      exact hs u hu i hp
    · rw [glueMatrix_child q hn hu (parent_mem_subtree_of_ne_top hxu he)]
      exact (hn u hu).ancestor i x hxu he hp

theorem subtreeCost_glue {R : RootedTree V} {H : V → ℕ} {m : ℕ}
    {v : V} (s : V → ℚ) (q : Fin m → ℕ) {ns : V → Fin m → V → ℕ}
    (hn : ∀ u ∈ R.children v, PartialValid R H m u (ns u)) (i : Fin m) :
    subtreeCost R s v (glueMatrix R v q ns i) =
      s v * ((q i + ∑ u ∈ R.children v, ns u i u : ℕ) : ℚ) +
        ∑ u ∈ R.children v, subtreeCost R s u (ns u i) := by
  rw [subtreeCost_split, glueMatrix_top]
  have htop : (∑ u ∈ R.children v, glueMatrix R v q ns i u) =
      ∑ u ∈ R.children v, ns u i u := by
    apply Finset.sum_congr rfl
    intro u hu
    exact glueMatrix_child q hn hu .self i
  rw [htop]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  exact subtreeCost_congr R s u (fun _ hx => glueMatrix_child q hn hu hx i)

/-- The transition uses support implication, never a bound on child counts. -/
theorem partialRep_merge_iff (R : RootedTree V) (H : V → ℕ) (m : ℕ)
    (s : V → ℚ) (v : V) (z : BoundaryState m) :
    PartialRep R H m s v z ↔
      (∑ i, z.q i) = H v ∧ ∃ zs : V → BoundaryState m,
        (∀ u ∈ R.children v, PartialRep R H m s u (zs u)) ∧
        (∀ u ∈ R.children v, ∀ i, 0 < (zs u).q i → 0 < z.q i) ∧
        ∀ i, z.cost i =
          s v * ((z.q i + ∑ u ∈ R.children v, (zs u).q i : ℕ) : ℚ) +
            ∑ u ∈ R.children v, (zs u).cost i := by
  classical
  constructor
  · rintro ⟨n, hn, hq, hc⟩
    refine ⟨?_, fun u => ⟨fun i => n i u, fun i => subtreeCost R s u (n i)⟩, ?_, ?_, ?_⟩
    · simpa only [hq] using hn.column v .self
    · intro u hu
      exact ⟨restrictMatrix R u n, partial_restrict_valid hn hu,
        fun i => restrictMatrix_eq n i .self, fun i => subtreeCost_restrict R s u n i⟩
    · intro u hu i hp
      rw [← hq i]
      have hne : u ≠ v := by
        have := R.child_rank hu
        intro he; simp [he] at this
      simpa only [((R.mem_children v u).mp hu).2] using
        hn.ancestor i u (child_mem_subtree hu) hne hp
    · intro i
      rw [← hc i, subtreeCost_split, hq i]
  · rintro ⟨hq, zs, hz, hs, hc⟩
    have hw : ∀ u, ∃ n : Fin m → V → ℕ, u ∈ R.children v →
        PartialValid R H m u n ∧ (∀ i, n i u = (zs u).q i) ∧
          ∀ i, subtreeCost R s u (n i) = (zs u).cost i := by
      intro u
      by_cases hu : u ∈ R.children v
      · obtain ⟨n, hn⟩ := hz u hu
        exact ⟨n, fun _ => hn⟩
      · exact ⟨fun _ _ => 0, fun h => (hu h).elim⟩
    choose ns hn using hw
    have hv := fun u hu => (hn u hu).1
    refine ⟨glueMatrix R v z.q ns, partial_glue_valid hq hv ?_,
      fun i => glueMatrix_top R v z.q ns i, ?_⟩
    · intro u hu i hp
      exact hs u hu i (by simpa only [(hn u hu).2.1 i] using hp)
    · intro i
      rw [subtreeCost_glue s z.q hv, hc i]
      have hqsum : (∑ u ∈ R.children v, ns u i u) =
          ∑ u ∈ R.children v, (zs u).q i :=
        Finset.sum_congr rfl (fun u hu => (hn u hu).2.1 i)
      have hcsum : (∑ u ∈ R.children v, subtreeCost R s u (ns u i)) =
          ∑ u ∈ R.children v, (zs u).cost i :=
        Finset.sum_congr rfl (fun u hu => (hn u hu).2.2 i)
      rw [hqsum, hcsum]

theorem partialRep_leaf_iff (R : RootedTree V) (H : V → ℕ) (m : ℕ)
    (s : V → ℚ) (v : V) (hleaf : R.children v = ∅) (z : BoundaryState m) :
    PartialRep R H m s v z ↔
      (∑ i, z.q i) = H v ∧ ∀ i, z.cost i = s v * (z.q i : ℚ) := by
  rw [partialRep_merge_iff]
  simp [hleaf]

end UAVProof.TreeBudgetSubtreeState

#print axioms UAVProof.TreeBudgetSubtreeState.partial_restrict_valid
#print axioms UAVProof.TreeBudgetSubtreeState.partial_glue_valid
#print axioms UAVProof.TreeBudgetSubtreeState.partialRep_merge_iff
#print axioms UAVProof.TreeBudgetSubtreeState.partialRep_leaf_iff
