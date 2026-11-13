import LeanCompletion.UAV.TreeBudgetSubtreeMerge

/-! Root acceptance for labeled local matrix states. The depot is never
charged, even when its supplied service value is nonzero. -/
namespace UAVProof.TreeBudgetSubtreeState
open TreeFlowExistence TreeFlowConnectivity TreeBudgetRow TreeBudgetMatrix
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem root_subtree (R : RootedTree V) (x : V) : InSubtree R R.root x := by
  by_cases hx : x = R.root
  · subst x; exact .self
  · exact .step hx (root_subtree R (R.parent x))
termination_by (∑ w, R.rank w) - R.rank x
decreasing_by
  classical
  have := R.parent_rank x hx
  have := rank_le_sum R (R.parent x)
  omega

theorem subtree_root (R : RootedTree V) : subtree R R.root = Finset.univ := by
  ext x
  simp [root_subtree]

theorem rowCost_eq_sum_root_subtrees (R : RootedTree V) (s : V → ℚ) (n : V → ℕ) :
    rowCost R n s = ∑ u ∈ R.children R.root, subtreeCost R s u n := by
  classical
  unfold rowCost
  rw [← subtree_root R, sum_subtree]
  simp only [rowVisits, if_true, Nat.cast_zero, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro x hx
  have hxr := subtree_ne_root ((R.mem_children _ _).mp hu).1 ((mem_subtree _ _ _).mp hx)
  simp [hxr]

def RootAccept (R : RootedTree V) (H : V → ℕ) (m : ℕ) (s : V → ℚ) (T : ℚ) : Prop :=
  ∃ zs : V → BoundaryState m,
    (∀ u ∈ R.children R.root, PartialRep R H m s u (zs u)) ∧
    (∀ i, (∑ u ∈ R.children R.root, (zs u).q i) = 1) ∧
    ∀ i, (∑ u ∈ R.children R.root, (zs u).cost i) ≤ T

theorem rootAccept_iff_matrixFeasible (R : RootedTree V) (H : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) : RootAccept R H m s T ↔ MatrixFeasible R H m s T := by
  classical
  constructor
  · rintro ⟨zs, hz, hdegree, hbudget⟩
    have hw : ∀ u, ∃ n : Fin m → V → ℕ, u ∈ R.children R.root →
        PartialValid R H m u n ∧ (∀ i, n i u = (zs u).q i) ∧
          ∀ i, subtreeCost R s u (n i) = (zs u).cost i := by
      intro u
      by_cases hu : u ∈ R.children R.root
      · obtain ⟨n, hn⟩ := hz u hu
        exact ⟨n, fun _ => hn⟩
      · exact ⟨fun _ _ => 0, fun h => (hu h).elim⟩
    choose ns hn using hw
    have hv := fun u hu => (hn u hu).1
    let n := glueMatrix R R.root (fun _ : Fin m => 0) ns
    have he {u x : V} (hu : u ∈ R.children R.root) (hx : InSubtree R u x) (i) :
        n i x = ns u i x := glueMatrix_child _ hv hu hx i
    refine ⟨n, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := (subtree_cases (root_subtree R x)).resolve_left hx
      simpa only [he hu hxu] using (hv u hu).column x hxu
    · intro i
      unfold rootDegree
      calc
        (∑ u ∈ R.children R.root, n i u) =
            ∑ u ∈ R.children R.root, (zs u).q i := by
          apply Finset.sum_congr rfl
          intro u hu
          exact (he hu .self i).trans ((hn u hu).2.1 i)
        _ = 1 := hdegree i
    · intro i x hx hp hparent
      obtain ⟨u, hu, hxu⟩ := (subtree_cases (root_subtree R x)).resolve_left hx
      have hne : x ≠ u := by
        intro heq; subst x
        exact hparent ((R.mem_children _ _).mp hu).2
      rw [he hu (parent_mem_subtree_of_ne_top hxu hne)]
      exact (hv u hu).ancestor i x hxu hne (by simpa only [he hu hxu] using hp)
    · intro i
      rw [rowCost_eq_sum_root_subtrees]
      have hc : (∑ u ∈ R.children R.root, subtreeCost R s u (n i)) =
          ∑ u ∈ R.children R.root, (zs u).cost i := by
        apply Finset.sum_congr rfl
        intro u hu
        exact (subtreeCost_congr R s u (fun _ hx => he hu hx i)).trans ((hn u hu).2.2 i)
      rw [hc]
      exact hbudget i
  · rintro ⟨n, hcolumn, hdegree, hancestor, hbudget⟩
    refine ⟨fun u => ⟨fun i => n i u, fun i => subtreeCost R s u (n i)⟩, ?_,
      hdegree, ?_⟩
    · intro u hu
      have hur := ((R.mem_children _ _).mp hu).1
      refine ⟨restrictMatrix R u n, ?_, fun i => restrictMatrix_eq n i .self,
        fun i => subtreeCost_restrict R s u n i⟩
      constructor
      · intro i x hx; simp [restrictMatrix, hx]
      · intro x hx
        simpa [restrictMatrix, hx] using hcolumn x (subtree_ne_root hur hx)
      · intro i x hx hne hp
        have hpx := parent_mem_subtree_of_ne_top hx hne
        rw [restrictMatrix_eq n i hpx]
        apply hancestor i x (subtree_ne_root hur hx)
        · simpa only [restrictMatrix_eq n i hx] using hp
        · exact subtree_ne_root hur hpx
    · intro i
      simpa only [rowCost_eq_sum_root_subtrees] using hbudget i

/-- Reuse the existing route-realization bridge with its degree hypothesis. -/
theorem rootAccept_iff_exactFeasible (R : RootedTree V) (H d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ)
    (hd : SupportExactFeasibility.HasDegrees R.root d m (edgeFlow R H)) :
    RootAccept R H m s T ↔
      SupportExactFeasibility.ExactFeasible R.root (edgeFlow R H) d m s T :=
  (rootAccept_iff_matrixFeasible R H m s T).trans (exact_iff_matrix R H d m s T hd).symm

end UAVProof.TreeBudgetSubtreeState

#print axioms UAVProof.TreeBudgetSubtreeState.rootAccept_iff_matrixFeasible
#print axioms UAVProof.TreeBudgetSubtreeState.rootAccept_iff_exactFeasible
