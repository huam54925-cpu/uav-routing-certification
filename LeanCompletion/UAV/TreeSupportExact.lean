import LeanCompletion.UAV.SupportExactFeasibility

/-! Fixed incoming and outgoing degrees determine a flow on a finite tree.
The proof removes a leaf; it does not assert existence of budget-feasible routes. -/

namespace UAVProof.TreeSupportExact
open SupportExactFeasibility

theorem tree_flow_unique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (x z : V → V → ℕ)
    (hx : ∀ i j, ¬ G.Adj i j → x i j = 0)
    (hz : ∀ i j, ¬ G.Adj i j → z i j = 0)
    (hout : ∀ i, ∑ j, x i j = ∑ j, z i j)
    (hin : ∀ j, ∑ i, x i j = ∑ i, z i j) : x = z := by
  classical
  by_cases ht : Nontrivial V
  · letI := ht
    obtain ⟨v, hv⟩ := hG.exists_vert_degree_one_of_nontrivial
    obtain ⟨u, huv, hu⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
    have row (f : V → V → ℕ) (hf : ∀ i j, ¬ G.Adj i j → f i j = 0) :
        ∑ j, f v j = f v u := by
      apply Finset.sum_eq_single u
      · intro j _ hj
        exact hf v j (fun h => hj (hu j h))
      · simp
    have col (f : V → V → ℕ) (hf : ∀ i j, ¬ G.Adj i j → f i j = 0) :
        ∑ i, f i v = f u v := by
      apply Finset.sum_eq_single u
      · intro i _ hi
        exact hf i v (fun h => hi (hu i h.symm))
      · simp
    have hr : ∀ j, x v j = z v j := by
      intro j
      by_cases h : G.Adj v j
      · rw [hu j h]
        exact (row x hx).symm.trans ((hout v).trans (row z hz))
      · rw [hx v j h, hz v j h]
    have hc : ∀ i, x i v = z i v := by
      intro i
      by_cases h : G.Adj i v
      · rw [hu i h.symm]
        exact (col x hx).symm.trans ((hin v).trans (col z hz))
      · rw [hx i v h, hz i v h]
    let S : Set V := {v}ᶜ
    have split (f : V → ℕ) : (∑ i, f i) = f v + ∑ i : S, f i := by
      rw [Fintype.sum_eq_add_sum_compl v]
      congr 1
      exact Finset.sum_subtype _ (by intro i; simp [S]) f
    have heq := tree_flow_unique (G.induce S)
      ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hv, hG.isAcyclic.induce S⟩
      (fun i j : S => x i j) (fun i j : S => z i j)
      (fun i j h => hx i j h) (fun i j h => hz i j h)
      (fun i => by have h := hout i; rw [split, split, hc] at h; exact Nat.add_left_cancel h)
      (fun j => by have h := hin j; rw [split, split, hr] at h; exact Nat.add_left_cancel h)
    funext i j
    by_cases hi : i = v
    · subst i; exact hr j
    by_cases hj : j = v
    · subst j; exact hc i
    exact congrFun (congrFun heq ⟨i, hi⟩) ⟨j, hj⟩
  · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp ht
    funext i j
    have h : ¬ G.Adj i j := by rw [Subsingleton.elim i j]; exact G.irrefl
    rw [hx i j h, hz i j h]
termination_by Fintype.card V
decreasing_by exact Fintype.card_subtype_lt (x := v) (by simp)

theorem tree_support_determines_flow {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree)
    (depot : V) (d : V → ℕ) (m : ℕ) (x : V → V → ℕ)
    (hdegrees : HasDegrees depot d m x)
    (hshape : ∀ i j, ¬ G.Adj i j → x i j = 0) :
    SupportDeterminesFlow depot d m x := by
  intro z hs hd
  exact tree_flow_unique G hG z x
    (fun i j h => hs i j (hshape i j h)) hshape
    (fun i => (hd.1 i).trans (hdegrees.1 i).symm)
    (fun j => (hd.2 j).trans (hdegrees.2 j).symm)

theorem tree_support_iff_exact {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree)
    (depot : V) (d : V → ℕ) (m : ℕ) (x : V → V → ℕ)
    (hdegrees : HasDegrees depot d m x)
    (hshape : ∀ i j, ¬ G.Adj i j → x i j = 0)
    (service : V → ℚ) (T : ℚ) :
    SupportFeasible depot x d m service T ↔ ExactFeasible depot x d m service T :=
  support_iff_exact_of_unique depot x d m service T
    (tree_support_determines_flow G hG depot d m x hdegrees hshape)

end UAVProof.TreeSupportExact

#print axioms UAVProof.TreeSupportExact.tree_support_determines_flow
#print axioms UAVProof.TreeSupportExact.tree_support_iff_exact
