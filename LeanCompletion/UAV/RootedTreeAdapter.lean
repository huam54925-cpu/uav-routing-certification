import LeanCompletion.UAV.TreeFlowExistence

/-! Every finite simple tree can be oriented from an arbitrary root.
The recursion rank is the sum of root distances minus the vertex distance. -/

namespace UAVProof.TreeFlowExistence

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_closer_neighbor (G : SimpleGraph V) (hG : G.IsTree)
    (o v : V) (hv : v ≠ o) :
    ∃ u, G.Adj v u ∧ G.dist o u + 1 = G.dist o v := by
  obtain ⟨p, hp⟩ := hG.connected.exists_walk_length_eq_dist v o
  cases p with
  | nil => exact (hv rfl).elim
  | @cons a b c hab p =>
    have hle := G.dist_le p
    obtain ⟨q, hq⟩ := hG.connected.exists_walk_length_eq_dist b o
    have hle' := G.dist_le (q.cons hab)
    simp only [SimpleGraph.Walk.length_cons, hq] at hp hle'
    refine ⟨b, hab, ?_⟩
    rw [G.dist_comm (u := o) (v := b), G.dist_comm (u := o) (v := v)]
    omega

theorem closer_neighbor_unique (G : SimpleGraph V) (hG : G.IsTree)
    (o v a b : V) (ha : G.Adj v a) (hb : G.Adj v b)
    (hda : G.dist o a + 1 = G.dist o v)
    (hdb : G.dist o b + 1 = G.dist o v) : a = b := by
  obtain ⟨p, hp⟩ := hG.connected.exists_walk_length_eq_dist a o
  obtain ⟨q, hq⟩ := hG.connected.exists_walk_length_eq_dist b o
  have hpa : (p.cons ha).IsPath := (p.cons ha).isPath_of_length_eq_dist (by
    simp only [SimpleGraph.Walk.length_cons, hp]
    simpa only [G.dist_comm] using hda)
  have hqb : (q.cons hb).IsPath := (q.cons hb).isPath_of_length_eq_dist (by
    simp only [SimpleGraph.Walk.length_cons, hq]
    simpa only [G.dist_comm] using hdb)
  have heq : p.cons ha = q.cons hb :=
    Subtype.mk.inj (hG.isAcyclic.path_unique ⟨_, hpa⟩ ⟨_, hqb⟩)
  simpa using congrArg SimpleGraph.Walk.snd heq

noncomputable def parentOfTree (G : SimpleGraph V) (hG : G.IsTree) (o v : V) : V :=
  if hv : v = o then o else (exists_closer_neighbor G hG o v hv).choose

theorem parentOfTree_spec (G : SimpleGraph V) (hG : G.IsTree) (o v : V)
    (hv : v ≠ o) :
    G.Adj v (parentOfTree G hG o v) ∧
      G.dist o (parentOfTree G hG o v) + 1 = G.dist o v := by
  simp only [parentOfTree, dif_neg hv]
  exact (exists_closer_neighbor G hG o v hv).choose_spec

noncomputable def RootedTree.ofIsTree (G : SimpleGraph V) (hG : G.IsTree) (o : V) :
    RootedTree V where
  graph := G
  isTree := hG
  root := o
  parent := parentOfTree G hG o
  parent_root := by simp [parentOfTree]
  rank := fun v => (∑ w, G.dist o w) - G.dist o v
  parent_rank := by
    intro v hv
    have h := (parentOfTree_spec G hG o v hv).2
    have hbound : G.dist o v ≤ ∑ w, G.dist o w :=
      Finset.single_le_sum (fun w _ => Nat.zero_le (G.dist o w)) (Finset.mem_univ v)
    omega
  adj_iff := by
    intro u v
    constructor
    · intro huv
      rcases hG.dist_eq_dist_add_one_of_adj o huv with h | h
      · have hu : u ≠ o := by intro heq; subst u; simp at h
        refine Or.inr ⟨hu, ?_⟩
        have hs := parentOfTree_spec G hG o u hu
        exact closer_neighbor_unique G hG o u _ v hs.1 huv hs.2 h.symm
      · have hv : v ≠ o := by intro heq; subst v; simp at h
        refine Or.inl ⟨hv, ?_⟩
        have hs := parentOfTree_spec G hG o v hv
        exact closer_neighbor_unique G hG o v _ u hs.1 huv.symm hs.2 h.symm
    · rintro (⟨hv, heq⟩ | ⟨hu, heq⟩)
      · rw [← heq]
        exact (parentOfTree_spec G hG o v hv).1.symm
      · rw [← heq]
        exact (parentOfTree_spec G hG o u hu).1

@[simp] theorem ofIsTree_graph (G : SimpleGraph V) (hG : G.IsTree) (o : V) :
    (RootedTree.ofIsTree G hG o).graph = G := rfl

@[simp] theorem ofIsTree_root (G : SimpleGraph V) (hG : G.IsTree) (o : V) :
    (RootedTree.ofIsTree G hG o).root = o := rfl

end UAVProof.TreeFlowExistence

#print axioms UAVProof.TreeFlowExistence.RootedTree.ofIsTree
