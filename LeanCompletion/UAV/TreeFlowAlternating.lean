import LeanCompletion.UAV.TreeFlowExistence

/-! Finite alternating expansion of the integer tree recursion.
`layerDemand k v` is the total demand reached by exactly k child steps from v.
The expansion uses the supplied decreasing rank only as a finite cutoff. -/

namespace UAVProof.TreeFlowExistence
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def layerDemand (R : RootedTree V) (d : V → ℕ) : ℕ → V → ℤ
  | 0, v => d v
  | n + 1, v => ∑ w ∈ R.children v, layerDemand R d n w

theorem layerDemand_eq_zero_of_rank_lt (R : RootedTree V) (d : V → ℕ)
    (n : ℕ) (v : V) (hv : R.rank v < n) : layerDemand R d n v = 0 := by
  induction n generalizing v with
  | zero => omega
  | succ n ih =>
    simp only [layerDemand]
    apply Finset.sum_eq_zero
    intro w hw
    apply ih w
    have h := R.child_rank hw
    omega

theorem requirement_eq_alternating_of_rank_lt (R : RootedTree V) (d : V → ℕ)
    (n : ℕ) (v : V) (hv : R.rank v < n) :
    requirement R d v = ∑ k ∈ Finset.range n, (-1 : ℤ) ^ k * layerDemand R d k v := by
  induction n generalizing v with
  | zero => omega
  | succ n ih =>
    rw [requirement_eq, Finset.sum_range_succ']
    simp only [pow_zero, layerDemand, one_mul]
    have hh : (∑ w ∈ R.children v, requirement R d w) =
        ∑ w ∈ R.children v, ∑ k ∈ Finset.range n, (-1 : ℤ) ^ k * layerDemand R d k w := by
      apply Finset.sum_congr rfl
      intro w hw
      apply ih w
      have h := R.child_rank hw
      omega
    rw [hh, Finset.sum_comm]
    simp [pow_succ, Finset.mul_sum, Finset.sum_neg_distrib, sub_eq_add_neg, add_comm]

theorem requirement_eq_alternating_layers (R : RootedTree V) (d : V → ℕ) (v : V) :
    requirement R d v =
      ∑ k ∈ Finset.range (R.rank v + 1), (-1 : ℤ) ^ k * layerDemand R d k v :=
  requirement_eq_alternating_of_rank_lt R d (R.rank v + 1) v (Nat.lt_succ_self _)

noncomputable def layerNodes (R : RootedTree V) : ℕ → V → Finset V
  | 0, v => {v}
  | n + 1, v => (R.children v).biUnion (fun w => layerNodes R n w)

theorem iterate_parent_of_mem_layerNodes (R : RootedTree V) (n : ℕ) (v u : V)
    (hu : u ∈ layerNodes R n v) : (R.parent^[n]) u = v := by
  induction n generalizing v with
  | zero => simpa [layerNodes] using hu
  | succ n ih =>
    obtain ⟨w, hw, hu⟩ := Finset.mem_biUnion.mp hu
    rw [Function.iterate_succ_apply', ih w hu]
    exact ((R.mem_children v w).mp hw).2

theorem layerNodes_disjoint_roots (R : RootedTree V) (n : ℕ) {v w : V}
    (hne : v ≠ w) : Disjoint (layerNodes R n v) (layerNodes R n w) := by
  apply Finset.disjoint_left.mpr
  intro u huv huw
  exact hne ((iterate_parent_of_mem_layerNodes R n v u huv).symm.trans
    (iterate_parent_of_mem_layerNodes R n w u huw))

theorem layerDemand_eq_sum_layerNodes (R : RootedTree V) (d : V → ℕ) (n : ℕ) (v : V) :
    layerDemand R d n v = ∑ u ∈ layerNodes R n v, (d u : ℤ) := by
  induction n generalizing v with
  | zero => simp [layerDemand, layerNodes]
  | succ n ih =>
    simp only [layerDemand, layerNodes]
    rw [Finset.sum_biUnion]
    · exact Finset.sum_congr rfl (fun w _ => ih w)
    · intro a _ b _ hab
      exact layerNodes_disjoint_roots R n hab

theorem requirement_eq_alternating_layerNodes (R : RootedTree V) (d : V → ℕ) (v : V) :
    requirement R d v = ∑ k ∈ Finset.range (R.rank v + 1),
      (-1 : ℤ) ^ k * (∑ u ∈ layerNodes R k v, (d u : ℤ)) := by
  rw [requirement_eq_alternating_layers]
  simp_rw [layerDemand_eq_sum_layerNodes]

theorem path_of_mem_layerNodes (R : RootedTree V) (n : ℕ) (v u : V)
    (hu : u ∈ layerNodes R n v) :
    ∃ p : R.graph.Walk v u, p.IsPath ∧ p.length = n ∧
      ∀ z ∈ p.support, R.rank z ≤ R.rank v := by
  induction n generalizing v with
  | zero =>
    have heq : u = v := by simpa [layerNodes] using hu
    subst u
    exact ⟨.nil, SimpleGraph.Walk.IsPath.nil, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw, hu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨p, hp, hl, hs⟩ := ih w hu
    have ha : R.graph.Adj v w := (R.adj_iff v w).mpr (Or.inl ((R.mem_children v w).mp hw))
    have hr := R.child_rank hw
    refine ⟨.cons ha p, hp.cons ?_, by simp [hl], ?_⟩
    · intro hv
      have := hs v hv
      omega
    · intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact le_rfl
      · exact (hs z hz).trans hr.le

theorem dist_of_mem_layerNodes (R : RootedTree V) (n : ℕ) (v u : V)
    (hu : u ∈ layerNodes R n v) : R.graph.dist v u = n := by
  obtain ⟨p, hp, hl, _⟩ := path_of_mem_layerNodes R n v u hu
  obtain ⟨q, hq, hd⟩ := R.isTree.connected.exists_path_of_dist v u
  have heq : p = q := congrArg Subtype.val (R.isTree.isAcyclic.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  rw [← hd, ← heq, hl]

/-- The finite rooted subtree, including its root. -/
noncomputable def descendants (R : RootedTree V) (v : V) : Finset V :=
  (Finset.range (R.rank v + 1)).biUnion (fun n => layerNodes R n v)

theorem rank_add_depth_le (R : RootedTree V) (n : ℕ) (v u : V)
    (hu : u ∈ layerNodes R n v) : R.rank u + n ≤ R.rank v := by
  induction n generalizing v with
  | zero =>
    have heq : u = v := by simpa [layerNodes] using hu
    subst u
    simp
  | succ n ih =>
    obtain ⟨w, hw, hu⟩ := Finset.mem_biUnion.mp hu
    have h₁ := ih w hu
    have h₂ := R.child_rank hw
    omega

theorem mem_descendants_iff (R : RootedTree V) (v u : V) :
    u ∈ descendants R v ↔ ∃ n, u ∈ layerNodes R n v := by
  constructor
  · intro hu
    obtain ⟨n, _, hn⟩ := Finset.mem_biUnion.mp hu
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    have hb := rank_add_depth_le R n v u hn
    apply Finset.mem_biUnion.mpr
    exact ⟨n, Finset.mem_range.mpr (by omega), hn⟩

theorem requirement_eq_alternating_subtree (R : RootedTree V) (d : V → ℕ) (v : V) :
    requirement R d v =
      ∑ u ∈ descendants R v, (-1 : ℤ) ^ R.graph.dist v u * (d u : ℤ) := by
  rw [requirement_eq_alternating_layerNodes]
  unfold descendants
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [dist_of_mem_layerNodes R n v u hu]
  · intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro u hua hub
    exact hab ((dist_of_mem_layerNodes R a v u hua).symm.trans
      (dist_of_mem_layerNodes R b v u hub))

end UAVProof.TreeFlowExistence

#print axioms UAVProof.TreeFlowExistence.requirement_eq_alternating_layers
#print axioms UAVProof.TreeFlowExistence.requirement_eq_alternating_subtree
