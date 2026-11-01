import LeanCompletion.UAV.TreeFlowExistence
import LeanCompletion.UAV.PositiveFlowConnectivity

namespace UAVProof.TreeFlowConnectivity
open TreeFlowExistence PositiveFlowConnectivity SupportExactFeasibility
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rank_le_sum (R : RootedTree V) (v : V) : R.rank v ≤ ∑ w, R.rank w :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)

theorem parent_path (R : RootedTree V) (v : V) :
    ∃ p : R.graph.Walk v R.root, p.IsPath ∧
      (∀ w ∈ p.support, R.rank v ≤ R.rank w) ∧
      (v ≠ R.root → p.snd = R.parent v) := by
  by_cases hv : v = R.root
  · subst v
    exact ⟨.nil, by simp, by simp, by simp⟩
  · obtain ⟨p, hp, hr, hs⟩ := parent_path R (R.parent v)
    have ha : R.graph.Adj v (R.parent v) := (R.adj_iff _ _).mpr (Or.inr ⟨hv, rfl⟩)
    have hnot : v ∉ p.support := by
      intro hm
      have := hr v hm
      have := R.parent_rank v hv
      omega
    refine ⟨.cons ha p, ?_, ?_, ?_⟩
    · exact (SimpleGraph.Walk.cons_isPath_iff ha p).mpr ⟨hp, hnot⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact le_rfl
      · exact (R.parent_rank v hv).le.trans (hr w hw)
    · intro _; simp
termination_by (∑ w, R.rank w) - R.rank v
decreasing_by
  classical
  have := R.parent_rank v hv
  have := rank_le_sum R (R.parent v)
  omega

theorem reachable_parent_positive (R : RootedTree V) (h : V → ℕ) {v : V}
    (hv : v ≠ R.root)
    (hr : (supportGraph (edgeFlow R h)).Reachable R.root v) : 0 < h v := by
  classical
  have hle : supportGraph (edgeFlow R h) ≤ R.graph := by
    intro a b hab
    by_contra hn
    have hz := edgeFlow_supported R h a b hn
    have hz' := edgeFlow_symmetric R h a b
    rcases hab.2 with hp | hp <;> omega
  obtain ⟨p, hp, _, hs⟩ := parent_path R v
  apply hr.symm.elim_path
  intro q
  have heq : q.val.mapLe hle = p := congrArg Subtype.val
    (R.isTree.isAcyclic.path_unique ⟨q.val.mapLe hle, q.property.mapLe hle⟩ ⟨p, hp⟩)
  have hsecond : q.val.snd = R.parent v := by
    have hmap : (q.val.mapLe hle).snd = q.val.snd := by
      set_option backward.isDefEq.respectTransparency false in
        simpa only [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.snd] using
          (SimpleGraph.Walk.getVert_map (SimpleGraph.Hom.ofLE hle) q.val 1)
    exact hmap.symm.trans ((congrArg (fun t : R.graph.Walk v R.root => t.snd) heq).trans (hs hv))
  have ha := q.val.adj_snd (SimpleGraph.Walk.not_nil_of_ne hv)
  rw [hsecond] at ha
  have he := edgeFlow_parent R h hv
  have he' := edgeFlow_symmetric R h v (R.parent v)
  rcases ha.2 with ha | ha <;> omega

theorem parent_positive_reachable (R : RootedTree V) (h : V → ℕ)
    (hl : ∀ v, v ≠ R.root → 0 < outFlow Finset.univ (edgeFlow R h) v → 0 < h v)
    (v : V) (hp : 0 < h v) : (supportGraph (edgeFlow R h)).Reachable R.root v := by
  by_cases hv : v = R.root
  · subst v; exact SimpleGraph.Reachable.refl _
  · have he : 0 < edgeFlow R h (R.parent v) v := by rw [edgeFlow_parent R h hv]; exact hp
    have ha : (supportGraph (edgeFlow R h)).Adj (R.parent v) v :=
      ⟨parent_ne_self R hv, Or.inl he⟩
    apply SimpleGraph.Reachable.trans (v := R.parent v) ?_ ha.reachable
    by_cases hpRoot : R.parent v = R.root
    · rw [hpRoot]
    · apply parent_positive_reachable R h hl (R.parent v)
      apply hl _ hpRoot
      exact lt_of_lt_of_le he
        (Finset.single_le_sum (fun j _ => Nat.zero_le (edgeFlow R h (R.parent v) j))
          (Finset.mem_univ v))
termination_by (∑ w, R.rank w) - R.rank v
decreasing_by
  classical
  have := R.parent_rank v hv
  have := rank_le_sum R (R.parent v)
  omega

theorem edgeFlow_connected_iff (R : RootedTree V) (h : V → ℕ) :
    DepotConnected R.root (edgeFlow R h) ↔
      ∀ v, v ≠ R.root → 0 < outFlow Finset.univ (edgeFlow R h) v → 0 < h v := by
  constructor
  · intro hc v hv hp
    obtain ⟨w, _, hw⟩ := Finset.sum_pos_iff.mp hp
    exact reachable_parent_positive R h hv (hc v w hw)
  · intro hl u v huv
    by_cases hu : u = R.root
    · subst u; exact SimpleGraph.Reachable.refl _
    · apply parent_positive_reachable R h hl u
      apply hl u hu
      exact lt_of_lt_of_le huv
        (Finset.single_le_sum (fun j _ => Nat.zero_le (edgeFlow R h u j))
          (Finset.mem_univ v))

theorem canonicalFlow_connected_iff (R : RootedTree V) (d : V → ℕ) (m : ℕ)
    (hc : FlowCompatible R d m) :
    DepotConnected R.root (canonicalFlow R d) ↔
      ∀ v, v ≠ R.root → 0 < d v → 0 < requirement R d v := by
  have hd := canonicalFlow_has_degrees R d m hc
  rw [canonicalFlow, edgeFlow_connected_iff]
  constructor
  · intro h v hv hp
    have ho : outFlow Finset.univ (canonicalFlow R d) v = d v := by
      simpa [prescribedDegree, hv] using hd.1 v
    have ht := h v hv (by simpa [← ho] using hp)
    omega
  · intro h v hv hp
    have ho : outFlow Finset.univ (canonicalFlow R d) v = d v := by
      simpa [prescribedDegree, hv] using hd.1 v
    have ht := h v hv (by simpa [← ho] using hp)
    omega

end UAVProof.TreeFlowConnectivity

#print axioms UAVProof.TreeFlowConnectivity.canonicalFlow_connected_iff
