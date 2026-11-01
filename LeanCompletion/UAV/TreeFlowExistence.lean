import LeanCompletion.UAV.TreeFlowSymmetry

/-! Rooted finite trees, integer leaf recursion, and existence of a flow
with prescribed incoming and outgoing degrees. Rank decreases toward children;
no nonnegativity is built into the integer recursion. -/

namespace UAVProof.TreeFlowExistence
open SupportExactFeasibility TreeFlowSymmetry

structure RootedTree (V : Type*) where
  graph : SimpleGraph V
  isTree : graph.IsTree
  root : V
  parent : V → V
  parent_root : parent root = root
  rank : V → ℕ
  parent_rank : ∀ v, v ≠ root → rank v < rank (parent v)
  adj_iff : ∀ u v, graph.Adj u v ↔
    (v ≠ root ∧ parent v = u) ∨ (u ≠ root ∧ parent u = v)

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def RootedTree.children (R : RootedTree V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => w ≠ R.root ∧ R.parent w = v)

@[simp] theorem RootedTree.mem_children (R : RootedTree V) (v w : V) :
    w ∈ R.children v ↔ w ≠ R.root ∧ R.parent w = v := by
  classical
  simp [RootedTree.children]

theorem RootedTree.child_rank (R : RootedTree V) {v w : V}
    (hw : w ∈ R.children v) : R.rank w < R.rank v := by
  obtain ⟨hne, hp⟩ := (R.mem_children v w).mp hw
  simpa [hp] using R.parent_rank w hne

noncomputable def requirement (R : RootedTree V) (d : V → ℕ) (v : V) : ℤ :=
  (d v : ℤ) - ∑ w : R.children v, requirement R d w
termination_by R.rank v
decreasing_by exact R.child_rank w.property

theorem requirement_eq (R : RootedTree V) (d : V → ℕ) (v : V) :
    requirement R d v = (d v : ℤ) - ∑ w ∈ R.children v, requirement R d w := by
  rw [requirement]
  simp only [Finset.sum_coe_sort]

theorem recurrence_unique (R : RootedTree V) (d : V → ℕ) (h : V → ℤ)
    (hh : ∀ v, v ≠ R.root → h v = (d v : ℤ) - ∑ w ∈ R.children v, h w) :
    ∀ v, v ≠ R.root → h v = requirement R d v := by
  intro v hv
  rw [hh v hv, requirement_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  exact recurrence_unique R d h hh w ((R.mem_children v w).mp hw).1
termination_by v => R.rank v
decreasing_by exact R.child_rank hw

def edgeFlow (R : RootedTree V) (h : V → ℕ) (u v : V) : ℕ :=
  (if v ≠ R.root ∧ R.parent v = u then h v else 0) +
  (if u ≠ R.root ∧ R.parent u = v then h u else 0)

theorem edgeFlow_symmetric (R : RootedTree V) (h : V → ℕ) (u v : V) :
    edgeFlow R h u v = edgeFlow R h v u := by
  unfold edgeFlow
  omega

theorem edgeFlow_supported (R : RootedTree V) (h : V → ℕ) (u v : V)
    (hn : ¬ R.graph.Adj u v) : edgeFlow R h u v = 0 := by
  have h := mt (R.adj_iff u v).mpr hn
  simp only [not_or] at h
  simp [edgeFlow, h.1, h.2]

theorem edgeFlow_out (R : RootedTree V) (h : V → ℕ) (v : V) :
    outFlow Finset.univ (edgeFlow R h) v =
      (if v = R.root then 0 else h v) + ∑ w ∈ R.children v, h w := by
  classical
  unfold outFlow edgeFlow
  rw [Finset.sum_add_distrib]
  have hp : (∑ j : V, if v ≠ R.root ∧ R.parent v = j then h v else 0) =
      if v = R.root then 0 else h v := by
    by_cases hv : v = R.root
    · simp [hv]
    · simp [hv]
  rw [hp]
  rw [add_comm]
  congr 1
  simp [RootedTree.children, Finset.sum_filter]

theorem edgeFlow_in (R : RootedTree V) (h : V → ℕ) (v : V) :
    inFlow Finset.univ (edgeFlow R h) v =
      (if v = R.root then 0 else h v) + ∑ w ∈ R.children v, h w := by
  simpa only [inFlow, edgeFlow_symmetric R h] using edgeFlow_out R h v

theorem parent_ne_self (R : RootedTree V) {v : V} (hv : v ≠ R.root) :
    R.parent v ≠ v := by
  have h := R.parent_rank v hv
  intro heq
  rw [heq] at h
  omega

theorem parent_not_child (R : RootedTree V) {v : V} (hv : v ≠ R.root) :
    ¬ (R.parent v ≠ R.root ∧ R.parent (R.parent v) = v) := by
  rintro ⟨hp, heq⟩
  have h₁ := R.parent_rank v hv
  have h₂ := R.parent_rank (R.parent v) hp
  rw [heq] at h₂
  omega

theorem edgeFlow_parent (R : RootedTree V) (h : V → ℕ) {v : V}
    (hv : v ≠ R.root) : edgeFlow R h (R.parent v) v = h v := by
  simp [edgeFlow, hv, parent_not_child R hv]

theorem flow_eq_edgeFlow (R : RootedTree V) (x : V → V → ℕ)
    (hshape : ∀ u v, ¬ R.graph.Adj u v → x u v = 0)
    (hsymm : ∀ u v, x u v = x v u) :
    x = edgeFlow R (fun v => x (R.parent v) v) := by
  funext u v
  by_cases hv : v ≠ R.root ∧ R.parent v = u
  · obtain ⟨hv, rfl⟩ := hv
    exact (edgeFlow_parent R (fun v => x (R.parent v) v) hv).symm
  · by_cases hu : u ≠ R.root ∧ R.parent u = v
    · obtain ⟨hu, rfl⟩ := hu
      rw [edgeFlow_symmetric, edgeFlow_parent R _ hu]
      exact hsymm _ _
    · have hn : ¬ R.graph.Adj u v := by simpa [R.adj_iff] using not_or.mpr ⟨hv, hu⟩
      rw [hshape u v hn, edgeFlow_supported R _ u v hn]

/-- The integer criterion; the requirement at the root itself is ignored. -/
def FlowCompatible (R : RootedTree V) (d : V → ℕ) (m : ℕ) : Prop :=
  (∀ v, v ≠ R.root → 0 ≤ requirement R d v) ∧
  (m : ℤ) = ∑ w ∈ R.children R.root, requirement R d w

noncomputable def canonicalFlow (R : RootedTree V) (d : V → ℕ) : V → V → ℕ :=
  edgeFlow R (fun v => (requirement R d v).toNat)

theorem compatible_of_flow (R : RootedTree V) (d : V → ℕ) (m : ℕ)
    (x : V → V → ℕ)
    (hshape : ∀ u v, ¬ R.graph.Adj u v → x u v = 0)
    (hdegrees : HasDegrees R.root d m x) : FlowCompatible R d m := by
  have hs := tree_flow_symmetric R.graph R.isTree x hshape
    (fun v => (hdegrees.1 v).trans (hdegrees.2 v).symm)
  let h : V → ℕ := fun v => x (R.parent v) v
  have heq : x = edgeFlow R h := flow_eq_edgeFlow R x hshape hs
  have hrec : ∀ v, v ≠ R.root →
      (h v : ℤ) = (d v : ℤ) - ∑ w ∈ R.children v, (h w : ℤ) := by
    intro v hv
    have hd := hdegrees.1 v
    rw [heq, edgeFlow_out] at hd
    simp only [prescribedDegree, hv, if_false] at hd
    have hc : (h v : ℤ) + ∑ w ∈ R.children v, (h w : ℤ) = d v := by
      exact_mod_cast hd
    omega
  have hreq := recurrence_unique R d (fun v => (h v : ℤ)) hrec
  constructor
  · intro v hv
    rw [← hreq v hv]
    exact Nat.cast_nonneg _
  · have hd := hdegrees.1 R.root
    rw [heq, edgeFlow_out] at hd
    simp [prescribedDegree] at hd
    have hc : (m : ℤ) = ∑ w ∈ R.children R.root, (h w : ℤ) := by
      exact_mod_cast hd.symm
    rw [hc]
    apply Finset.sum_congr rfl
    intro w hw
    exact hreq w ((R.mem_children R.root w).mp hw).1

theorem canonicalFlow_has_degrees (R : RootedTree V) (d : V → ℕ) (m : ℕ)
    (h : FlowCompatible R d m) : HasDegrees R.root d m (canonicalFlow R d) := by
  have hcast (v : V) (hv : v ≠ R.root) :
      ((requirement R d v).toNat : ℤ) = requirement R d v :=
    Int.toNat_of_nonneg (h.1 v hv)
  have hsum (v : V) :
      ((∑ w ∈ R.children v, (requirement R d w).toNat : ℕ) : ℤ) =
        ∑ w ∈ R.children v, requirement R d w := by
    push_cast
    apply Finset.sum_congr rfl
    intro w hw
    exact hcast w ((R.mem_children v w).mp hw).1
  have hd (v : V) :
      (if v = R.root then 0 else (requirement R d v).toNat) +
        ∑ w ∈ R.children v, (requirement R d w).toNat = prescribedDegree R.root d m v := by
    by_cases hv : v = R.root
    · subst v
      simp only [prescribedDegree, ite_true, eq_self, zero_add]
      apply Int.natCast_inj.mp
      rw [hsum]
      exact h.2.symm
    · simp only [prescribedDegree, hv, if_false]
      apply Int.natCast_inj.mp
      rw [Nat.cast_add, hcast v hv, hsum]
      have hr := requirement_eq R d v
      omega
  constructor
  · intro v
    exact (edgeFlow_out R _ v).trans (hd v)
  · intro v
    exact (edgeFlow_in R _ v).trans (hd v)

theorem exists_flow_iff (R : RootedTree V) (d : V → ℕ) (m : ℕ) :
    (∃ x : V → V → ℕ,
      (∀ u v, ¬ R.graph.Adj u v → x u v = 0) ∧ HasDegrees R.root d m x) ↔
      FlowCompatible R d m := by
  constructor
  · rintro ⟨x, hs, hd⟩
    exact compatible_of_flow R d m x hs hd
  · intro h
    exact ⟨canonicalFlow R d, edgeFlow_supported R _, canonicalFlow_has_degrees R d m h⟩

end UAVProof.TreeFlowExistence

#print axioms UAVProof.TreeFlowExistence.exists_flow_iff
