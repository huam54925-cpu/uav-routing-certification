import LeanCompletion.UAV.TreeBudgetSubtreeCompact
import LeanCompletion.UAV.TreeFlowExamples

/-! Kernel-checked guards for repeated crossings, signed costs, empty fleets,
and the root-child multiplicity cap. -/
namespace UAVProof.TreeBudgetSubtreeExamples
open TreeFlowExistence TreeFlowExamples TreeBudgetRow TreeBudgetMatrix TreeBudgetSubtreeState
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def repeatH : Fin 4 → ℕ := ![0, 1, 1, 3]
def repeatFee : Fin 4 → ℚ := ![99, 0, -1, 2]
def repeatLeaf : BoundaryState 1 := ⟨fun _ => 3, fun _ => 6⟩
def repeatTop : BoundaryState 1 := ⟨fun _ => 1, fun _ => 2⟩

theorem repeated_leaf : PartialRep pathFour repeatH 1 repeatFee 3 repeatLeaf := by
  apply (partialRep_leaf_iff _ _ _ _ _ pathFour_children.2.2.2 _).mpr
  norm_num [repeatH, repeatFee, repeatLeaf, Fin.sum_univ_succ]

/-- A child boundary count of three is compatible with a parent count of one. -/
theorem repeated_internal_merge : PartialRep pathFour repeatH 1 repeatFee 2 repeatTop := by
  rw [partialRep_merge_iff, pathFour_children.2.2.1]
  refine ⟨by simp [repeatTop, repeatH], fun _ => repeatLeaf, ?_, ?_, ?_⟩
  · intro u hu
    have : u = 3 := Finset.mem_singleton.mp hu
    subst u
    exact repeated_leaf
  · intro u hu i hp
    norm_num [repeatTop]
  · intro i
    norm_num [repeatTop, repeatLeaf, repeatFee]

theorem child_count_exceeds_parent : repeatTop.q 0 < repeatLeaf.q 0 := by decide

def signedH : Fin 4 → ℕ := ![0, 1, 1, 1]
def signedFee : Fin 4 → ℚ := ![99, 0, -3, 10]

/-- The leaf costs 10 locally (7 linearly), but the whole route costs only 4. -/
theorem signed_matrix : MatrixFeasible pathFour signedH 1 signedFee 4 := by
  refine ⟨fun _ => signedH, ?_, ?_, ?_, ?_⟩
  · intro v hv; simp
  · intro i
    simp [rootDegree, pathFour, RootedTree.children, signedH, Finset.sum_filter, Fin.sum_univ_succ]
  · intro i v hv hp hparent
    fin_cases v <;> norm_num [pathFour, signedH] at *
  · intro i
    rw [rowCost_linear]
    norm_num [pathFour, signedH, signedFee, Fin.sum_univ_succ]
    decide +kernel

theorem signed_root_accept : RootAccept pathFour signedH 1 signedFee 4 :=
  (rootAccept_iff_matrixFeasible _ _ _ _ _).mpr signed_matrix

theorem signed_compact_root_accept : CompactRootAccept pathFour signedH 1 signedFee 4 :=
  (compactRootAccept_iff_matrixFeasible _ _ _ _ _).mpr signed_matrix

theorem signed_leaf_above_budget :
    PartialRep pathFour signedH 1 signedFee 3 ⟨fun _ => 1, fun _ => 10⟩ ∧
    (4 : ℚ) < 10 ∧ 4 < linearWeight pathFour signedFee 3 := by
  refine ⟨?_, by norm_num, ?_⟩
  · apply (partialRep_leaf_iff _ _ _ _ _ pathFour_children.2.2.2 _).mpr
    norm_num [signedH, signedFee, Fin.sum_univ_succ]
  · norm_num [linearWeight, parentCharge, pathFour, signedFee]
    decide +kernel

/-- Root-child caps reject multiplicity two although the active set is a singleton. -/
theorem root_child_cap_rejects_two :
    ¬ CompactRep pathFour (fun _ => 2) 1 (fun _ => 0) 1 ⟨{0}, fun _ => 0⟩ := by
  rintro ⟨n, hn, hcap, _, _⟩
  have hcol := hn.column 1 InSubtree.self
  have hle := hcap (by decide) 0
  have hcol' : n 0 1 = 2 := by simpa using hcol
  change n 0 1 ≤ 1 at hle
  omega

theorem zero_routes_negative_budget {V : Type*} [Fintype V] [DecidableEq V]
    (R : RootedTree V) (s : V → ℚ) : CompactRootAccept R (fun _ => 0) 0 s (-1) := by
  apply (compactRootAccept_iff_matrixFeasible _ _ _ _ _).mpr
  refine ⟨fun i => Fin.elim0 i, ?_, ?_, ?_, ?_⟩
  · intro v hv; simp
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

theorem depot_only_positive_routes {V : Type*} [Fintype V] [DecidableEq V]
    (R : RootedTree V) (H : V → ℕ) (m : ℕ) (hm : 0 < m) (s : V → ℚ) (T : ℚ)
    (hchildren : R.children R.root = ∅) : ¬ RootAccept R H m s T := by
  intro h
  obtain ⟨n, _, hd, _, _⟩ := (rootAccept_iff_matrixFeasible _ _ _ _ _).mp h
  have := hd ⟨0, hm⟩
  simp [rootDegree, hchildren] at this

end UAVProof.TreeBudgetSubtreeExamples

#print axioms UAVProof.TreeBudgetSubtreeExamples.repeated_internal_merge
#print axioms UAVProof.TreeBudgetSubtreeExamples.signed_compact_root_accept
#print axioms UAVProof.TreeBudgetSubtreeExamples.root_child_cap_rejects_two
#print axioms UAVProof.TreeBudgetSubtreeExamples.zero_routes_negative_budget
