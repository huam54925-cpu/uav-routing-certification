import LeanCompletion.UAV.TreeBudgetSparseCertificate

/-! Kernel-checked edge cases for A0--A2. -/
namespace UAVProof.TreeBudgetSparseExamples

open TreeFlowExistence TreeBudgetPatterns TreeBudgetCertificate TreeBudgetSparse

/-- A path rooted at vertex 2, rather than vertex 0. -/
def pathThree : RootedTree (Fin 3) where
  graph := SimpleGraph.pathGraph 3
  isTree := by
    classical
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨SimpleGraph.pathGraph_connected 2, ?_⟩
    simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    have he : (SimpleGraph.pathGraph 3).edgeFinset =
        {s((0 : Fin 3), 1), s((1 : Fin 3), 2)} := by
      ext e
      induction e using Sym2.inductionOn with
      | hf u v =>
        fin_cases u <;> fin_cases v <;>
          simp [SimpleGraph.mem_edgeFinset, SimpleGraph.pathGraph_adj, Sym2.eq]
    rw [he]
    decide +kernel
  root := 2
  parent := ![1, 2, 2]
  parent_root := rfl
  rank := ![0, 1, 2]
  parent_rank := by decide +kernel
  adj_iff := by
    intro u v
    rw [SimpleGraph.pathGraph_adj]
    fin_cases u <;> fin_cases v <;> decide

theorem repeated_child_signed_valid :
    RowValid pathThree ![3, 1, 99] ![-1, 0, 999] (-3) ![3, 1, 0] := by decide +kernel

theorem repeated_child_is_polytope_integer :
    InPolytope pathThree ![3, 1, 99] ![-1, 0, 999] (-3)
      (fun v => ((![3, 1, 0] : Fin 3 → ℕ) v : ℚ)) :=
  (rowValid_iff_polytope_integer ..).mp repeated_child_signed_valid

theorem zero_parent_positive_child_reject :
    ¬ RowValid pathThree ![3, 0, 99] (fun _ => 0) 0 ![3, 0, 0] := by decide +kernel

theorem signed_midpoint_valid :
    RowValid pathThree ![3, 1, 99] ![-1, 0, 999] (-1)
      (midpoint ![1, 1, 0] ![3, 1, 0]) := by
  apply midpoint_rowValid
  · decide +kernel
  · decide +kernel
  · decide +kernel

def twoPatterns : Certificate (Fin 3) :=
  ⟨2, ![![1, 1, 0], ![3, 1, 0]], fun _ => 1⟩

def onePattern : Certificate (Fin 3) := ⟨1, fun _ => ![2, 1, 0], fun _ => 2⟩

theorem signed_two_patterns_accept :
    checkCertificate pathThree ![4, 2, 99] 2 ![-1, 0, 999] (-1) twoPatterns = true := by
  decide +kernel

theorem signed_midpoint_compression_accept :
    checkCertificate pathThree ![4, 2, 99] 2 ![-1, 0, 999] (-1) onePattern = true := by
  decide +kernel

theorem wrong_route_count_reject :
    checkCertificate pathThree ![4, 2, 99] 3 ![-1, 0, 999] (-1) onePattern = false := by
  decide +kernel

theorem illegal_zero_count_row_reject :
    checkCertificate pathThree (fun _ => 0) 0 (fun _ => 0) 0
      ⟨1, fun _ => ![1, 0, 0], fun _ => 0⟩ = false := by decide +kernel

/-- Every root position and every signed budget, including the singleton tree. -/
theorem empty_certificate_accept {V : Type*} [Fintype V] [DecidableEq V]
    (R : RootedTree V) (H : V → ℕ) (s : V → ℚ) (T : ℚ)
    (hH : ∀ v, v ≠ R.root → H v = 0) :
    checkCertificate R H 0 s T ⟨0, Fin.elim0, Fin.elim0⟩ = true := by
  rw [checkCertificate_eq_true_iff]
  exact ⟨fun i => Fin.elim0 i, by simp, fun v hv => by simp [hH v hv]⟩

end UAVProof.TreeBudgetSparseExamples
