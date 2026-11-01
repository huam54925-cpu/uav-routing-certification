import LeanCompletion.UAV.TreeBudgetCriterion
import LeanCompletion.UAV.SingleSatelliteClosed
import LeanCompletion.UAV.TreeFlowExamples

/-! Regression guards for signed costs, ancestor closure, empty rows, and ceilings. -/
namespace UAVProof.TreeBudgetExamples
open TreeFlowExistence TreeBudgetRow TreeBudgetMatrix TreeBudgetNormalization
open SupportExactFeasibility TreeFlowExamples SingleSatelliteClosed
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def centerThree : RootedTree (Fin 3) where
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
      | hf u v => fin_cases u <;> fin_cases v <;>
          simp [SimpleGraph.mem_edgeFinset, SimpleGraph.pathGraph_adj, Sym2.eq]
    rw [he]
    decide +kernel
  root := 1
  parent := fun _ => 1
  parent_root := rfl
  rank := fun v => if v = 1 then 1 else 0
  parent_rank := by decide +kernel
  adj_iff := by
    intro u v
    rw [SimpleGraph.pathGraph_adj]
    fin_cases u <;> fin_cases v <;> decide

theorem center_cost (n : Fin 3 → ℕ) :
    rowCost centerThree n ![2, 0, -2] = 2 * (n 0 : ℚ) - 2 * (n 2 : ℚ) := by
  rw [rowCost_linear]
  simp [centerThree, Fin.sum_univ_succ]
  ring

/-- Signed fees can hide an over-budget leaf in a relaxed row. -/
theorem signed_relaxed : RelaxedMatrixFeasible centerThree ![1, 0, 1] 2 ![2, 0, -2] 1 := by
  refine ⟨![![1, 0, 1], ![0, 0, 0]], ?_, ?_, ?_⟩
  · intro v hv
    fin_cases v <;> simp_all [centerThree, Fin.sum_univ_succ]
  · simp [AncestorClosed, centerThree]
  · intro r
    rw [center_cost]
    fin_cases r <;> norm_num

theorem signed_no_exact :
    ¬ ExactFeasible centerThree.root (edgeFlow centerThree ![1, 0, 1])
      ![1, 0, 1] 2 ![2, 0, -2] 1 := by
  intro he
  obtain ⟨n, hc, hk, _, hb⟩ := exact_implies_matrix centerThree _ _ _ _ _ he
  have hsum : 0 < ∑ r, n r 0 := by rw [hc 0 (by decide)]; decide
  obtain ⟨r, _, hr⟩ := Finset.sum_pos_iff.mp hsum
  have hroot := hk r
  simp [rootDegree, RootedTree.children, centerThree, Finset.sum_filter,
    Fin.sum_univ_succ] at hroot
  have hcost := hb r
  rw [center_cost] at hcost
  have h0 : n r 0 = 1 := by omega
  have h2 : n r 2 = 0 := by omega
  norm_num [h0, h2] at hcost

/-- Root degree need not be one in a nonnegative relaxed certificate. -/
theorem nonnegative_split :
    MatrixFeasible centerThree ![1, 0, 1] 2 (fun _ => 1) 2 := by
  have hd : HasDegrees centerThree.root ![1, 0, 1] 2 (edgeFlow centerThree ![1, 0, 1]) := by
    constructor <;> intro v
    · rw [edgeFlow_out]; fin_cases v <;>
        norm_num [prescribedDegree, RootedTree.children, centerThree,
          Finset.sum_filter, Fin.sum_univ_succ] <;> decide +kernel
    · rw [edgeFlow_in]; fin_cases v <;>
        norm_num [prescribedDegree, RootedTree.children, centerThree,
          Finset.sum_filter, Fin.sum_univ_succ] <;> decide +kernel
  apply (matrix_iff_relaxed centerThree _ _ 2 (fun _ => 1) 2 hd (by intros; norm_num)).mpr
  refine ⟨![![1, 0, 1], ![0, 0, 0]], ?_, ?_, ?_⟩
  · intro v hv
    fin_cases v <;> simp_all [centerThree, Fin.sum_univ_succ]
  · simp [AncestorClosed, centerThree]
  · intro r
    rw [rowCost_linear]
    fin_cases r <;> norm_num [centerThree, Fin.sum_univ_succ] <;> decide +kernel

theorem path_cost (n : Fin 4 → ℕ) : rowCost pathFour n (fun _ => 1) =
    (n 1 : ℚ) + 2 * (n 2 : ℚ) + 2 * (n 3 : ℚ) := by
  rw [rowCost_linear]
  simp [pathFour, Fin.sum_univ_succ]
  ring

/-- Even a globally connected flow cannot replace row-wise ancestor closure. -/
theorem path_no_budget_matrix : ¬ MatrixFeasible pathFour ![0, 2, 1, 1] 2 (fun _ => 1) 3 := by
  rintro ⟨n, hc, hk, ha, hb⟩
  have hsum : 0 < ∑ r, n r 3 := by rw [hc 3 (by decide)]; decide
  obtain ⟨r, _, hr⟩ := Finset.sum_pos_iff.mp hsum
  have h2 : 0 < n r 2 := by
    simpa [pathFour] using ha r 3 (by decide) hr (by decide)
  have h1 : n r 1 = 1 := by
    have hroot := hk r
    change (∑ w ∈ pathFour.children 0, n r w) = 1 at hroot
    simpa [pathFour_children.1] using hroot
  have hcost := hb r
  rw [path_cost, h1] at hcost
  have h2q : (1 : ℚ) ≤ n r 2 := by exact_mod_cast h2
  have h3q : (1 : ℚ) ≤ n r 3 := by exact_mod_cast hr
  norm_num at hcost
  linarith

theorem path_false_certificate :
    let n : Fin 2 → Fin 4 → ℕ := ![![0, 1, 0, 1], ![0, 1, 1, 0]]
    (∀ v, v ≠ pathFour.root → ∑ r, n r v = (![0, 2, 1, 1] : Fin 4 → ℕ) v) ∧
    (∀ r, rootDegree pathFour (n r) = 1) ∧
    (∀ r, rowCost pathFour (n r) (fun _ => 1) ≤ 3) ∧
    ¬ AncestorClosed pathFour (n 0) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv; fin_cases v <;> norm_num [Fin.sum_univ_succ]
  · intro r
    change (∑ w ∈ pathFour.children 0, _) = 1
    rw [pathFour_children.1]
    fin_cases r <;> norm_num
  · intro r
    rw [path_cost]
    fin_cases r <;> norm_num
  · intro h
    have hp := h 3 (by decide) (by decide) (by decide)
    norm_num [pathFour] at hp

theorem empty_fleet {V : Type*} [Fintype V] [DecidableEq V]
    (R : RootedTree V) (s : V → ℚ) (T : ℚ) :
    ExactFeasible R.root (edgeFlow R (fun _ => 0)) (fun _ => 0) 0 s T := by
  refine ⟨fun r => Fin.elim0 r, ?_, fun r => Fin.elim0 r, ?_⟩
  · simp [totalVisitCount]
  · simp [totalRouteFlow, edgeFlow]

theorem ceiling_rounding :
    (∃ a : Fin 2 → ℕ, (∑ r, a r) = 3 ∧ ∀ r, (1 : ℚ) + 3 * (a r : ℚ) ≤ 7) ∧
    ¬ (∃ a : Fin 2 → ℕ, (∑ r, a r) = 3 ∧ ∀ r, (1 : ℚ) + 3 * (a r : ℚ) ≤ 6) := by
  constructor <;> rw [allocation_budget_iff 2 3 (by decide) 1 3 _ (by norm_num)] <;>
    norm_num [Nat.ceilDiv_eq_add_pred_div]

theorem zero_satellite :
    (∃ a : Fin 3 → ℕ, (∑ r, a r) = 0 ∧ ∀ r, (2 : ℚ) + 4 * (a r : ℚ) ≤ 2) := by
  rw [allocation_budget_iff 3 0 (by decide) 2 4 2 (by norm_num)]
  norm_num

theorem zero_fees (m n : ℕ) (hm : 0 < m) :
    ExactFeasible HubSpokeSupportExact.depot
      (HubSpokeSupportExact.canonicalFlow m (fun _ : Unit => n))
      (HubSpokeSupportExact.required m (fun _ : Unit => n)) m (fun _ => 0) 0 := by
  apply (exact_iff_closed m n hm (fun _ => 0) 0 (by norm_num) (by norm_num)).mpr
  norm_num

theorem repeated_edges_realized : ∃ r : LegalRoute pathFour.root,
    r.visits.count 1 = 3 ∧ r.visits.count 2 = 4 ∧ r.visits.count 3 = 2 ∧
      ResourceCuts.routeServiceIn r Finset.univ (fun _ => 1) = 9 := by
  have ha : AncestorClosed pathFour ![0, 1, 2, 2] := by
    intro v hv hp hpr
    fin_cases v <;> simp_all [pathFour]
  have hk : rootDegree pathFour ![0, 1, 2, 2] = 1 := by
    change (∑ w ∈ pathFour.children 0, _) = 1
    rw [pathFour_children.1]; norm_num
  obtain ⟨r, hf, hc⟩ := single_row_realization pathFour ![0, 1, 2, 2] ha hk
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · simpa [rowVisits, pathFour, RootedTree.children, Finset.sum_filter,
      Fin.sum_univ_succ] using hc 1
  · simpa [rowVisits, pathFour, RootedTree.children, Finset.sum_filter,
      Fin.sum_univ_succ] using hc 2
  · simpa [rowVisits, pathFour, RootedTree.children, Finset.sum_filter,
      Fin.sum_univ_succ] using hc 3
  · rw [service_of_flow pathFour _ r hf, path_cost]; norm_num

end UAVProof.TreeBudgetExamples

#print axioms UAVProof.TreeBudgetExamples.signed_relaxed
#print axioms UAVProof.TreeBudgetExamples.signed_no_exact
#print axioms UAVProof.TreeBudgetExamples.nonnegative_split
#print axioms UAVProof.TreeBudgetExamples.path_no_budget_matrix
#print axioms UAVProof.TreeBudgetExamples.path_false_certificate
#print axioms UAVProof.TreeBudgetExamples.empty_fleet
#print axioms UAVProof.TreeBudgetExamples.ceiling_rounding
#print axioms UAVProof.TreeBudgetExamples.zero_satellite
#print axioms UAVProof.TreeBudgetExamples.zero_fees
#print axioms UAVProof.TreeBudgetExamples.repeated_edges_realized
