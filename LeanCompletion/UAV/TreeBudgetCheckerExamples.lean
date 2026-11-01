import LeanCompletion.UAV.TreeBudgetChecker
import LeanCompletion.UAV.TreeBudgetExamples

/-! Kernel-checked executable regressions, including signed fees, exact budgets,
empty fleets, incompatible demands, disconnected positive flow, and compression. -/
namespace UAVProof.TreeBudgetCheckerExamples

open TreeFlowExistence TreeBudgetChecker TreeBudgetCertificate TreeBudgetCriterion
open TreeFlowExamples

def hubGraph : SimpleGraph (Fin 5) where
  Adj u v := (u = 1 ∧ v ≠ 1) ∨ (u ≠ 1 ∧ v = 1)
  symm := by intro u v h; rcases h with h | h <;> simp_all
  loopless := ⟨fun v => by simp⟩

instance : DecidableRel hubGraph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def hubTree : RootedTree (Fin 5) where
  graph := hubGraph
  isTree := by
    classical
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨?_, ?_⟩
    · apply (SimpleGraph.connected_iff_exists_forall_reachable hubGraph).mpr
      refine ⟨1, fun w => ?_⟩
      by_cases hw : w = 1
      · subst w; exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable (show hubGraph.Adj 1 w from Or.inl ⟨rfl, hw⟩)
    · simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      have he : hubGraph.edgeFinset =
          {s((0 : Fin 5), 1), s((1 : Fin 5), 2), s((1 : Fin 5), 3), s((1 : Fin 5), 4)} := by
        ext e
        induction e using Sym2.inductionOn with
        | hf u v =>
          fin_cases u <;> fin_cases v <;>
            simp [SimpleGraph.mem_edgeFinset, hubGraph, Sym2.eq]
      rw [he]
      decide +kernel
  root := 0
  parent := ![0, 0, 1, 1, 1]
  parent_root := rfl
  rank := ![2, 1, 0, 0, 0]
  parent_rank := by decide +kernel
  adj_iff := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide

def hubDemands (m : ℕ) : Fin 5 → ℕ := ![0, m + 3, 1, 1, 1]
def hubFees : Fin 5 → ℚ := ![999, 0, 6, 6, 6]

theorem two_routes_reject :
    checkTreeBudget hubTree (hubDemands 2) 2 hubFees 10 = false := by decide +kernel

theorem three_routes_accept :
    checkTreeBudget hubTree (hubDemands 3) 3 hubFees 10 = true := by decide +kernel

/-- Changing fleet size alone does not preserve exact hub demand compatibility. -/
theorem fixed_hub_demand_reject :
    checkTreeBudget hubTree (hubDemands 2) 3 hubFees 10 = false := by decide +kernel

theorem three_routes_exist : BudgetRoutes hubTree (hubDemands 3) 3 hubFees 10 :=
  (check_eq_true_iff ..).mp three_routes_accept

theorem two_routes_impossible : ¬ BudgetRoutes hubTree (hubDemands 2) 2 hubFees 10 := by
  intro h
  have ht := (check_eq_true_iff ..).mpr h
  rw [two_routes_reject] at ht
  contradiction

theorem empty_negative_budget_accept :
    checkTreeBudget pathFour ![999, 0, 0, 0] 0 (fun _ => 0) (-1) = true := by decide +kernel

/-- Integer compatibility alone does not exclude positive flow away from the depot. -/
theorem empty_positive_demand_reject :
    compatible pathFour ![0, 1, 1, 0] 0 = true ∧
    checkTreeBudget pathFour ![0, 1, 1, 0] 0 (fun _ => 0) 0 = false := by decide +kernel

theorem negative_requirement_reject :
    checkTreeBudget pathFour ![0, 0, 0, 1] 1 (fun _ => 0) 100 = false := by decide +kernel

theorem ancestor_gap_reject :
    compatible pathFour (fun _ => 1) 1 = true ∧
    checkTreeBudget pathFour (fun _ => 1) 1 (fun _ => 0) 100 = false := by decide +kernel

/-- The edge increments are 0, 6, -2: early rejection at cost 6 would be unsound. -/
theorem signed_exact_budget_accept :
    checkTreeBudget pathFour ![0, 2, 2, 1] 1 ![999, 0, 6, -8] 4 = true := by decide +kernel

theorem signed_lower_budget_reject :
    checkTreeBudget pathFour ![0, 2, 2, 1] 1 ![999, 0, 6, -8] 3 = false := by decide +kernel

theorem zero_fees_accept :
    checkTreeBudget hubTree (hubDemands 2) 2 (fun _ => 0) 0 = true := by decide +kernel

def compressed : Certificate (Fin 5) := ⟨1, fun _ => ![0, 1, 0, 0, 0], fun _ => 3⟩

theorem compressed_accept :
    checkCertificate hubTree ![999, 3, 0, 0, 0] 3 (fun _ => 0) 0 compressed = true := by
  decide +kernel

theorem wrong_count_reject :
    checkCertificate hubTree ![999, 3, 0, 0, 0] 2 (fun _ => 0) 0 compressed = false := by
  decide +kernel

theorem wrong_column_reject :
    checkCertificate hubTree ![999, 3, 1, 0, 0] 3 (fun _ => 0) 0 compressed = false := by
  decide +kernel

theorem nonzero_root_certificate_reject :
    checkCertificate hubTree ![999, 3, 0, 0, 0] 3 (fun _ => 0) 0
      ⟨1, fun _ => ![1, 1, 0, 0, 0], fun _ => 3⟩ = false := by decide +kernel

#eval checkTreeBudget hubTree (hubDemands 2) 2 hubFees 10
#eval checkTreeBudget hubTree (hubDemands 3) 3 hubFees 10
#eval (solve hubTree (hubDemands 3) 3 hubFees 10).map fun c =>
  (c.size, List.ofFn c.count, List.ofFn (fun i => List.ofFn (c.row i)))

end UAVProof.TreeBudgetCheckerExamples

#print axioms UAVProof.TreeBudgetCheckerExamples.two_routes_reject
#print axioms UAVProof.TreeBudgetCheckerExamples.three_routes_accept
#print axioms UAVProof.TreeBudgetCheckerExamples.fixed_hub_demand_reject
#print axioms UAVProof.TreeBudgetCheckerExamples.three_routes_exist
#print axioms UAVProof.TreeBudgetCheckerExamples.two_routes_impossible
#print axioms UAVProof.TreeBudgetCheckerExamples.empty_negative_budget_accept
#print axioms UAVProof.TreeBudgetCheckerExamples.empty_positive_demand_reject
#print axioms UAVProof.TreeBudgetCheckerExamples.negative_requirement_reject
#print axioms UAVProof.TreeBudgetCheckerExamples.ancestor_gap_reject
#print axioms UAVProof.TreeBudgetCheckerExamples.signed_exact_budget_accept
#print axioms UAVProof.TreeBudgetCheckerExamples.signed_lower_budget_reject
#print axioms UAVProof.TreeBudgetCheckerExamples.zero_fees_accept
#print axioms UAVProof.TreeBudgetCheckerExamples.compressed_accept
#print axioms UAVProof.TreeBudgetCheckerExamples.wrong_count_reject
#print axioms UAVProof.TreeBudgetCheckerExamples.wrong_column_reject
#print axioms UAVProof.TreeBudgetCheckerExamples.nonzero_root_certificate_reject
