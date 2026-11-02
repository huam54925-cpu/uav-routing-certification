import LeanCompletion.UAV.TreeBudgetBranchSearch
import LeanCompletion.UAV.TreeBudgetCheckerExamples

/-! Kernel-checked executable regressions for certificate splitting, merging and branch search. -/
namespace UAVProof.TreeBudgetBranchExamples
open TreeFlowExistence TreeBudgetPatterns TreeBudgetMatrix TreeBudgetCertificate
open TreeBudgetRootFactorization TreeBudgetBranchCertificate
open TreeBudgetBranchSearch TreeBudgetFiniteSearch TreeBudgetChecker
open TreeBudgetExamples TreeFlowExamples

def directCounts : Fin 3 → ℕ := ![2, 99, 3]
def directFees : Fin 3 → ℚ := ![10, 999, 2]

def directLocals (c : RootChild centerThree) : Certificate (Fin 3) :=
  if c.val = 0 then ofEntries [(![1, 0, 0], 2)]
  else ofEntries [(![0, 0, 1], 3)]

theorem direct_locals_checked : ∀ c : RootChild centerThree,
    checkCertificate centerThree (branchMultiplicity centerThree directCounts c)
      (directCounts c.val) directFees 10 (directLocals c) = true := by decide +kernel

theorem direct_merge_checked :
    checkCertificate centerThree directCounts 5 directFees 10
      (mergeBranches centerThree directLocals) = true := by decide +kernel

theorem direct_merge_sound :
    checkCertificate centerThree directCounts 5 directFees 10
      (mergeBranches centerThree directLocals) = true :=
  mergeBranches_checked _ _ _ _ _ _ (by decide +kernel) direct_locals_checked

def leftChild : RootChild centerThree := ⟨0, by decide +kernel⟩
def rightChild : RootChild centerThree := ⟨2, by decide +kernel⟩

def withZeroEntries : Certificate (Fin 3) :=
  ofEntries [(![0, 0, 1], 0), (![1, 0, 0], 2), (![0, 0, 1], 3), (![1, 0, 0], 0)]

theorem zero_entries_checked :
    checkCertificate centerThree directCounts 5 directFees 10 withZeroEntries = true := by
  decide +kernel

theorem split_keeps_zero_and_order :
    entries (splitBranch centerThree withZeroEntries leftChild) =
      [(![1, 0, 0], 2), (![1, 0, 0], 0)] := by decide +kernel

theorem split_checked :
    checkCertificate centerThree (branchMultiplicity centerThree directCounts leftChild)
      2 directFees 10 (splitBranch centerThree withZeroEntries leftChild) = true :=
  splitBranch_checked _ _ _ _ _ _ _ zero_entries_checked

theorem merge_split_keeps_four_entries :
    (mergeBranches centerThree (splitBranch centerThree withZeroEntries)).size = 4 := by
  decide +kernel

theorem merge_split_perm :
    (entries (mergeBranches centerThree (splitBranch centerThree withZeroEntries))).Perm
      (entries withZeroEntries) :=
  merge_split_entries_perm _ _ _ _ _ _ ((checkCertificate_eq_true_iff ..).mp zero_entries_checked)

theorem merge_split_changes_order :
    entries (mergeBranches centerThree (splitBranch centerThree withZeroEntries)) ≠
      entries withZeroEntries := by decide +kernel

theorem empty_branch_rejects_zero_placeholder :
    checkCertificate centerThree (branchMultiplicity centerThree (fun _ => 0) leftChild)
      0 (fun _ => 0) (-1) (ofEntries [((fun _ => 0), 0)]) = false := by decide +kernel

def depotOnly : RootedTree (Fin 1) where
  graph := ⊥
  isTree := by
    classical
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨?_, ?_⟩
    · apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
      refine ⟨0, fun w => ?_⟩
      have hw : w = 0 := Subsingleton.elim _ _
      subst w
      exact SimpleGraph.Reachable.refl _
    · simp [Nat.card_eq_fintype_card]
  root := 0
  parent := fun _ => 0
  parent_root := rfl
  rank := fun _ => 0
  parent_rank := by intro v hv; exact (hv (Subsingleton.elim _ _)).elim
  adj_iff := by intro u v; fin_cases u; fin_cases v; simp

theorem depot_only_negative_budget_empty :
    (searchByRoot depotOnly (fun _ => 999) 0 (fun _ => 999) (-1)).map
      Certificate.size = some 0 := by
  decide +kernel

theorem depot_only_output_checked :
    (searchByRoot depotOnly (fun _ => 999) 0 (fun _ => 999) (-1)).map
      (checkCertificate depotOnly (fun _ => 999) 0 (fun _ => 999) (-1)) = some true := by
  decide +kernel

theorem zero_root_deep_positive_reject :
    (searchByRoot pathFour ![7, 0, 1, 0] 0 (fun _ => 0) 100).isSome = false := by decide +kernel

theorem wrong_fleet_reject :
    (searchByRoot centerThree directCounts 4 directFees 10).isSome = false := by decide +kernel

theorem other_branch_negative_cannot_rescue :
    (searchByRoot centerThree ![1, 99, 1] 2 ![11, 999, -100] 10).isSome = false := by decide +kernel

theorem same_branch_signed_cancellation :
    (searchByRoot pathFour ![7, 1, 1, 1] 1 ![999, 0, 6, -8] 4).isSome = true := by decide +kernel

theorem branch_search_output_checked :
    (searchByRoot centerThree directCounts 5 directFees 10).map
      (checkCertificate centerThree directCounts 5 directFees 10) = some true := by decide +kernel

theorem new_old_flags_agree :
    (searchByRoot centerThree directCounts 5 directFees 10).isSome =
      (search centerThree directCounts 5 directFees 10).isSome := by decide +kernel

theorem negative_integer_requirement_reject :
    checkTreeBudgetByRoot pathFour ![0, 0, 0, 1] 1 (fun _ => 0) 100 = false := by decide +kernel

theorem compatible_but_disconnected_reject :
    compatible pathFour ![0, 1, 1, 0] 0 = true ∧
      checkTreeBudgetByRoot pathFour ![0, 1, 1, 0] 0 (fun _ => 0) 100 = false := by decide +kernel

theorem demand_signed_accept :
    checkTreeBudgetByRoot pathFour ![999, 2, 2, 1] 1 ![999, 0, 6, -8] 4 = true := by decide +kernel

end UAVProof.TreeBudgetBranchExamples

#print axioms UAVProof.TreeBudgetBranchExamples.direct_locals_checked
#print axioms UAVProof.TreeBudgetBranchExamples.direct_merge_checked
#print axioms UAVProof.TreeBudgetBranchExamples.direct_merge_sound
#print axioms UAVProof.TreeBudgetBranchExamples.zero_entries_checked
#print axioms UAVProof.TreeBudgetBranchExamples.split_keeps_zero_and_order
#print axioms UAVProof.TreeBudgetBranchExamples.split_checked
#print axioms UAVProof.TreeBudgetBranchExamples.merge_split_keeps_four_entries
#print axioms UAVProof.TreeBudgetBranchExamples.merge_split_perm
#print axioms UAVProof.TreeBudgetBranchExamples.merge_split_changes_order
#print axioms UAVProof.TreeBudgetBranchExamples.empty_branch_rejects_zero_placeholder
#print axioms UAVProof.TreeBudgetBranchExamples.depot_only_negative_budget_empty
#print axioms UAVProof.TreeBudgetBranchExamples.depot_only_output_checked
#print axioms UAVProof.TreeBudgetBranchExamples.zero_root_deep_positive_reject
#print axioms UAVProof.TreeBudgetBranchExamples.wrong_fleet_reject
#print axioms UAVProof.TreeBudgetBranchExamples.other_branch_negative_cannot_rescue
#print axioms UAVProof.TreeBudgetBranchExamples.same_branch_signed_cancellation
#print axioms UAVProof.TreeBudgetBranchExamples.branch_search_output_checked
#print axioms UAVProof.TreeBudgetBranchExamples.new_old_flags_agree
#print axioms UAVProof.TreeBudgetBranchExamples.negative_integer_requirement_reject
#print axioms UAVProof.TreeBudgetBranchExamples.compatible_but_disconnected_reject
#print axioms UAVProof.TreeBudgetBranchExamples.demand_signed_accept
