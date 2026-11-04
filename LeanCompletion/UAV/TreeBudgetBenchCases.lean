import LeanCompletion.UAV.TreeBudgetSearchStats
import LeanCompletion.UAV.TreeBudgetMemoIntegration
import LeanCompletion.UAV.TreeBudgetCheckerExamples

/-! Small canonical initial inputs. No hand-picked/reordered candidate list. -/
namespace UAVProof.TreeBudgetBenchCases
open TreeBudgetCheckerExamples TreeBudgetSearchStats TreeBudgetMemoState
open TreeBudgetPatterns TreeBudgetRow TreeBudgetMemoSearch

def sharedH (k : ℕ) : Fin 5 → ℕ := ![0, k, 1, 1, 1]
def fees : Fin 5 → ℚ := ![0, 0, 6, 6, 6]
def ps (k : ℕ) := TreeBudgetFiniteSearch.candidates hubTree (sharedH k) fees 10
def cold (k : ℕ) := memoStat (ps k) k (sharedH k) emptyCache

theorem canonical_start (k : ℕ) :
    normalize hubTree (sharedH k) = sharedH k ∧
      rootCount hubTree (sharedH k) = k := by
  constructor
  · funext v; fin_cases v <;> simp [TreeBudgetPatterns.normalize, sharedH, hubTree]
  · have hc : TreeBudgetPatterns.children hubTree hubTree.root = {1} := by decide +kernel
    simp [rootCount, hc, sharedH]

theorem complete_failure : (cold 2).1.1 = none := by decide +kernel
theorem backtracking_success : (cold 3).1.1.isSome = true := by decide +kernel
theorem canonical_failure_reuses : 0 < (cold 2).2.hits := by decide +kernel
theorem canonical_success_reuses : 0 < (cold 3).2.hits := by decide +kernel
theorem failure_saves_expansions :
    (cold 2).2.expansions < (searchStat (ps 2) 2 (sharedH 2)).2.expansions := by
  decide +kernel
theorem success_saves_expansions :
    (cold 3).2.expansions < (searchStat (ps 3) 3 (sharedH 3)).2.expansions := by
  decide +kernel

def a : Fin 5 → ℕ := ![0, 1, 0, 0, 1]
def b : Fin 5 → ℕ := ![0, 1, 0, 1, 0]

/-- Both legal choice orders leave the same unserved leaf and no route.
The failure is present in the actual canonical cold run, not an external cache. -/
theorem canonical_shared_failure :
    a ∈ ps 2 ∧ b ∈ ps 2 ∧ (∀ v, a v ≤ sharedH 2 v) ∧
      (∀ v, b v ≤ (sharedH 2 - a) v) ∧ (∀ v, b v ≤ sharedH 2 v) ∧
      (∀ v, a v ≤ (sharedH 2 - b) v) ∧
      sharedH 2 - a - b = sharedH 2 - b - a ∧
      lookup (cold 2).1.2 (0, sharedH 2 - a - b) = some none := by
  decide +kernel

theorem warm_failure_counts :
    (memoStat (ps 2) 2 (sharedH 2) (cold 2).1.2).2 =
      { calls := 1, hits := 1, lookupComparisons := 1 } := by decide +kernel
theorem warm_success_counts :
    (memoStat (ps 3) 3 (sharedH 3) (cold 3).1.2).2 =
      { calls := 1, hits := 1, lookupComparisons := 1 } := by decide +kernel

end UAVProof.TreeBudgetBenchCases

#print axioms UAVProof.TreeBudgetBenchCases.canonical_start
#print axioms UAVProof.TreeBudgetBenchCases.complete_failure
#print axioms UAVProof.TreeBudgetBenchCases.backtracking_success
#print axioms UAVProof.TreeBudgetBenchCases.canonical_failure_reuses
#print axioms UAVProof.TreeBudgetBenchCases.canonical_success_reuses
#print axioms UAVProof.TreeBudgetBenchCases.failure_saves_expansions
#print axioms UAVProof.TreeBudgetBenchCases.success_saves_expansions
#print axioms UAVProof.TreeBudgetBenchCases.canonical_shared_failure
#print axioms UAVProof.TreeBudgetBenchCases.warm_failure_counts
#print axioms UAVProof.TreeBudgetBenchCases.warm_success_counts
