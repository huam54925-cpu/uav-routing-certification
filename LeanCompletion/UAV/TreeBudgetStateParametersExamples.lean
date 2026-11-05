import LeanCompletion.UAV.TreeBudgetStateParameters
import LeanCompletion.UAV.TreeBudgetBranchExamples

/-! Kernel-checked boundary cases for numerical state-space parameters.
The existing path and one-vertex trees are reused. Root values are deliberately
large to check that only nonroot multiplicities enter S, M, t and U. -/
namespace UAVProof.TreeBudgetStateParametersExamples
open TreeBudgetMemoBounds TreeBudgetStateParameters TreeFlowExamples
open TreeBudgetBranchExamples

def zeroNonroot : Fin 4 → ℕ := ![999, 0, 0, 0]

theorem zero_nonroot_ignores_large_root :
    stateBound pathFour zeroNonroot = 1 ∧
      totalMultiplicity pathFour zeroNonroot = 0 ∧
      positiveCount pathFour zeroNonroot = 0 ∧
      maxMultiplicity pathFour zeroNonroot = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The maximum over the empty nonroot set is zero, and its product is one. -/
theorem root_only_has_empty_parameters :
    nonrootVertices depotOnly = ∅ ∧
      stateBound depotOnly (fun _ => 999) = 1 ∧
      totalMultiplicity depotOnly (fun _ => 999) = 0 ∧
      positiveCount depotOnly (fun _ => 999) = 0 ∧
      maxMultiplicity depotOnly (fun _ => 999) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def unitNonroot : Fin 4 → ℕ := ![999, 1, 1, 1]

/-- When every active value is one, both parameter bounds are attained. -/
theorem unit_values_attain_both_bounds :
    stateBound pathFour unitNonroot = 8 ∧
      totalMultiplicity pathFour unitNonroot = 3 ∧
      positiveCount pathFour unitNonroot = 3 ∧
      maxMultiplicity pathFour unitNonroot = 1 ∧
      stateBound pathFour unitNonroot = 2 ^ totalMultiplicity pathFour unitNonroot ∧
      stateBound pathFour unitNonroot =
        (maxMultiplicity pathFour unitNonroot + 1) ^ positiveCount pathFour unitNonroot := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def sparseNonroot : Fin 4 → ℕ := ![999, 2, 0, 3]

/-- Zero coordinates contribute one to the product and nothing to the active count. -/
theorem sparse_nonuniform_parameters :
    stateBound pathFour sparseNonroot = 12 ∧
      totalMultiplicity pathFour sparseNonroot = 5 ∧
      positiveCount pathFour sparseNonroot = 2 ∧
      maxMultiplicity pathFour sparseNonroot = 3 ∧
      2 ^ totalMultiplicity pathFour sparseNonroot = 32 ∧
      (maxMultiplicity pathFour sparseNonroot + 1) ^ positiveCount pathFour sparseNonroot = 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def singlePositive : Fin 4 → ℕ := ![999, 0, 4, 0]

/-- One positive coordinate attains (U+1)^t even when the total-mass bound is loose. -/
theorem single_positive_attains_max_bound :
    stateBound pathFour singlePositive = 5 ∧
      totalMultiplicity pathFour singlePositive = 4 ∧
      positiveCount pathFour singlePositive = 1 ∧
      maxMultiplicity pathFour singlePositive = 4 ∧
      stateBound pathFour singlePositive =
        (maxMultiplicity pathFour singlePositive + 1) ^ positiveCount pathFour singlePositive := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end UAVProof.TreeBudgetStateParametersExamples

#print axioms UAVProof.TreeBudgetStateParametersExamples.zero_nonroot_ignores_large_root
#print axioms UAVProof.TreeBudgetStateParametersExamples.root_only_has_empty_parameters
#print axioms UAVProof.TreeBudgetStateParametersExamples.unit_values_attain_both_bounds
#print axioms UAVProof.TreeBudgetStateParametersExamples.sparse_nonuniform_parameters
#print axioms UAVProof.TreeBudgetStateParametersExamples.single_positive_attains_max_bound
