import LeanCompletion.UAV.TreeBudgetVectorChecker
import LeanCompletion.UAV.TreeFlowExamples

/-! Kernel-checked representation boundaries: empty arrays, truncated subtraction,
root normalization, negative budgets, unreduced fractions, and structural guards.
These examples do not assert runtime bounds. -/
namespace UAVProof.TreeBudgetRepresentationExamples
open TreeBudgetVector TreeBudgetVectorChecker TreeFlowExamples

theorem empty_vector_checks :
    eqB (encode (n := 0) Fin.elim0) (encode Fin.elim0) = true ∧
      leB (encode (n := 0) Fin.elim0) (encode Fin.elim0) = true ∧
      isZero (encode (n := 0) Fin.elim0) = true := by
  decide +kernel

theorem truncated_subtraction :
    sub (encode ![1, 0, 4]) (encode ![2, 3, 1]) = encode ![0, 0, 3] ∧
      leB (encode ![2, 3, 1]) (encode ![1, 0, 4]) = false := by
  decide +kernel

theorem materialized_root_normalization :
    normalize pathFour (encode ![999, 1, 2, 0]) = encode ![0, 1, 2, 0] := by
  decide +kernel

def H : Vector ℕ 4 := encode ![0, 1, 1, 1]
def p : Vector ℕ 4 := encode ![0, 1, 1, 0]
def signedFees : Vector ℤ 4 := Vector.ofFn ![0, -2, 1, 0]

/-- Exact cost is -3, so a negative budget is not automatically infeasible. -/
theorem signed_budget_boundary :
    rowValidB pathFour H signedFees (-3) p = true ∧
      rowValidB pathFour H signedFees (-4) p = false := by
  decide +kernel

/-- -2/4 + (2/8 - 2/4) = -6/8, using deliberately unreduced input. -/
theorem unreduced_signed_fractions :
    rowValidB pathFour H
      (scaleFees (Vector.ofFn ![0, -2, 2, 0]) (encode ![2, 4, 8, 3]) 8)
      (scaleBudget (encode ![2, 4, 8, 3]) (-6) 8) p = true ∧
    rowValidB pathFour H
      (scaleFees (Vector.ofFn ![0, -2, 2, 0]) (encode ![2, 4, 8, 3]) 8)
      (scaleBudget (encode ![2, 4, 8, 3]) (-7) 8) p = false := by
  decide +kernel

/-- Root, capacity, and parent support checks cannot be dropped even with a
permissive signed-integer budget. -/
theorem structural_rejections :
    rowValidB pathFour H signedFees 100 (encode ![1, 1, 1, 0]) = false ∧
      rowValidB pathFour H signedFees 100 (encode ![0, 1, 2, 0]) = false ∧
      rowValidB pathFour H signedFees 100 (encode ![0, 1, 0, 1]) = false := by
  decide +kernel

end UAVProof.TreeBudgetRepresentationExamples

#print axioms UAVProof.TreeBudgetRepresentationExamples.empty_vector_checks
#print axioms UAVProof.TreeBudgetRepresentationExamples.truncated_subtraction
#print axioms UAVProof.TreeBudgetRepresentationExamples.materialized_root_normalization
#print axioms UAVProof.TreeBudgetRepresentationExamples.signed_budget_boundary
#print axioms UAVProof.TreeBudgetRepresentationExamples.unreduced_signed_fractions
#print axioms UAVProof.TreeBudgetRepresentationExamples.structural_rejections
