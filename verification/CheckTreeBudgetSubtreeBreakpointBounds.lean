import LeanCompletion.UAV.TreeBudgetSubtreeBreakpointBounds
import LeanCompletion.UAV.TreeBudgetSubtreeAutoExamples

namespace UAVProof.TreeBudgetSubtreeBudgetProfile.CheckBounds
open TreeFlowExamples

-- Ignore both the root's large coefficient and the zero-mass fourth vertex.
private def H : Fin 4 → Nat := ![99,2,2,0]
private def w : Fin 4 → Int := ![101,-10,4,17]

example : divisor pathFour H w = 2 := by decide +kernel
example : total pathFour H w = -12 := by decide +kernel
example : positiveTotal pathFour H w = 8 := by decide +kernel
example : divisor pathFour (fun _ => 0) w = 0 := by decide +kernel
#guard (buildProfile pathFour H w 1).getLast?.map Prod.fst == some (-6)
#guard (records none [(2,0), (2,1), (4,2), (-3,3), (-3,4)]).map Prod.snd == [0,3]

#print axioms records_necessary
#print axioms breakpoint_bound
#print axioms breakpoint_bound_zero
#print axioms breakpoint_bound_single

end UAVProof.TreeBudgetSubtreeBudgetProfile.CheckBounds
