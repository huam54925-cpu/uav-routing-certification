import LeanCompletion.UAV.TreeBudgetSubtreeBudgetQueries
import LeanCompletion.UAV.TreeBudgetSubtreeAutoExamples

namespace UAVProof.TreeBudgetSubtreeBudgetProfile.CheckQueries
open TreeFlowExamples TreeBudgetSubtreeDPExamples TreeBudgetSubtreeIntegerWitnessSeed
open TreeBudgetSubtreeAutoExamples (observe)

#guard (Id.run do
  let H := (![0,2,2,0] : Fin 4 → Nat)
  let s := (![0,-5/2,7/2,0] : Fin 4 → Rat)
  let table := prepareQueries pathFour H s 2
  for T in [(-7/4 : Rat), -3/2, -5/4, -1/2, 0] do
    let (found, tests) := table.lookup T
    unless tests ≤ table.breakpoints && found.map observe == (solveAuto pathFour H s 2 T).map observe do
      return false
  return true)

#guard ((prepareQueries pointTree (fun _ => 0) (fun _ => 0) 0).lookup (-100)).1.isSome
#guard (Id.run do
  let table := prepareQueries pointTree (fun _ => 0) (fun _ => 0) (2^200)
  return table.breakpoints == 0 && (table.lookup 0).1.isNone && (table.lookup 0).2 == 0)

#print axioms lookup_comparisons
#print axioms prepareQueries_reject
#print axioms lookup_eq_auto

end UAVProof.TreeBudgetSubtreeBudgetProfile.CheckQueries
