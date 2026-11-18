import LeanCompletion.UAV.TreeBudgetSubtreeRouteOutput
import LeanCompletion.UAV.TreeBudgetSubtreeAutoExamples

namespace UAVProof.TreeBudgetSubtreeRouteOutput.Check
open TreeFlowExamples TreeBudgetSubtreeDPExamples TreeBudgetSubtreeIntegerWitnessSeed
open TreeBudgetCertificate TreeBudgetRepresentationBridge TreeBudgetPatterns

-- Exercise the complete certificate returned at a negative optimal budget.
#guard (Id.run do
  let H := (![0,2,2,0] : Fin 4 → Nat)
  let s := (![0,-5,7,0] : Fin 4 → Rat)
  let some c := solveAuto pathFour H s 2 (-3) | return false
  let words := vertices pathFour c
  return checkCertificate pathFour H 2 s (-3) c &&
    words == [[0,1,2,1,0], [0,1,2,1,0]] && (words.map List.length).sum == 10)

-- The first positive crossing serves the whole subtree, later crossings bounce.
#guard (tour pathFour ![99,1,2,1] 0).arrivals = [1,2,3,2,1,2,1,0]
#guard (vertices pointTree ⟨0, Fin.elim0, Fin.elim0⟩).isEmpty

#print axioms tour_weight
#print axioms tour_flow
#print axioms tour_length
#print axioms route_vertices
#print axioms round_trip
#print axioms output_size
#print axioms output_moves
#print axioms output_word

end UAVProof.TreeBudgetSubtreeRouteOutput.Check
