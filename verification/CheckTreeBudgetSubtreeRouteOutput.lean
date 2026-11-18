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
  let indices := (List.finRange c.size).flatMap fun i => List.replicate (c.count i) i
  unless indices.length == words.length do return false
  for (i, word) in indices.zip words do
    let visits := word.tail.dropLast
    for v in List.finRange 4 do
      let projected := if v = pathFour.root then 0 else routeFlow word (pathFour.parent v) v
      unless projected == c.row i v do return false
    unless (visits.map s).sum == cost pathFour (c.row i) s && (visits.map s).sum == -3 do
      return false
  return checkCertificate pathFour H 2 s (-3) c &&
    words == [[0,1,2,1,0], [0,1,2,1,0]] && (words.map List.length).sum == 10)

-- The first positive crossing serves the whole subtree, later crossings bounce.
#guard (tour pathFour ![99,1,2,1] 0).arrivals = [1,2,3,2,1,2,1,0]
-- Binary multiplicity at the second edge expands into an explicit output word.
#guard (List.range 6).all fun q =>
  (0 :: (tour pathFour ![0,1,2^q,0] 0).arrivals).length == 2^(q+1)+3

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
