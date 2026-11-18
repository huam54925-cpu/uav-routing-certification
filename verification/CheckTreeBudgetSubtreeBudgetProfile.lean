import LeanCompletion.UAV.TreeBudgetSubtreeBudgetProfile
import LeanCompletion.UAV.TreeBudgetSubtreeAutoExamples

namespace UAVProof.TreeBudgetSubtreeBudgetProfile.Check
open TreeFlowExamples TreeBudgetSubtreeDPExamples TreeBudgetSubtreeExecutable
open TreeBudgetSubtreeAutoScaleSeed TreeBudgetSubtreeIntegerWitnessSeed
open TreeBudgetSubtreeAutoExamples (observe)

-- Distinct payloads at a tied threshold; a later improvement stays selectable.
#guard records none [(3,"a"), (3,"b"), (4,"c"), (-1,"d")] = [(3,"a"), (-1,"d")]
#guard query 3 (records none [(3,"a"), (3,"b")]) = some (3,"a")

-- The fourth vertex has zero edge flow. The active subtree is the chain 0-1-2.
private def mass : Fin 4 → Nat := ![0, 2, 2, 0]
private def service : Fin 4 → Rat := ![0, -5, 7, 0]

-- With two routes each crosses edge 1 once. Splitting edge 2 as i and 2-i
-- gives row costs -5 + 2*i and -5 + 2*(2-i), for i = 0, 1, 2.
#guard (match optimize pathFour mass service 2 with
  | .least q c => q == -3 && TreeBudgetCertificate.checkCertificate pathFour mass 2 service q c
  | _ => false)

-- Compare every row and multiplicity below, at and between scaled thresholds.
#guard (Id.run do
  let s := fun v => service v / 2
  let p := prepare pathFour s 0
  let xs := buildProfile pathFour mass (val p.weight) 1
  for T in [(-7/4 : Rat), -3/2, -5/4, -1/2, 0] do
    let actual := ((query (TreeBudgetSubtreeInteger.floorBudget p.scale T) xs).map Prod.snd).map
      (certificate pathFour)
    unless actual.map observe == (solveAuto pathFour mass s 2 T).map observe do return false
    unless actual.isSome == decide ((-3/2 : Rat) ≤ T) do return false
  return true)

#guard (match optimize pointTree (fun _ => 0) (fun _ => 0) 0 with
  | .allBudgets c => c.size == 0
  | _ => false)

-- Zero root mass passes the guard, but a positive descendant still needs a row.
#guard (match optimize pathFour ![0,0,1,0] service 0 with
  | .infeasible => true
  | _ => false)

-- Positive fleet, compatible root mass, and an unreachable positive grandchild.
#guard (match optimize pathFour ![0,1,0,1] service 1 with
  | .infeasible => true
  | _ => false)

#guard (match optimize pointTree (fun _ => 0) (fun _ => 0) (2^200) with
  | .infeasible => true
  | _ => false)

#print axioms query_records
#print axioms query_records_none
#print axioms records_decreasing
#print axioms query_at_record
#print axioms peak_le
#print axioms accept_iff
#print axioms query_scored
#print axioms profile_query_eq_solve
#print axioms profile_query_eq_auto
#print axioms accept_zero
#print axioms profile_query_eq_materialized
#print axioms solveAuto_zero_budget_independent
#print axioms optimize_spec
#print axioms least_exact_iff

end UAVProof.TreeBudgetSubtreeBudgetProfile.Check
