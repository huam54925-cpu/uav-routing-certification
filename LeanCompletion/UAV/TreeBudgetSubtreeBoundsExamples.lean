import LeanCompletion.UAV.TreeBudgetSubtreeGridBounds
import LeanCompletion.UAV.TreeBudgetSubtreeStatsGlobalBounds
import LeanCompletion.UAV.TreeBudgetSubtreeIntegerStats
import LeanCompletion.UAV.TreeBudgetSubtreeDPExamples
import LeanCompletion.UAV.TreeBudgetSubtreeWitnessDP

/-! Executed boundary checks supplement the general theorems. -/
namespace UAVProof.TreeBudgetSubtreeBoundsExamples
open TreeFlowExistence TreeFlowExamples TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats
open TreeBudgetSubtreeState TreeBudgetSubtreeDPExamples


example : TreeBudgetSubtreeInteger.floorBudget 1 (-1 / 2) = -1 := by decide +kernel
example : TreeBudgetSubtreeInteger.floorBudget 3 (-1 / 2) = -2 := by decide +kernel
example : (compositionProfile 1 100).compositionCalls = 102 := by decide +kernel

def checkCase {N : ℕ} (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (w : Fin N → ℤ) (D m : ℕ) (T : ℚ) : IO Unit := do
  let qs := (List.finRange N).filter fun v => v != R.root
  let P := (qs.map fun v => columnFactor m (H v)).prod
  let U := (qs.map H).foldl max 0
  let r := checkCompactStats R H s m T
  let j := TreeBudgetSubtreeInteger.checkMeasured R H w m (TreeBudgetSubtreeInteger.floorBudget D T)
  unless r.value == j.value && r.stats == j.stats do
    throw (IO.userError "integer answer/statistics mismatch")
  let cert := TreeBudgetSubtreeWitness.solve R H s m T
  unless cert.isSome == r.value do
    throw (IO.userError "witness solver completeness mismatch")
  match cert with
  | none => pure ()
  | some c =>
    unless TreeBudgetCertificate.checkCertificate R H m s T c && c.size == m do
      throw (IO.userError "original checker rejected generated certificate")
  let rt := rootFold ((childrenList R R.root).map (computeCompact R H s m))
  let jt := TreeBudgetSubtreeInteger.rootFold ((childrenList R R.root).map (TreeBudgetSubtreeInteger.compute R H w m))
  unless rt == jt.map (TreeBudgetSubtreeInteger.liftRoot D) do
    throw (IO.userError "root ordered-table mismatch")
  let t := r.stats
  let n := N - 1
  unless t.nodeCalls == n && t.rangeChoices + n == t.compositionCalls &&
      t.compositionCalls ≤ n * (m + 1) * (U + 1) * P &&
      t.columnsGenerated ≤ n * P && t.columnsAccepted ≤ n * P &&
      t.subsetCalls ≤ n * P && t.insidePairs + t.rootPairs ≤ n * P &&
      t.rootRejected ≤ n * P && t.ratAdds ≤ m * n * P && t.ratMuls ≤ m * n * P &&
      t.dedupInput ≤ 2 * n * P && t.dedupOutput ≤ 2 * n * P &&
      t.eqCalls ≤ n * P ^ 2 && t.acceptCalls ≤ P &&
      t.maxRawTable ≤ P && t.maxDedupTable ≤ P &&
      logicalWork t ≤ 32 * N * (m + 1) * (U + 1) * P ^ 2 do
    throw (IO.userError "logical-work envelope mismatch")
  for v in qs do
    let a := computeCompact R H s m v
    let b := TreeBudgetSubtreeInteger.compute R H w m v
    unless a == b.map (TreeBudgetSubtreeInteger.liftState D) do
      throw (IO.userError "local ordered-table mismatch")
    let es := TreeBudgetSubtreeWitness.compute R H s m v
    unless a == es.map TreeBudgetSubtreeWitness.Entry.key do
      throw (IO.userError "witness ordered-table mismatch")
    unless (w v : ℚ) == (D : ℚ) * linearWeight R s v do
      throw (IO.userError "invalid regression scaling contract")

def runCases : IO Unit := do
  runEvaluationCases
  let mut count := 0
  for m in [0:4] do
    for H in [![0,0,0,0], ![0,0,1,0], ![0,1,1,3], ![0,2,3,0], ![0,1,1,1], ![0,2,0,2]] do
      for T in [(-3/2 : ℚ), -1, 0, 3/2, 4] do
        checkCase pathFour H (fun _ => 0) (fun _ => 0) 1 m T
        checkCase pathFour H ![99,0,-3,10] ![0,0,-3,7] 1 m T
        checkCase pathFour H ![99,1/2,-3/2,7/2] ![0,1,-2,4] 2 m T
        checkCase forkTree H (fun _ => 0) (fun _ => 0) 1 m T
        count := count + 4
  checkCase pointTree (fun _ => 99) (fun _ => 99) (fun _ => 0) 1 0 (-1/2)
  checkCase pointTree (fun _ => 99) (fun _ => 99) (fun _ => 0) 1 1 (-1/2)
  checkCase pathFour ![0,1,1,100] (fun _ => 0) (fun _ => 0) 1 1 0
  IO.println s!"PASS: {count + 3} table/integer/statistics/certificate checks, plus original 21 DP cases"

#eval runCases

end UAVProof.TreeBudgetSubtreeBoundsExamples
