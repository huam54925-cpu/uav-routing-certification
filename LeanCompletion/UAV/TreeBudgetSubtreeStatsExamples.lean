import LeanCompletion.UAV.TreeBudgetSubtreeFull
import LeanCompletion.UAV.TreeBudgetSubtreeFast
import LeanCompletion.UAV.TreeBudgetSubtreeDPExamples

/-! Hand-computable counters, short-circuit order, empty-prefix work and
full/compact state collisions. These execute the new implementations. -/
namespace UAVProof.TreeBudgetSubtreeStats
open TreeFlowExamples TreeBudgetSubtreeExecutable TreeBudgetSubtreeDPExamples

def countRegression : IO Unit := do
  let tests : List (String × Bool) := [
    ("distinct dedup", dedupCounted ([1,2,3,4] : List Nat) == ([1,2,3,4], 6)),
    ("equal dedup", dedupCounted ([2,2,2,2] : List Nat) == ([2], 3)),
    ("rightmost order", dedupCounted ([1,2,1,3,2] : List Nat) == ([1,3,2], 7)),
    ("successful scan stops", memberCounted 2 [1,2,2,3] == (true, 2)),
    ("accept stops", anyCounted (fun n : Nat => n == 2) [1,2,3] == (true, 2)),
    ("single coordinate range", (compositionsStats 1 4).stats.rangeChoices == 5),
    ("single coordinate recursive calls", (compositionsStats 1 4).stats.compositionCalls == 6),
    ("single coordinate optimization", (compositionsFastStats 1 4).stats.rangeChoices == 0),
    ("zero route empty vector", (compositionsStats 0 0).value.length == 1),
    ("zero route impossible sum", (compositionsStats 0 1).value.isEmpty)]
  for (name, ok) in tests do
    unless ok do throw (IO.userError s!"counter regression: {name}")
  let e : ExecCompactState 1 := ⟨#[true].toVector, #[0].toVector⟩
  let r := rootFoldStats [[e], [e]]
  unless r.value.isEmpty && r.stats.rootPairs == 2 && r.stats.rootRejected == 1 &&
      r.stats.ratAdds == 2 do throw (IO.userError "root arithmetic precedes rejection")
  let r := insideCostsStats e.active e.cost [[], [e]]
  unless r.value.isEmpty && r.stats.insidePairs == 1 && r.stats.subsetCalls == 1 do
    throw (IO.userError "empty head must still compute tail")
  let h : Fin 4 → Nat := ![0,2,3,0]
  let c := computeCompact pathFour h (fun _ => 0) 2 2
  let f := computeFull pathFour h (fun _ => 0) 2 2
  unless c.length == 3 && f.length == 4 do throw (IO.userError "full-count reference collapsed q")
  unless (computeCompactStats pathFour h (fun _ => 0) 2 2).value == c &&
      (computeFullStats pathFour h (fun _ => 0) 2 2).value == f &&
      computeFast pathFour h (fun _ => 0) 2 2 == c do
    throw (IO.userError "ordered table preservation")
  runEvaluationCases
  IO.println "PASS: 14 counter/reference checks plus 21 original DP regressions"

#eval countRegression

end UAVProof.TreeBudgetSubtreeStats
