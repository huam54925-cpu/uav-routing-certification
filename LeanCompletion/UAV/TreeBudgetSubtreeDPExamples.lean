import LeanCompletion.UAV.TreeBudgetSubtreeDP
import LeanCompletion.UAV.TreeFlowExamples

/-! Actual evaluation of the new executor, including signed rational costs,
root separation and collisions of different local columns after compression. -/
namespace UAVProof.TreeBudgetSubtreeDPExamples
open TreeFlowExistence TreeFlowExamples TreeBudgetSubtreeExecutable

def pointTree : RootedTree (Fin 1) where
  graph := ⊥
  isTree := ⟨SimpleGraph.Connected.of_subsingleton, SimpleGraph.isAcyclic_bot⟩
  root := 0
  parent := fun _ => 0
  parent_root := rfl
  rank := fun _ => 0
  parent_rank := by intro v hv; exact (hv (Subsingleton.elim _ _)).elim
  adj_iff := by intro u v; simp [Subsingleton.elim u 0, Subsingleton.elim v 0]

/-- The path 0--1--2--3, rooted at 1, has two root branches. -/
def forkTree : RootedTree (Fin 4) where
  graph := pathFour.graph
  isTree := pathFour.isTree
  root := 1
  parent := ![1, 1, 1, 2]
  parent_root := rfl
  rank := ![0, 2, 1, 0]
  parent_rank := by decide +kernel
  adj_iff := by
    intro u v
    change (SimpleGraph.pathGraph 4).Adj u v ↔ _
    rw [SimpleGraph.pathGraph_adj]
    fin_cases u <;> fin_cases v <;> decide

def evaluationCases : List (String × Bool × Bool) :=
  [ ("zero routes, negative budget",
      checkCompact pathFour (fun _ => 0) (fun _ => 99) 0 (-1), true),
    ("zero routes with nonzero column",
      checkCompact pathFour ![0,1,0,0] (fun _ => 0) 0 0, false),
    ("depot only, no routes",
      checkCompact pointTree (fun _ => 99) (fun _ => 99) 0 (-1), true),
    ("depot only, positive routes",
      checkCompact pointTree (fun _ => 0) (fun _ => 99) 1 0, false),
    ("zero multiplicity subtree",
      checkCompact pathFour ![0,1,0,0] (fun _ => 1) 1 1, true),
    ("child count three, parent count one",
      checkCompact pathFour ![0,1,1,3] ![99,0,-1,2] 1 2, true),
    ("negative fee cancels excess leaf cost",
      checkCompact pathFour ![0,1,1,1] ![99,0,-3,10] 1 4, true),
    ("signed cost below threshold rejected",
      checkCompact pathFour ![0,1,1,1] ![99,0,-3,10] 1 3, false),
    ("fractional fees accepted exactly",
      checkCompact pathFour ![0,1,1,1] ![99,1/2,-3/2,7/2] 1 (3/2), true),
    ("fractional fees exceed budget",
      checkCompact pathFour ![0,1,1,1] ![99,1/2,-3/2,7/2] 1 1, false),
    ("disjoint root supports",
      checkCompact forkTree ![1,99,1,0] (fun _ => 0) 2 0, true),
    ("overlapping root supports rejected",
      checkCompact forkTree ![1,99,1,0] (fun _ => 0) 1 0, false),
    ("incomplete root coverage rejected",
      checkCompact forkTree ![1,99,1,0] (fun _ => 0) 3 0, false),
    ("root child count exceeds one",
      checkCompact forkTree ![2,0,0,0] (fun _ => 0) 1 0, false),
    ("root initial cost must not be pruned",
      checkCompact forkTree ![1,99,1,0] (fun _ => -1) 2 (-1), true),
    ("parent active with no active child",
      checkCompact pathFour ![0,1,1,0] (fun _ => 0) 1 0, true),
    ("compressed duplicate columns accepted",
      checkCompact pathFour ![0,2,3,0] (fun _ => 0) 2 0, true),
    ("four column compositions",
      (compositionsV 2 3).length == 4, true),
    ("four columns yield three compressed states",
      (computeCompact pathFour ![0,2,3,0] (fun _ => 0) 2 2).length == 3, true),
    ("zero dimensional composition",
      (compositionsV 0 0).length == 1, true),
    ("impossible zero dimensional composition",
      (compositionsV 0 1).isEmpty, true) ]

def runEvaluationCases : IO Unit := do
  for (label, actual, expected) in evaluationCases do
    if actual != expected then
      throw (IO.userError s!"FAIL {label}: expected {expected}, got {actual}")
  IO.println s!"PASS: {evaluationCases.length} executable compressed-DP regression cases"

#eval runEvaluationCases

end UAVProof.TreeBudgetSubtreeDPExamples
