import LeanCompletion.UAV.TreeBudgetSubtreePreRanges
import LeanCompletion.UAV.TreeBudgetSubtreeAutoExamples
import LeanCompletion.UAV.TreeBudgetSubtreeResourceExamples

/-! Kernel boundaries, complete-certificate regressions and records for an
independent Python integer/Fraction replay. Records stay in ignored run logs. -/
namespace UAVProof.TreeBudgetSubtreePreExamples
open TreeFlowExistence TreeFlowExamples TreeBudgetSubtreeDPExamples
open TreeBudgetSubtreeExecutable TreeBudgetSubtreePre TreeBudgetSubtreeResourceSeed
open TreeBudgetSubtreeAutoExamples (observe)
open Lean (toJson Json)

example : (euclid 144 233).value = 1 ∧ euclidIterations 144 233 = 11 := by decide +kernel
example : (ratAddC (1/3) (-1/3)).value = 0 := by decide +kernel
example : (floorBudgetC 3 (-1/2)).value = -2 := by decide +kernel
example : (floorBudgetC 6 (-1/2)).value = -3 := by decide +kernel
example : (denLCMC []).value = 1 := by decide +kernel
example : (denLCMC [1/5, 2/5, -3/5]).value = 5 := by decide +kernel
example : (denLCMC [1/5, 1/7, 1/11]).value = 385 := by decide +kernel
example : findCounted (fun n : ℕ => decide (n = 0)) [0, 1, 2] = (some 0, 1) := by
  decide +kernel
example : findCounted (fun n : ℕ => decide (n = 2)) [0, 1, 2] = (some 2, 3) := by
  decide +kernel
example : findCounted (fun n : ℕ => decide (n = 4)) [0, 1, 2] = (none, 3) := by
  decide +kernel
example : (execute pointTree
    (materialize pointTree (fun _ => 0) (fun _ => 0) 0 (-1))).value.value.isSome := by
  decide +kernel
example : (execute pointTree
    (materialize pointTree (fun _ => 0) (fun _ => 0) (2^200) 0)).value.keyStats = {} := by
  decide +kernel
example : (execute pointTree
    (materialize pointTree (fun _ => 0) (fun _ => 0) (2^200) 0)).ops = 13 := by
  decide +kernel

def emit {N : ℕ} (R : RootedTree (Fin N)) (I : Input N) : IO Unit := do
  let p := prepareC I
  let g := rootMassC I
  let r := execute R I
  IO.println ("HCASE " ++ (Json.mkObj [
    ("root", toJson I.root.val), ("parent", toJson (I.parent.toList.map Fin.val)),
    ("mass", toJson I.mass.toList),
    ("service", toJson (I.service.toList.map fun q => [q.num, (q.den : ℤ)])),
    ("routes", toJson I.routes), ("budget", toJson [I.budget.num, (I.budget.den : ℤ)]),
    ("scale", toJson p.value.scale), ("weight", toJson p.value.weight.toList),
    ("floor", toJson p.value.budget), ("rootRun", toJson [g.value, g.ops, g.width]),
    ("prepRun", toJson [p.ops, p.width]), ("entryRun", toJson [r.ops, r.width]),
    ("certificate", toJson (r.value.value.map observe))]).compress)

def checkCase {N : ℕ} (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) : IO Unit := do
  let I := materialize R H s m T
  let p := prepareC I
  let expected := TreeBudgetSubtreeAutoScaleSeed.prepare R s T
  unless p.value.scale == expected.scale && p.value.weight == expected.weight &&
      p.value.budget == expected.budget do throw (IO.userError "Prepared field mismatch")
  let r := execute R I
  let old := solveGuardedR R H s m T
  unless r.value.value.map observe == old.value.map observe &&
      decide (r.value.keyStats = old.keyStats) && decide (r.value.payload = old.payload) do
    throw (IO.userError "complete certificate / 17 fields / 9 payload fields mismatch")
  unless r.value.value.map observe == (TreeBudgetSubtreeWitness.solve R H s m T).map observe do
    throw (IO.userError "rational witness mismatch")
  let b := ((I.service.toList ++ [T]).flatMap fun q => [q.num.natAbs.size, q.den.size]).foldl max 1
  let h := (I.mass.toList.map Nat.size).foldl max 0
  unless bitWork r ≤ prePolynomial N b h m.size do throw (IO.userError "preprocessing bound")
  unless p.ops == 2*((List.finRange N).map (coefficientOps I)).sum +
      denOps ((List.finRange N).map fun v => (coefficientC I v).value) + 8*N+16 do
    throw (IO.userError "single-run operation recurrence")
  emit R I

def runCases : IO Unit := do
  let mut count := 0
  for m in [0:4] do
    for H in [![0,0,0,0], ![0,0,1,0], ![0,1,1,3], ![0,2,3,0], ![0,1,1,1], ![0,2,0,2]] do
      for T in [(-3/2 : ℚ), -1, 0, 3/2, 4] do
        for s in [![99,0,0,0], ![99,0,-3,10], ![99,1/2,-3/2,7/2], ![-99,1/3,-5/6,7/10]] do
          checkCase pathFour H s m T
          count := count + 1
        checkCase forkTree H (fun _ => 0) m T
        count := count + 1
  checkCase pointTree (fun _ => 99) (fun _ => 99) 0 (-1/2)
  checkCase pointTree (fun _ => 99) (fun _ => 99) 1 (-1/2)
  checkCase pathFour ![0,1,1,100] (fun _ => 0) 1 0
  checkCase pathFour ![0,1,1,1] ![0,1/5,1/7,1/11] 1 (-1/13)
  checkCase pathFour ![0,1,1,1] ![0,1/3,-1/3,1/3] 1 (-1/3)
  checkCase pathFour ![0,1,1,1] ![0,1/(2^200+1),-1/(2^200+1),1/233] 1 (1/144)
  checkCase pathFour ![0,2,2,1] ![0,-3,1,3] 2 (-3)
  let last := execute pathFour (materialize pathFour ![0,2,2,1] ![0,-3,1,3] 2 (-3))
  unless last.value.value.isSome && last.value.keyStats.acceptCalls == 3 do
    throw (IO.userError "expected acceptance at the last of three root states")
  let huge := materialize pointTree (fun _ => 2^300) (fun _ => 1/(2^400+1)) (2^200) (-1/3)
  let out := execute pointTree huge
  unless out.value.value.isNone && out.ops == 13 && out.width == 201 &&
      decide (out.value.keyStats = {}) && decide (out.value.payload = {}) do
    throw (IO.userError "huge route guard did not reject cheaply")
  emit pointTree huge
  IO.println s!"PASS H: {count+8} complete records; preprocessing, full certificates, \
    all statistics, huge rejection"

#eval runCases
end UAVProof.TreeBudgetSubtreePreExamples
