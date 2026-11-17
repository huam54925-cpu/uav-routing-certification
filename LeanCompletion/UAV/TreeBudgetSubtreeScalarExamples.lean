import LeanCompletion.UAV.TreeBudgetSubtreeScalarEntry
import LeanCompletion.UAV.TreeBudgetSubtreeAutoExamples

namespace UAVProof.TreeBudgetSubtreeScalarExamples
open TreeFlowExistence TreeFlowExamples TreeBudgetSubtreeDPExamples
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeScalar TreeBudgetSubtreeResourceSeed
open TreeBudgetSubtreeIntegerWitnessSeed TreeBudgetSubtreeStats
open TreeBudgetSubtreePre (materialize guardC prepareC bitWork)
open TreeBudgetSubtreeAutoExamples (observe)
open Lean (toJson Json)

example : (vectorEqC (#v[1,2,3] : Vector Int 3) #v[1,2,3]).ops = 26 := by decide +kernel
example : (vectorEqC (#v[1,2,3] : Vector Int 3) #v[0,2,3]).ops = 13 := by decide +kernel
example : (vectorEqC (#v[1,2,3] : Vector Int 3) #v[1,2,0]).ops = 25 := by decide +kernel
example : (vectorEqC (#v[] : Vector Int 0) #v[]).ops = 2 := by decide +kernel
example : (dedupC Prod.fst (fun a b : Nat => ⟨decide (a=b), 1⟩)
    [(0,3), (1,5), (0,7)]).value.value = [(1,5), (0,7)] := by decide +kernel
example : (childrenC pathFour 2).ops = 50 := by decide +kernel
example : (rootsC [[(⟨⟨#v[true], #v[-3]⟩, #v[#v[0]]⟩ : Entry 1 1)],
    [⟨⟨#v[true], #v[4]⟩, #v[#v[0]]⟩]]).value.keyStats.rootRejected = 1 := by decide +kernel
example : (insideC #v[true] #v[0]
    [[], [(⟨⟨#v[true], #v[1]⟩, #v[#v[0]]⟩ : Entry 1 1)]]).value.payload.pickCons = 1 := by
  decide +kernel
example : (executeC pointTree (materialize pointTree (fun _ => 0) (fun _ => 0) 0 (-1))).value.value.isSome := by
  decide +kernel
example : (executeC pointTree (materialize pointTree (fun _ => 2^300)
    (fun _ => 1/(2^400+1)) (2^200) (-1/3))).ops = 13 := by decide +kernel
example : (executeC pointTree (materialize pointTree (fun _ => 2^300)
    (fun _ => 1/(2^400+1)) (2^200) (-1/3))).width = 201 := by decide +kernel

def statsList (s : DPStats) : List Nat :=
  [s.nodeCalls,s.compositionCalls,s.rangeChoices,s.columnsGenerated,s.columnsAccepted,
   s.subsetCalls,s.insidePairs,s.rootPairs,s.rootRejected,s.ratAdds,s.ratMuls,
   s.dedupInput,s.dedupOutput,s.eqCalls,s.acceptCalls,s.maxRawTable,s.maxDedupTable]

def payloadList (p : PayloadStats) : List Nat :=
  [p.matrices,p.matrixCells,p.childReads,p.natAdds,p.tempCells,p.columnReads,
   p.pickCons,p.keyMapCells,p.rootZeroCells]

def checkCase {N : Nat} (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (s : Fin N → Rat) (m : Nat) (T : Rat) : IO Unit := do
  let I := materialize R H s m T
  let g := guardC I
  let r := executeC R I
  let old := solveGuardedR R H s m T
  unless r.value.value.map observe == old.value.map observe &&
      decide (r.value.keyStats = old.keyStats) && decide (r.value.payload = old.payload) do
    throw (IO.userError "I full certificate or 17+9 fields changed")
  let mut dpOps := 0
  if g.value then
    let p := prepareC I
    dpOps := r.ops - (g.ops+p.ops+8)
    unless dpOps ≤ 2*dpFactor N m*(1+resourceWork old) do
      throw (IO.userError "I actual recurrence exceeded resource bridge")
    let nonroot := (List.finRange N).filter (fun v => v != R.root)
    let upper := dpUpper N m (nonroot.map H).sum (nonroot.map (fun v => columnFactor m (H v))).prod
    let width := max (TreeBudgetSubtreePre.inputWidth N (TreeBudgetSubtreePre.serviceBits I)
      (TreeBudgetSubtreePre.massBits I) I.routes.size)
      (dpWidth N m (TreeBudgetSubtreePre.serviceBits I) (TreeBudgetSubtreePre.massBits I) upper)
    unless bitWork r ≤ 32*(width+1)^2*
        (128*(N+1)*(TreeBudgetSubtreePre.serviceBits I+1)+upper+6) do
      throw (IO.userError "I common-width bit bound")
    unless r.value.value.map observe == (TreeBudgetSubtreeWitness.solve R H s m T).map observe do
      throw (IO.userError "I full rational witness changed")
  else
    unless r.ops == g.ops+1 && r.width == g.width do
      throw (IO.userError "I rejection performed DP work")
  IO.println ("ICASE " ++ (Json.mkObj [
    ("root", toJson I.root.val), ("parent", toJson (I.parent.toList.map Fin.val)),
    ("mass", toJson I.mass.toList),
    ("service", toJson (I.service.toList.map fun q => [q.num, (q.den : Int)])),
    ("routes", toJson I.routes), ("budget", toJson [I.budget.num, (I.budget.den : Int)]),
    ("entryRun", toJson [r.ops,r.width]), ("dpOps", toJson dpOps),
    ("keyStats", toJson (statsList r.value.keyStats)),
    ("payload", toJson (payloadList r.value.payload)),
    ("certificate", toJson (r.value.value.map observe))]).compress)

def runCases : IO Unit := do
  let mut count := 0
  for m in [0:4] do
    for H in [![0,0,0,0], ![0,0,1,0], ![0,1,1,3], ![0,2,3,0], ![0,1,1,1], ![0,2,0,2]] do
      for T in [(-3/2 : Rat), -1, 0, 3/2, 4] do
        for s in [![99,0,0,0], ![99,0,-3,10], ![99,1/2,-3/2,7/2], ![-99,1/3,-5/6,7/10]] do
          checkCase pathFour H s m T
          count := count+1
        checkCase forkTree H (fun _ => 0) m T
        count := count+1
  checkCase pointTree (fun _ => 99) (fun _ => 99) 0 (-1/2)
  checkCase pointTree (fun _ => 99) (fun _ => 99) 1 (-1/2)
  checkCase pathFour ![0,1,1,100] (fun _ => 0) 1 0
  checkCase pathFour ![0,1,1,1] ![0,1/5,1/7,1/11] 1 (-1/13)
  checkCase pathFour ![0,1,1,1] ![0,1/3,-1/3,1/3] 1 (-1/3)
  checkCase pathFour ![0,1,1,1] ![0,1/(2^200+1),-1/(2^200+1),1/233] 1 (1/144)
  checkCase pathFour ![0,2,2,1] ![0,-3,1,3] 2 (-3)
  checkCase pointTree (fun _ => 2^300) (fun _ => 1/(2^400+1)) (2^200) (-1/3)
  for n in [0:49] do
    let a := Vector.ofFn (fun i : Fin n => (i.val : Int))
    for k in [0:n+1] do
      let b := Vector.ofFn (fun i : Fin n => (i.val : Int) + if i.val = k then 1 else 0)
      let c := vectorEqC a b
      let checks := if k=n then n else k+1
      unless c.value == decide (a=b) && c.ops == 2*n+1+6*checks+(if k=n then 1 else 0) do
        throw (IO.userError "I coordinate prefix recurrence")
  IO.println s!"PASS I Lean: {count+8} complete records; 1225 coordinate-prefix cases; 17+9 fields"

#eval runCases
end UAVProof.TreeBudgetSubtreeScalarExamples
