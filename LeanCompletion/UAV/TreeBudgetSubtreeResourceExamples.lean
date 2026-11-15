import LeanCompletion.UAV.TreeBudgetSubtreeResourceBounds
import LeanCompletion.UAV.TreeBudgetSubtreeResourceRealizes
import LeanCompletion.UAV.TreeBudgetSubtreeAutoExamples

/-! Executed regressions: full certificate observations, all statistics, raw
payload charges, and pre-rejection intermediate values. No native_decide axioms. -/
namespace UAVProof.TreeBudgetSubtreeResourceExamples
open TreeFlowExistence TreeFlowExamples TreeBudgetSubtreeState
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeDPExamples
open TreeBudgetSubtreeResourceSeed TreeBudgetSubtreeIntegerWitnessSeed
open TreeBudgetSubtreeAutoExamples (observe)

example : (findCounted (fun n : ℕ => decide (n = 0)) [0, 1, 2]) = (some 0, 1) := by
  decide +kernel
example : (findCounted (fun n : ℕ => decide (n = 2)) [0, 1, 2]) = (some 2, 3) := by
  decide +kernel
example : (findCounted (fun n : ℕ => decide (n = 4)) [0, 1, 2]) = (none, 3) := by
  decide +kernel
example : (dedupKeyCounted Prod.fst [(0, 3), (1, 5), (0, 7)]).value =
    [(1, 5), (0, 7)] := by decide +kernel
example : (solveGuardedR pointTree (fun _ => 99) (fun _ => 99) 0 (-1/2)).value.isSome := by
  decide +kernel
example : (solveGuardedR pointTree (fun _ => 99) (fun _ => 99) 1 (-1/2)).keyStats = {} := by
  decide +kernel
example : (rootsR [[(⟨⟨#v[true], #v[-3]⟩, #v[#v[0]]⟩ : Entry 1 1)],
    [⟨⟨#v[true], #v[4]⟩, #v[#v[0]]⟩]]).keyStats.rootRejected = 1 := by decide +kernel
example : (rootsR [[(⟨⟨#v[true], #v[-3]⟩, #v[#v[0]]⟩ : Entry 1 1)],
    [⟨⟨#v[true], #v[4]⟩, #v[#v[0]]⟩]]).payload.pickCons = 2 := by decide +kernel
example : (insideR #v[true] #v[0]
    [[], [(⟨⟨#v[true], #v[1]⟩, #v[#v[0]]⟩ : Entry 1 1)]]).payload.pickCons = 1 := by
  decide +kernel

def checkCost {m : ℕ} (W : ℕ) (cost : Vector ℤ m) : IO Unit := do
  for i in List.finRange m do
    unless (val cost i).natAbs ≤ W do throw (IO.userError "raw signed cost exceeds W")

def checkPicks {N m : ℕ} (H : Fin N → ℕ) (es : List (Entry N m)) : IO Unit := do
  for k in [0:es.length + 1] do
    for i in List.finRange m do
      for x in List.finRange N do
        let a := ((es.take k).map fun e => TreeBudgetSubtreeWitness.matrixVal e.matrix i x).sum
        unless a ≤ H x do throw (IO.userError "temporary coordinate exceeds H")

def checkCase {N : ℕ} (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) : IO Unit := do
  let p := TreeBudgetSubtreeAutoScaleSeed.prepare R s T
  let w := val p.weight
  let r := solveAutoR R H s m T
  unless r.value.map observe == (TreeBudgetSubtreeWitness.solve R H s m T).map observe do
    throw (IO.userError "resource executor changed full certificate")
  unless decide (r.keyStats = (TreeBudgetSubtreeInteger.checkMeasured R H w m p.budget).stats) &&
      decide (r.keyStats = (TreeBudgetSubtreeStats.checkCompactStats R H s m T).stats) do
    throw (IO.userError "17-field statistics mismatch")
  unless (solveGuardedR R H s m T).value.map observe == r.value.map observe do
    throw (IO.userError "guard changed full certificate")
  let vs := (List.finRange N).filter fun v => v != R.root
  let A := (vs.map (rawCount R H w m)).sum
  let D := (vs.map fun v => (childrenList R v).length * rawCount R H w m v).sum
  let C := optionCount r.value
  let d := m * (N - 1) * (D + C * (childrenList R R.root).length)
  let expected : PayloadStats :=
    { matrices := A + C, matrixCells := m * N * (A + C), columnReads := m * (A + C),
      childReads := d, natAdds := d, tempCells := d,
      pickCons := r.keyStats.insidePairs + r.keyStats.rootPairs,
      keyMapCells := r.payload.keyMapCells, rootZeroCells := m * C }
  unless decide (r.payload = expected) do throw (IO.userError "payload census mismatch")
  let P := (vs.map fun v => columnFactor m (H v)).prod
  let U := (vs.map H).foldl max 0
  unless resourceWork r ≤ 64 * (N + 1)^2 * (m + 1) * (U + 1) * P ^ 2 &&
      r.payload.keyMapCells ≤ (N - 1) * P * (P - 1) do
    throw (IO.userError "global resource bound mismatch")
  let W := (vs.map fun v => (w v).natAbs * H v).sum
  let b := ((vs.flatMap fun v => [(s v).num.natAbs.size, (s v).den.size]) ++
    [T.num.natAbs.size, T.den.size]).foldl max 1
  let K := ((N - 1) + 1) * b + 1
  unless p.scale == TreeBudgetSubtreeResource.serviceDenLCM R s &&
      p.scale ≤ 2 ^ ((N - 1) * b) && p.budget.natAbs < 2 ^ (((N - 1) + 1) * b) &&
      W < 2 ^ (K + (N - 1).size + U.size) do
    throw (IO.userError "denominator or numeric width bound mismatch")
  for v in List.finRange N do
    unless (w v).natAbs < 2 ^ K do throw (IO.userError "weight magnitude bound mismatch")
  for v in vs do
    let ts := (childrenList R v).map (compute R H w m)
    let raw := nodeRawEntries R H w m v ts
    unless raw.length ≤ P do throw (IO.userError "raw node length exceeds P")
    for e in raw do
      checkCost W e.key.cost
      for i in List.finRange m do
        for x in List.finRange N do
          unless TreeBudgetSubtreeWitness.matrixVal e.matrix i x ≤ H x do
            throw (IO.userError "raw matrix coordinate exceeds H")
    for q in localCandidates R H m v do
      let base := Vector.ofFn fun i => w v * ((val q i : ℕ) : ℤ)
      checkCost W base
      for tail in ts.tails do
        for b in inside (support q) base tail do
          checkCost W b.cost
          checkPicks H b.picks
        match tail with
        | [] => pure ()
        | t :: rest =>
          for b in insideRawEntries (support q) base t rest do
            checkCost W b.cost
            checkPicks H b.picks
  let ts := (childrenList R R.root).map (compute R H w m)
  for tail in ts.tails do
    match tail with
    | [] => pure ()
    | t :: rest =>
      for b in rootsRawEntries t rest do
        checkCost W b.key.cost
        checkPicks H b.picks

def runCases : IO Unit := do
  let mut count := 0
  for m in [0:4] do
    for H in [![0,0,0,0], ![0,0,1,0], ![0,1,1,3], ![0,2,3,0], ![0,1,1,1], ![0,2,0,2]] do
      for T in [(-3/2 : ℚ), -1, 0, 3/2, 4] do
        checkCase pathFour H (fun _ => 0) m T
        checkCase pathFour H ![99,0,-3,10] m T
        checkCase pathFour H ![99,1/2,-3/2,7/2] m T
        checkCase pathFour H ![-99,1/3,-5/6,7/10] m T
        checkCase forkTree H (fun _ => 0) m T
        count := count + 5
  checkCase pointTree (fun _ => 99) (fun _ => 99) 0 (-1/2)
  checkCase pointTree (fun _ => 99) (fun _ => 99) 1 (-1/2)
  checkCase pathFour ![0,1,1,100] (fun _ => 0) 1 0
  let huge := solveGuardedR pointTree (fun _ => 99) (fun _ => 99) (2 ^ 200) (-1/2)
  unless huge.value.isNone && decide (huge.keyStats = {}) && decide (huge.payload = {}) do
    throw (IO.userError "huge-m guard failed to exit before allocation")
  let gap := dedupKeyCounted id ((List.replicate 100 0) ++ List.range 20)
  unless gap.comparisons == 290 && gap.keyMapCells == 2190 do
    throw (IO.userError "key-map/scan distinction lost")
  IO.println s!"PASS: {count + 3} complete certificate/statistics/raw-resource cases; huge guard and key-map gap"

#eval runCases
end UAVProof.TreeBudgetSubtreeResourceExamples
