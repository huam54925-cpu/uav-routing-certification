import LeanCompletion.UAV.TreeBudgetSubtreeIntegerWitnessSeed
import LeanCompletion.UAV.TreeBudgetSubtreeDPExamples

/-! Boundary regressions compare every certificate coordinate and multiplicity,
not just feasibility. The finite checks supplement the general refinement proof. -/
namespace UAVProof.TreeBudgetSubtreeAutoExamples
open TreeFlowExistence TreeFlowExamples TreeBudgetSubtreeState
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeDPExamples
open TreeBudgetSubtreeIntegerWitnessSeed

/-- A finite, ordered observation of the entire function-valued certificate. -/
def observe {N : ℕ} (c : TreeBudgetCertificate.Certificate (Fin N)) :
    ℕ × List (List ℕ × ℕ) :=
  (c.size, (List.finRange c.size).map fun i =>
    ((List.finRange N).map (c.row i), c.count i))

example : TreeBudgetSubtreeAutoScaleSeed.denLCM [] = 1 := by decide +kernel
example : TreeBudgetSubtreeAutoScaleSeed.denLCM [2/3, -5/6] = 6 := by decide +kernel
example : TreeBudgetSubtreeAutoScaleSeed.scaleNum 6 (-5/6) = -5 := by decide +kernel
example : TreeBudgetSubtreeInteger.floorBudget 3 (-1/2) = -2 := by decide +kernel

example : (solveAuto pointTree (fun _ => 99) (fun _ => 99) 0 (-1/2)).isSome = true := by
  decide +kernel
example : (solveAuto pointTree (fun _ => 0) (fun _ => 99) 1 0).isSome = false := by
  decide +kernel

/-- Equal keys with distinct payloads retain the rightmost matrix. -/
example :
    (TreeBudgetSubtreeWitness.dedupKey (Entry.key (N := 1) (m := 1))
      [⟨⟨#v[true], #v[0]⟩, #v[#v[3]]⟩, ⟨⟨#v[true], #v[0]⟩, #v[#v[7]]⟩]).map
        Entry.matrix = [#v[#v[7]]] := by decide +kernel

def checkCase {N : ℕ} (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) : IO Unit := do
  let p := TreeBudgetSubtreeAutoScaleSeed.prepare R s T
  let actual := solveAuto R H s m T
  let expected := TreeBudgetSubtreeWitness.solve R H s m T
  unless actual.map observe == expected.map observe do
    throw (IO.userError "complete ordered certificate mismatch")
  unless actual.isSome == TreeBudgetSubtreeAutoScaleSeed.checkAuto R H s m T do
    throw (IO.userError "automatic decision mismatch")
  match actual with
  | none => pure ()
  | some c =>
    unless c.size == m && TreeBudgetCertificate.checkCertificate R H m s T c do
      throw (IO.userError "original certificate checker rejected automatic witness")
  let doubled := solve R H (fun v => 2 * val p.weight v) m
    (TreeBudgetSubtreeInteger.floorBudget (2 * p.scale) T)
  unless doubled.map observe == actual.map observe do
    throw (IO.userError "certificate changed under another valid scale")
  let zroots := roots ((childrenList R R.root).map (compute R H (val p.weight) m))
  let qroots := TreeBudgetSubtreeWitness.roots
    ((childrenList R R.root).map (TreeBudgetSubtreeWitness.compute R H s m))
  let zview := (zroots.map (liftRoot p.scale)).map fun r =>
    (r.key, r.picks.map fun e => (e.key, e.matrix))
  let qview := qroots.map fun r => (r.key, r.picks.map fun e => (e.key, e.matrix))
  unless zview == qview do
    throw (IO.userError "ordered root table including selected payloads mismatch")
  for v in (childrenList R R.root) do
    let zs := compute R H (val p.weight) m v
    let qs := TreeBudgetSubtreeWitness.compute R H s m v
    let left := (zs.map (liftEntry p.scale)).map fun e => (e.key, e.matrix)
    let right := qs.map fun e => (e.key, e.matrix)
    unless left == right do
      throw (IO.userError "ordered node table including matrix payload mismatch")

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
  IO.println s!"PASS: {count + 3} automatic full-certificate/table/scale regressions"

#eval runCases
end UAVProof.TreeBudgetSubtreeAutoExamples
