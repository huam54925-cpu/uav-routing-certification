import LeanCompletion.UAV.TreeBudgetSubtreeIntegerStats
import LeanCompletion.UAV.TreeBudgetSubtreeStatsBench

/-! Six frozen inputs, three separate executor timings. Scaling is checked
before timing. The prepared arm excludes scale construction; the end-to-end
arm includes it. No instrumentation or certificate payloads in timed runs. -/
namespace UAVProof.TreeBudgetSubtreeIntegerBench
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeState TreeBudgetSubtreeStats
open TreeBudgetSubtreeStatsBench

structure Prepared where
  input : Case
  scale : ℕ
  weight : Vector ℤ 4
  budget : ℤ

def prepare (c : Case) : Prepared :=
  let weights := Vector.ofFn fun v => linearWeight (tree c) (val c.s) v
  let D := weights.toList.foldl (fun d a => Nat.lcm d a.den) 1
  ⟨c, D, weights.map (fun a => (D : ℤ) * a.num / (a.den : ℤ)),
    TreeBudgetSubtreeInteger.floorBudget D c.budget⟩

def selected : List Case := cases.filter fun c =>
  ["fees_4", "fees_8", "zero_4", "zero_8", "rational_short", "rational_long"].contains c.name

def runArm (arm : ℕ) (p : Prepared) : Bool :=
  if arm = 0 then
    checkCompact (tree p.input) (val p.input.h) (val p.input.s) p.input.m p.input.budget
  else
    let q := if arm = 1 then p else prepare p.input
    TreeBudgetSubtreeInteger.check (tree q.input) (val q.input.h)
      (val q.weight) q.input.m q.budget

def validate (p : Prepared) : IO Unit := do
  let c := p.input
  let R := tree c
  unless p.scale > 0 do throw (IO.userError "nonpositive scale")
  for v in List.finRange 4 do
    if v != R.root then
      unless ((val p.weight v : ℤ) : ℚ) == (p.scale : ℚ) * linearWeight R (val c.s) v do
        throw (IO.userError "scaling contract")
      unless (TreeBudgetSubtreeInteger.compute R (val c.h) (val p.weight) c.m v).map
          (TreeBudgetSubtreeInteger.liftState p.scale) ==
          computeCompact R (val c.h) (val c.s) c.m v do
        throw (IO.userError "ordered table mismatch")
  let a := checkCompactStats R (val c.h) (val c.s) c.m c.budget
  let b := TreeBudgetSubtreeInteger.checkMeasured R (val c.h) (val p.weight) c.m p.budget
  unless a.value == b.value && a.stats == b.stats do
    throw (IO.userError "answer/statistics mismatch")
  for arm in [:3] do
    unless runArm arm p == a.value do throw (IO.userError "arm answer mismatch")
  emit [("kind", Lean.toJson "validation"), ("case", Lean.toJson c.name),
    ("scale", Lean.toJson p.scale), ("answer", Lean.toJson a.value),
    ("stats", statsJson a.stats)]

@[noinline] def timedBatch (arm reps : ℕ) (input : IO.Ref Prepared) : IO (ℕ × ℕ) := do
  let output ← IO.mkRef false
  let mut checksum := 0
  let start ← IO.monoNanosNow
  for _ in [:reps] do
    let p ← input.get
    output.set (runArm arm p)
    if ← output.get then checksum := checksum + 1
  return ((← IO.monoNanosNow) - start, checksum)

def main (args : List String) : IO Unit := do
  let rounds := (args[0]?.getD "7").toNat?.getD 7
  let targetMs := (args[1]?.getD "20").toNat?.getD 20
  for c in selected do
    let p := prepare c
    validate p
    let input ← IO.mkRef p
    for arm in [:3] do discard (timedBatch arm 1 input)
    let mut reps := 1
    let mut ready := false
    while !ready do
      let mut shortest := 1000000000000
      for arm in [:3] do
        let (ns, _) ← timedBatch arm reps input
        shortest := min shortest ns
      ready := shortest ≥ targetMs * 1000000 || reps ≥ 4096
      if !ready then reps := reps * 2
    for round in [:rounds] do
      for offset in [:3] do
        let arm := (round + offset) % 3
        let (ns, checksum) ← timedBatch arm reps input
        unless checksum == (if runArm arm p then reps else 0) do
          throw (IO.userError "timing checksum")
        emit [("kind", Lean.toJson "timing"), ("case", Lean.toJson c.name),
          ("arm", Lean.toJson arm), ("round", Lean.toJson round),
          ("reps", Lean.toJson reps), ("ns", Lean.toJson ns),
          ("checksum", Lean.toJson checksum)]
  emit [("phase", Lean.toJson "complete")]

end UAVProof.TreeBudgetSubtreeIntegerBench
