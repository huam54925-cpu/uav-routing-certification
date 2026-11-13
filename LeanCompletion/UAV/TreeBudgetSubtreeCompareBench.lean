import LeanCompletion.UAV.TreeBudgetSubtreeCompareOrder
import LeanCompletion.UAV.TreeBudgetSubtreeStatsBench

/-! Six frozen inputs, original executors plus four explicit-comparator arms.
Diagnostics are separate from timing. Same calibrated batch size for all six
arms of each input, rotating order, seven paired rounds. -/
namespace UAVProof.TreeBudgetSubtreeCompareBench
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats TreeBudgetSubtreeCompare
open TreeBudgetSubtreeStatsBench

def selected : List Case := cases.filter fun c =>
  ["fees_4", "fees_8", "zero_4", "zero_8", "rational_short", "rational_long"].contains c.name

def labels : List String := ["C_original", "F_original", "C_K", "C_B", "F_K", "F_B"]

def countJson (d : CompareCounts) : Lean.Json := Lean.toJson
  [d.calls, d.keyVectorCalls, d.keyRejects, d.costVectorCalls, d.costRejects,
   d.equalStates, d.keyCoordinateChecks, d.ratCoordinateChecks]

def rowJson (detailAvailable : Bool) (r : StageRow) : Lean.Json := Lean.Json.mkObj
  [("node", Lean.toJson r.node), ("stage", Lean.toJson r.stage),
   ("position", Lean.toJson r.position), ("input", Lean.toJson r.input),
   ("output", Lean.toJson r.output), ("counts", countJson r.comparisons),
   ("detailAvailable", Lean.toJson detailAvailable)]

def runArm (arm : Nat) (c : Case) : Bool :=
  let R := tree c
  if arm = 0 then checkCompact R (val c.h) (val c.s) c.m c.budget
  else if arm = 1 then checkFull R (val c.h) (val c.s) c.m c.budget
  else if arm < 4 then checkCompactOrder (arm == 3) R (val c.h) (val c.s) c.m c.budget
  else checkFullOrder (arm == 5) R (val c.h) (val c.s) c.m c.budget

def diagnostics (c : Case) : IO Unit := do
  let R := tree c
  let a := checkCompactStats R (val c.h) (val c.s) c.m c.budget
  let b := checkFullStats R (val c.h) (val c.s) c.m c.budget
  emit [("kind", Lean.toJson "input"), ("case", Lean.toJson c.name),
    ("m", Lean.toJson c.m), ("root", Lean.toJson R.root.val),
    ("parent", Lean.toJson ((List.finRange 4).map fun i => (R.parent i).val)),
    ("H", Lean.toJson c.h.toList), ("s", Lean.toJson (c.s.toList.map toString)),
    ("T", Lean.toJson (toString c.budget)), ("answer", Lean.toJson a.value)]
  for native in [true, false] do
    for order in (if native then [false] else [false, true]) do
      let x := checkCompactDiagnostic native order R (val c.h) (val c.s) c.m c.budget
      let y := checkFullDiagnostic native order R (val c.h) (val c.s) c.m c.budget
      unless x.result.value == a.value && y.result.value == b.value &&
          x.result.stats == a.stats && y.result.stats == b.stats do
        throw (IO.userError s!"{c.name}: diagnostic collapse")
      for (rep, d) in [("compact", x), ("full", y)] do
        unless (d.rows.map fun r => r.comparisons.calls).sum == d.result.stats.eqCalls do
          throw (IO.userError s!"{c.name}: phase sum")
        if !native then
          for r in d.rows do
            if r.stage == "node" then
              let z := r.comparisons
              let conserved := if order then
                z.calls == z.costRejects + z.keyVectorCalls &&
                  z.keyVectorCalls == z.keyRejects + z.equalStates
                else z.calls == z.keyRejects + z.costVectorCalls &&
                  z.costVectorCalls == z.costRejects + z.equalStates
              unless conserved do throw (IO.userError s!"{c.name}: field conservation")
        emit [("kind", Lean.toJson "diagnostic"), ("case", Lean.toJson c.name),
          ("representation", Lean.toJson rep),
          ("strategy", Lean.toJson (if native then "native" else if order then "cost" else "key")),
          ("answer", Lean.toJson d.result.value), ("stats", statsJson d.result.stats),
          ("rows", Lean.toJson (d.rows.map fun r => rowJson (!native && r.stage == "node") r))]
  for v in List.finRange 4 do
    if v != R.root then
      let cs := computeCompact R (val c.h) (val c.s) c.m v
      let fs := computeFull R (val c.h) (val c.s) c.m v
      for order in [false, true] do
        unless computeCompactOrder order R (val c.h) (val c.s) c.m v == cs &&
            computeFullOrder order R (val c.h) (val c.s) c.m v == fs &&
            (computeCompactDiagnostic false order R (val c.h) (val c.s) c.m v).result.value == cs &&
            (computeFullDiagnostic false order R (val c.h) (val c.s) c.m v).result.value == fs do
          throw (IO.userError s!"{c.name}: ordered table mismatch")
  for arm in [:6] do
    unless runArm arm c == a.value do throw (IO.userError s!"{c.name}: arm answer")

@[noinline] def timedBatch (arm reps : Nat) (input : IO.Ref Case) : IO (Nat × Nat) := do
  let result ← IO.mkRef false
  let mut checksum := 0
  let start ← IO.monoNanosNow
  for _ in [:reps] do
    let c ← input.get
    result.set (runArm arm c)
    if ← result.get then checksum := checksum + 1
  return ((← IO.monoNanosNow) - start, checksum)

def counterRegression : IO Unit := do
  let q : ExecFullState 2 := ⟨#[1,2].toVector, #[3,4].toVector⟩
  let r : ExecFullState 2 := ⟨#[2,1].toVector, #[5,2].toVector⟩
  let f := fullEqDetailed false q r
  let c := compactEqDetailed false (projectFull q) (projectFull r)
  let b := fullEqDetailed true q r
  unless !f.value && f.counts.keyRejects == 1 && f.counts.ratCoordinateChecks == 0 &&
      !c.value && c.counts.keyCoordinateChecks == 2 && c.counts.ratCoordinateChecks == 1 &&
      !b.value && b.counts.keyCoordinateChecks == 0 && b.counts.ratCoordinateChecks == 1 do
    throw (IO.userError "projection/short-circuit regression")
  let same := compactEqDetailed false (projectFull q) (projectFull q)
  unless same.value && same.counts.equalStates == 1 &&
      same.counts.keyCoordinateChecks == 2 && same.counts.ratCoordinateChecks == 2 do
    throw (IO.userError "equal coordinate scan")
  let empty : ExecCompactState 0 := ⟨Vector.ofFn Fin.elim0, Vector.ofFn Fin.elim0⟩
  let z := compactEqDetailed false empty empty
  unless z.value && z.counts.ratCoordinateChecks == 0 && z.counts.keyCoordinateChecks == 0 do
    throw (IO.userError "empty scan")
  let d := dedupDetailed (fullEqDetailed false) [q,r,q]
  unless d.value == [r,q] && d.counts.calls == 3 do
    throw (IO.userError "rightmost dedup order/count")
  TreeBudgetSubtreeStats.countRegression
  IO.println "PASS: 4 comparison regressions, 14 previous counters and 21 original DP cases"

#eval counterRegression

def main (args : List String) : IO Unit := do
  let rounds := (args[0]?.getD "7").toNat?.getD 7
  let targetMs := (args[1]?.getD "100").toNat?.getD 100
  let startAt := (args[2]?.getD "0").toNat?.getD 0
  for (c, idx) in selected.zipIdx do
    if idx ≥ startAt then
      emit [("phase", Lean.toJson "case_start"), ("case", Lean.toJson c.name),
        ("index", Lean.toJson idx)]
      diagnostics c
      let input ← IO.mkRef c
      for arm in [:6] do discard (timedBatch arm 1 input)
      let mut reps := 1
      let mut ready := false
      while !ready do
        let mut shortest := 1000000000000
        for arm in [:6] do
          emit [("phase", Lean.toJson "calibration"), ("case", Lean.toJson c.name)]
          let (ns, _) ← timedBatch arm reps input
          shortest := min shortest ns
          emit [("kind", Lean.toJson "calibration"), ("case", Lean.toJson c.name),
            ("arm", Lean.toJson arm), ("reps", Lean.toJson reps), ("ns", Lean.toJson ns)]
        ready := shortest ≥ targetMs * 1000000 || reps ≥ 4096
        if !ready then reps := reps * 2
      emit [("kind", Lean.toJson "batch_size"), ("case", Lean.toJson c.name),
        ("reps", Lean.toJson reps), ("target_ms", Lean.toJson targetMs)]
      for round in [:rounds] do
        for offset in [:6] do
          let arm := (round + offset) % 6
          emit [("phase", Lean.toJson "timing"), ("case", Lean.toJson c.name)]
          let (ns, checksum) ← timedBatch arm reps input
          emit [("kind", Lean.toJson "timing"), ("case", Lean.toJson c.name),
            ("arm", Lean.toJson arm), ("label", Lean.toJson (labels[arm]?.getD "invalid")),
            ("round", Lean.toJson round), ("ns", Lean.toJson ns),
            ("reps", Lean.toJson reps), ("checksum", Lean.toJson checksum)]
      emit [("phase", Lean.toJson "case_done"), ("case", Lean.toJson c.name),
        ("index", Lean.toJson idx)]
  emit [("phase", Lean.toJson "complete")]

end UAVProof.TreeBudgetSubtreeCompareBench
