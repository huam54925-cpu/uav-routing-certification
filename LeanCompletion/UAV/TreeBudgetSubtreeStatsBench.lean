import LeanCompletion.UAV.TreeBudgetSubtreeStatsExamples

/-! Deterministic, small, matched experiments. Build this module once; a tiny
--run driver imports its compiled code. Timing excludes instrumentation and
input/output serialization, but includes the result IO.Ref write. -/
namespace UAVProof.TreeBudgetSubtreeStatsBench
open TreeFlowExistence TreeFlowExamples TreeBudgetSubtreeExecutable
open TreeBudgetSubtreeDPExamples TreeBudgetSubtreeStats

structure Case where
  name : String
  fork : Bool := false
  m : Nat
  h : Vector Nat 4
  s : Vector Rat 4
  budget : Rat

def pathCase (name : String) (m a b : Nat) (s : Vector Rat 4) (budget : Rat) : Case :=
  ⟨name, false, m, #[0,m,a,b].toVector, s, budget⟩

def cases : List Case :=
  (([2,4,8,16,32] : List Nat).map fun h =>
    pathCase s!"zero_{h}" 2 h h #[0,0,0,0].toVector 0) ++
  (([2,4,6,8] : List Nat).map fun h =>
    pathCase s!"fees_{h}" 2 h h #[0,1,2,3].toVector (8*h+2)) ++
  (([8,64,256,1024] : List Nat).map fun h =>
    pathCase s!"single_{h}" 1 h h #[0,0,0,0].toVector 0) ++
  [pathCase "three_routes_3" 3 3 3 #[0,0,0,0].toVector 0,
   pathCase "three_routes_6" 3 6 6 #[0,0,0,0].toVector 0,
   pathCase "signed_yes" 1 1 1 #[99,0,-3,10].toVector 4,
   pathCase "signed_no" 1 1 1 #[99,0,-3,10].toVector 3,
   pathCase "rational_short" 2 4 4 #[0,1/2,-3/2,7/2].toVector 10,
   pathCase "rational_long" 2 4 4
     #[0,1/(2^80+7),-(3/(2^80+7)),7/(2^80+7)].toVector (20/(2^80+7)),
   pathCase "rational_long_shift" 2 4 4
     #[0,(2^100+1)/3,-((2^100+3)/7),(2^100+7)/11].toVector (2^104),
   ⟨"root_disjoint", true, 2, #[1,99,1,3].toVector, #[0,0,0,0].toVector, 0⟩,
   ⟨"root_conflict", true, 1, #[1,99,1,3].toVector, #[0,0,0,0].toVector, 0⟩,
   ⟨"root_missing", true, 3, #[1,99,1,3].toVector, #[0,0,0,0].toVector, 0⟩,
   ⟨"root_cap", true, 1, #[2,0,0,0].toVector, #[0,0,0,0].toVector, 0⟩,
   ⟨"root_negative", true, 2, #[1,99,1,0].toVector, #[-1,-1,-1,-1].toVector, -1⟩,
   pathCase "zero_routes" 0 0 0 #[0,0,0,0].toVector (-1),
   pathCase "zero_routes_nonzero_column" 0 1 0 #[0,0,0,0].toVector 0]

def tree (c : Case) : RootedTree (Fin 4) := if c.fork then forkTree else pathFour

def emit (fields : List (String × Lean.Json)) : IO Unit := do
  IO.println (Lean.Json.mkObj fields).compress
  (← IO.getStdout).flush

def statsJson (s : DPStats) : Lean.Json := Lean.toJson
  [s.nodeCalls, s.compositionCalls, s.rangeChoices, s.columnsGenerated, s.columnsAccepted,
   s.subsetCalls, s.insidePairs, s.rootPairs, s.rootRejected, s.ratAdds, s.ratMuls,
   s.dedupInput, s.dedupOutput, s.eqCalls, s.acceptCalls, s.maxRawTable, s.maxDedupTable]

def runMode (mode : Nat) (c : Case) : Bool :=
  if mode = 0 then checkCompact (tree c) (val c.h) (val c.s) c.m c.budget
  else if mode = 1 then checkFull (tree c) (val c.h) (val c.s) c.m c.budget
  else checkFast (tree c) (val c.h) (val c.s) c.m c.budget

/-- Reading the case from IO and writing each result before the stop timestamp
prevents a pure result from being floated outside the measured interval. -/
@[noinline] def timedBatch (mode reps : Nat) (input : IO.Ref Case) : IO (Nat × Nat) := do
  let output ← IO.mkRef false
  let mut checksum := 0
  let t ← IO.monoNanosNow
  for _ in [:reps] do
    let c ← input.get
    output.set (runMode mode c)
    if ← output.get then checksum := checksum + 1
  let stop ← IO.monoNanosNow
  return (stop - t, checksum)

def validateCase (c : Case) : IO Unit := do
  let R := tree c
  let a := checkCompactStats R (val c.h) (val c.s) c.m c.budget
  let b := checkFullStats R (val c.h) (val c.s) c.m c.budget
  let f := checkFastStats R (val c.h) (val c.s) c.m c.budget
  unless a.value == b.value && a.value == f.value && a.value == runMode 0 c &&
      b.value == runMode 1 c && f.value == runMode 2 c do
    throw (IO.userError s!"{c.name}: checker mismatch")
  let strip := fun s : DPStats => { s with compositionCalls := 0, rangeChoices := 0 }
  unless strip a.stats == strip f.stats do
    throw (IO.userError s!"{c.name}: optimization changed non-enumeration counts")
  emit [("phase", Lean.toJson "counts"), ("case", Lean.toJson c.name),
    ("m", Lean.toJson c.m), ("root", Lean.toJson R.root.val),
    ("parent", Lean.toJson ((List.finRange 4).map fun i => (R.parent i).val)),
    ("H", Lean.toJson c.h.toList), ("s", Lean.toJson (c.s.toList.map toString)),
    ("T", Lean.toJson (toString c.budget)), ("answer", Lean.toJson a.value),
    ("compact", statsJson a.stats), ("full", statsJson b.stats), ("fast", statsJson f.stats)]
  for v in List.finRange 4 do
    if v != R.root then
      let cs := computeCompact R (val c.h) (val c.s) c.m v
      let fs := computeFull R (val c.h) (val c.s) c.m v
      unless (computeCompactStats R (val c.h) (val c.s) c.m v).value == cs &&
          (computeFullStats R (val c.h) (val c.s) c.m v).value == fs &&
          computeFast R (val c.h) (val c.s) c.m v == cs do
        throw (IO.userError s!"{c.name}: ordered table mismatch at {v}")
      emit [("case", Lean.toJson c.name), ("node", Lean.toJson v.val),
        ("compactTable", Lean.toJson (cs.map fun e =>
          (e.active.toList, e.cost.toList.map toString))),
        ("fullTable", Lean.toJson (fs.map fun e => (e.q.toList, e.cost.toList.map toString)))]

def main (args : List String) : IO Unit := do
  let reps := (args[0]?.getD "20").toNat?.getD 20
  let rounds := (args[1]?.getD "7").toNat?.getD 7
  let start := (args[2]?.getD "0").toNat?.getD 0
  if reps = 0 || rounds = 0 then throw (IO.userError "positive repetitions required")
  for (test, idx) in cases.zipIdx do
    if idx ≥ start then
      emit [("phase", Lean.toJson "case_start"), ("case", Lean.toJson test.name),
        ("index", Lean.toJson idx)]
      validateCase test
      let input ← IO.mkRef test
      for mode in [:3] do
        emit [("phase", Lean.toJson "warmup"), ("case", Lean.toJson test.name)]
        discard (timedBatch mode 1 input)
      for round in [:rounds] do
        for offset in [:3] do
          let mode := (round + offset) % 3
          emit [("phase", Lean.toJson "timing"), ("case", Lean.toJson test.name),
            ("mode", Lean.toJson mode), ("round", Lean.toJson round)]
          let (ns, checksum) ← timedBatch mode reps input
          emit [("case", Lean.toJson test.name), ("mode", Lean.toJson mode),
            ("round", Lean.toJson round), ("ns", Lean.toJson ns),
            ("reps", Lean.toJson reps), ("checksum", Lean.toJson checksum)]
      emit [("phase", Lean.toJson "case_done"), ("case", Lean.toJson test.name),
        ("index", Lean.toJson idx)]
  emit [("phase", Lean.toJson "complete")]

end UAVProof.TreeBudgetSubtreeStatsBench
