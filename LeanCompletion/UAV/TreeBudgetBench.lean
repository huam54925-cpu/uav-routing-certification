import LeanCompletion.UAV.TreeBudgetBenchCases

/-! Run with `lake env lean --run LeanCompletion/UAV/TreeBudgetBench.lean CASE REPS`.
Timing uses original (uninstrumented) executors. Raw records are JSON lines.
The supervising runner gives each phase a hard wall-clock deadline. -/
namespace UAVProof.TreeBudgetBench
open TreeFlowExistence TreeBudgetPatterns TreeBudgetRow TreeBudgetCertificate
open TreeBudgetMemoState TreeBudgetMemoSearch TreeBudgetMemoIntegration
open TreeBudgetResidualSearch TreeBudgetSearchStats TreeBudgetCertificateCompression
open TreeBudgetExamples TreeFlowExamples TreeBudgetCheckerExamples TreeBudgetRootFactorization
open TreeBudgetBenchCases

def emit (fields : List (String × Lean.Json)) : IO Unit := do
  IO.println (Lean.Json.mkObj fields).compress
  (← IO.getStdout).flush

def statsJson (c : Counts) : Lean.Json := Lean.toJson
  [c.calls, c.hits, c.expansions, c.candidates, c.lookupComparisons, c.insertionScans]

def answerSize {n : ℕ} (a : Answer n) : ℕ := (a.getD []).length

def answerSnapshot {n : ℕ} (a : Answer n) : Option (List (List ℕ)) :=
  a.map fun rows => rows.map fun p => List.ofFn p

def outputSnapshot {n : ℕ} (o : Answer n × Cache n) : String :=
  (Lean.toJson (answerSnapshot o.1, o.2.map fun (q, a) =>
    ((q.1, List.ofFn q.2), answerSnapshot a))).compress

/-- Read input from IO for every sample. Write the result to an IO.Ref BEFORE
the end timestamp, preventing pure evaluation from floating past the clock read.
Timer and reference-write overhead are not subtracted. First sample is warm-up. -/
@[noinline] def measure {α β : Type} (name : String) (reps : ℕ)
    (input : IO α) (f : α → β) (consume : β → ℕ) : IO Unit := do
  emit [("phase", Lean.toJson name)]
  let mut samples : Array Nat := #[]
  let mut checksum := 0
  for i in [:reps + 1] do
    let x ← input
    let result ← IO.mkRef (none : Option β)
    let t ← IO.monoNanosNow
    result.set (some (f x))
    let stop ← IO.monoNanosNow
    let some out ← result.get | throw (IO.userError "missing timed result")
    checksum := checksum + consume out
    if i > 0 then samples := samples.push (stop - t)
  emit [("timing", Lean.toJson name), ("ns", Lean.toJson samples),
    ("checksum", Lean.toJson checksum)]

def runCase {n : ℕ} (name : String) (R : RootedTree (Fin n)) (h : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (reps : ℕ) : IO Unit := do
  let H := normalize R h
  let k := rootCount R H
  emit [("case", Lean.toJson name), ("n", Lean.toJson n), ("k", Lean.toJson k),
    ("H", Lean.toJson (List.ofFn H)), ("phase", Lean.toJson "counts")]
  let ps := TreeBudgetFiniteSearch.candidates R H s T
  let nc := searchStat ps k H
  let mc := memoStat ps k H emptyCache
  let hot := memoStat ps k H mc.1.2
  unless answerSnapshot nc.1 == answerSnapshot (searchRowsWith ps k H) &&
      outputSnapshot mc.1 == outputSnapshot (memoRowsWith ps k H emptyCache) &&
      outputSnapshot hot.1 == outputSnapshot mc.1 &&
      answerSnapshot nc.1 == answerSnapshot mc.1.1 &&
      nc.2.calls == nc.2.expansions && mc.2.calls == mc.2.hits + mc.2.expansions &&
      mc.2.expansions == mc.1.2.length do
    throw (IO.userError "executor/count consistency failure")
  let rows := mc.1.1.getD []
  let cert := unitCertificate rows
  let compressed := compressCertificate cert
  if mc.1.1.isSome then
    unless checkCertificate R H k s T cert && checkCertificate R H k s T compressed do
      throw (IO.userError "certificate rejected")
  emit [("case", Lean.toJson name), ("candidates", Lean.toJson ps.length),
    ("boundedVectors", Lean.toJson (TreeBudgetFiniteSearch.boundedVectors n (bound R H)).length),
    ("success", Lean.toJson mc.1.1.isSome), ("uncached", statsJson nc.2),
    ("cold", statsJson mc.2), ("hot", statsJson hot.2),
    ("entries", Lean.toJson mc.1.2.length), ("witnessRows", Lean.toJson (witnessRows mc.1.2)),
    ("outputBefore", Lean.toJson (if mc.1.1.isSome then some cert.size else none)),
    ("outputAfter", Lean.toJson (if mc.1.1.isSome then some compressed.size else none))]
  let href ← IO.mkRef H
  let pref ← IO.mkRef ps
  let cref ← IO.mkRef mc.1.2
  let coldInput := do return (← pref.get, ← href.get)
  let warmInput := do return (← pref.get, ← href.get, ← cref.get)
  measure "candidates" reps href.get
    (fun h => TreeBudgetFiniteSearch.candidates R h s T) List.length
  measure "search_uncached" reps coldInput
    (fun (ps, h) => searchRowsWith ps k h) answerSize
  measure "search_cold" reps coldInput
    (fun (ps, h) => memoRowsWith ps k h emptyCache) (fun o => answerSize o.1 + o.2.length)
  measure "search_hot" reps warmInput
    (fun (ps, h, c) => memoRowsWith ps k h c) (fun o => answerSize o.1 + o.2.length)
  measure "full_uncached" reps href.get
    (fun h => searchRows R h s T k h) answerSize
  measure "full_cold" reps href.get
    (fun h => memoRows R h s T k h emptyCache) (fun o => answerSize o.1 + o.2.length)
  measure "full_hot" reps (do return (← href.get, ← cref.get))
    (fun (h, c) => memoRows R h s T k h c) (fun o => answerSize o.1 + o.2.length)
  if mc.1.1.isSome then
    let certRef ← IO.mkRef cert
    measure "compress_only" reps certRef.get compressCertificate (fun c => c.size)

def branchRun (reps : ℕ) : IO Unit := do
  let R := centerThree
  let h : Fin 3 → ℕ := ![2, 0, 3]
  let s : Fin 3 → ℚ := ![10, 0, 2]
  runCase "branches_global" R h s 10 reps
  for c in TreeBudgetBranchCertificate.rootChildren R do
    runCase s!"branch_{c.val.val}" R (branchMultiplicity R h c) s 10 reps
  let ref ← IO.mkRef h
  emit [("phase", Lean.toJson "branch_check")]
  let mc := searchByRootMemo R h 5 s 10
  let nc := TreeBudgetResidualBranchSearch.searchByRoot R h 5 s 10
  unless mc.isSome && nc.isSome do throw (IO.userError "branch search failed")
  for cert in mc.toList ++ nc.toList do
    unless checkCertificate R h 5 s 10 cert do throw (IO.userError "branch certificate rejected")
  emit [("branchOutputBefore", Lean.toJson (mc.map fun c => c.size)),
    ("branchOutputAfter", Lean.toJson (mc.map fun c => (compressCertificate c).size))]
  measure "branch_full_uncached" reps ref.get
    (fun h => TreeBudgetResidualBranchSearch.searchByRoot R h 5 s 10)
    (fun c => (c.map fun c => c.size).getD 0)
  measure "branch_full_memo" reps ref.get (fun h => searchByRootMemo R h 5 s 10)
    (fun c => (c.map fun c => c.size).getD 0)

end UAVProof.TreeBudgetBench

open UAVProof.TreeBudgetBench UAVProof.TreeBudgetBenchCases
  UAVProof.TreeBudgetExamples UAVProof.TreeFlowExamples UAVProof.TreeBudgetCheckerExamples

def main (args : List String) : IO Unit := do
  let name := args[0]?.getD "shared_failure"
  let reps := (args[1]?.bind String.toNat?).getD 21
  if reps > 100 then throw (IO.userError "repetition cap: 100")
  match name with
    | "all" => do
      runCase "shared_failure" hubTree (sharedH 2) fees 10 reps
      runCase "shared_success" hubTree (sharedH 3) fees 10 reps
      runCase "early_stop" hubTree ![0, 1, 0, 0, 0] fees 10 reps
      runCase "repeated" centerThree ![3, 0, 0] (fun _ => 0) 0 reps
      runCase "low_reuse" pathFour ![0, 1, 1, 1] (fun _ => 0) 0 reps
      branchRun reps
    | "shared_failure" => runCase name hubTree (sharedH 2) fees 10 reps
    | "shared_success" => runCase name hubTree (sharedH 3) fees 10 reps
    | "early_stop" => runCase name hubTree ![0, 1, 0, 0, 0] fees 10 reps
    | "repeated" => runCase name centerThree ![3, 0, 0] (fun _ => 0) 0 reps
    | "low_reuse" => runCase name pathFour ![0, 1, 1, 1] (fun _ => 0) 0 reps
    | "branches" => branchRun reps
    | _ => throw (IO.userError "unknown case")
