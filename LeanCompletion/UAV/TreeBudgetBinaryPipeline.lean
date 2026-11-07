import LeanCompletion.UAV.TreeBudgetBinaryInput
import LeanCompletion.UAV.TreeBudgetBinaryPreprocessing
import LeanCompletion.UAV.TreeBudgetCostedCandidates
import LeanCompletion.UAV.TreeBudgetBinarySearch

/-! Executable composition of the checked binary frontend, division-free
preprocessing, ordered candidates and search. The recorded phase work excludes
the frontend and final wire encoder; it is deliberately not named total time.
The proof-only rooted tree appears only in correspondence statements. -/
namespace UAVProof.TreeBudgetBinaryPipeline
open TreeBudgetBinaryInput TreeBudgetBinaryCodec TreeBudgetBinaryPreprocessing
open TreeBudgetCostedCandidates TreeBudgetBinarySearch TreeBudgetCostedSearch
open TreeBudgetVectorMemoState TreeBudgetVectorMemoIntegration TreeBudgetVectorSearchStats
open TreeBudgetParentArray TreeBudgetVector TreeBudgetVectorChecker TreeBudgetPatterns

def preparedSearch (I : Input) : Run (AnswerV I.n × CacheV I.n) :=
  let H := normalizeCost I.parents I.H
  let A := scaleFeesCost I.numerators I.denominators I.budgetDenominator
  let budget := scaleBudgetCost I.denominators I.budgetNumerator
  let ps := candidateCost I.parents H.value A.value budget.value
  let count := rootCountCost I.parents H.value
  let out := search ps.value count.value H.value []
  { out with
    work := H.steps + A.steps + budget.steps + ps.steps + count.steps + out.work
    allocations := H.allocations + A.allocations + budget.allocations +
      ps.allocations + count.allocations + out.allocations }

theorem preparedSearch_observe (I : Input) :
    observe (preparedSearch I) =
      initialRowsStatV (toRootedTree I.parents I.valid) I.H
        (scaleFees I.numerators I.denominators I.budgetDenominator)
        (scaleBudget I.denominators I.budgetNumerator I.budgetDenominator)
        (rootCount (toRootedTree I.parents I.valid)
          (decode (TreeBudgetVector.normalize (toRootedTree I.parents I.valid) I.H))) := by
  simp only [preparedSearch, observe, normalizeCost_value I.parents I.valid,
    scaleFeesCost_value _ _ _ I.positive,
    scaleBudgetCost_value _ _ _ I.budgetPositive,
    candidateCost_value I.parents I.valid, rootCountCost_value I.parents I.valid]
  exact memoCost_observe (backend I.n) _ _ _ _

def matrixBits {n : ℕ} (answer : AnswerV n) : Option Bits :=
  answer.map (fun rows => encodeMatrix (rows.map Vector.toList))

theorem matrixBits_roundtrip {n : ℕ} (answer : AnswerV n) :
    (matrixBits answer).bind parseMatrix = answer.map (fun rows => rows.map Vector.toList) := by
  cases answer <;> simp [matrixBits]

structure Result where
  n : ℕ
  output : Option Bits
  cache : CacheV n
  events : TreeBudgetSearchStats.Counts
  phaseWork : ℕ
  phaseAllocations : ℕ

def runInput (I : Input) : Result :=
  let out := preparedSearch I
  ⟨I.n, matrixBits out.value.1, out.value.2, out.events, out.work, out.allocations⟩

/-- The outer `none` denotes malformed input; an accepted result whose output
is `none` denotes infeasibility. Successful zero-row answers encode a matrix. -/
def run (bits : Bits) : Option Result := (parse bits).map runInput

theorem run_encode (I : RawInput) (hs : Shape I) :
    run (encodeInput I) = (decodeRaw I).map runInput := by
  simp [run, parse_encode I hs]

theorem run_rejects_invalid (bits : Bits) (h : parse bits = none) : run bits = none := by
  simp [run, h]

end UAVProof.TreeBudgetBinaryPipeline
