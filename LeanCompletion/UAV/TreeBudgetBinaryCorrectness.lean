import LeanCompletion.UAV.TreeBudgetCostedExecution

/-! Binary-input functional correctness. Fractions are interpreted directly
from the checked input fields. The serialized matrix, ordered cache and six
event counters refine the existing semantics. No machine-time conclusion is
part of this interface. -/
namespace UAVProof.TreeBudgetBinaryCorrectness
open TreeBudgetBinaryInput TreeBudgetBinaryCodec TreeBudgetBinaryPipeline
open TreeBudgetCostedExecution TreeBudgetCostedSearch TreeBudgetParentArray
open TreeBudgetVector TreeBudgetVectorMemoState TreeBudgetVectorMemoIntegration
open TreeBudgetVectorSearchStats TreeBudgetVectorCandidates TreeBudgetPatterns
open TreeBudgetMatrix TreeBudgetSearchStats
open TreeBudgetCertificate TreeBudgetResidualSearch

noncomputable def tree (I : Input) := toRootedTree I.parents I.valid

def fees (I : Input) (v : Fin I.n) : ℚ :=
  (I.numerators[v] : ℚ) / (I.denominators[v] : ℚ)

def budget (I : Input) : ℚ := (I.budgetNumerator : ℚ) / (I.budgetDenominator : ℚ)

noncomputable def normalized (I : Input) : Fin I.n → ℕ :=
  TreeBudgetPatterns.normalize (tree I) (decode I.H)

noncomputable def initialCount (I : Input) : ℕ :=
  rootCount (tree I) (decode (TreeBudgetVector.normalize (tree I) I.H))

noncomputable def reference (I : Input) :=
  memoRowsStat (tree I) (normalized I) (fees I) (budget I) (initialCount I)
    (normalized I) TreeBudgetMemoState.emptyCache

theorem preparedSearch_value_scaled (I : Input) :
    (preparedSearch I).value =
      initialRowsVScaled (tree I) I.H I.numerators I.denominators
        I.budgetNumerator I.budgetDenominator (initialCount I) := by
  have h := congrArg Prod.fst (preparedSearch_observe I)
  simpa only [observe, initialRowsStatV, memoRowsStatV, memoStatV_erase,
    initialRowsVScaled, candidatesVScaled, tree, initialCount] using h

/-- Equality includes the concrete answer, the order and multiplicity of
cache entries, and all six event fields. -/
theorem preparedSearch_refines (I : Input) :
    decodeMeasured (observe (preparedSearch I)) = reference I := by
  calc
    _ = decodeMeasured (initialRowsStatVScaled (tree I) I.H I.numerators I.denominators
        I.budgetNumerator I.budgetDenominator (initialCount I)) := by
      rw [preparedSearch_observe]
      rfl
    _ = reference I := by
      simpa only [reference, normalized, fees, budget] using
        initialRowsStatVScaled_refines (tree I) I.H I.numerators I.denominators
          I.budgetNumerator I.budgetDenominator (initialCount I) I.positive I.budgetPositive

theorem runInput_output_correct (I : Input) :
    (runInput I).output.isSome = true ↔
      MatrixFeasible (tree I) (decode I.H) (initialCount I) (fees I) (budget I) := by
  have h := searchMemoVScaled_correct (tree I) I.H I.numerators I.denominators
    I.budgetNumerator I.budgetDenominator (initialCount I) I.positive I.budgetPositive
  simpa only [runInput, matrixBits, Option.isSome_map, preparedSearch_value_scaled,
    searchMemoVScaled, decodeAnswer, fees, budget] using h

theorem runInput_output_roundtrip (I : Input) :
    (runInput I).output.bind parseMatrix =
      (preparedSearch I).value.1.map (fun rows => rows.map Vector.toList) :=
  matrixBits_roundtrip (preparedSearch I).value.1

theorem runInput_cache_events (I : Input) :
    decodeCache (runInput I).cache = (reference I).1.2 ∧
      (runInput I).events = (reference I).2 := by
  have h := preparedSearch_refines I
  exact ⟨congrArg (fun out => out.1.2) h, congrArg Prod.snd h⟩

theorem preparedSearch_certificate_sound (I : Input) (rows : RowsV I.n)
    (hrows : (preparedSearch I).value.1 = some rows) :
    checkCertificate (tree I) (decode I.H) (initialCount I) (fees I) (budget I)
      (unitCertificate (decodeRows rows)) = true := by
  have hs : searchMemoVScaled (tree I) I.H I.numerators I.denominators
      I.budgetNumerator I.budgetDenominator (initialCount I) =
        some (unitCertificate (decodeRows rows)) := by
    rw [searchMemoVScaled, ← preparedSearch_value_scaled I, hrows, decodeAnswer_some]
    rfl
  rw [searchMemoVScaled_eq _ _ _ _ _ _ _ I.positive I.budgetPositive] at hs
  exact TreeBudgetMemoIntegration.searchMemo_sound _ _ _ _ _ _ hs

theorem execute_accepted (bits : Bits) (I : Input) (h : parse bits = some I) :
    (execute bits).value = some (runInput I) := by
  simp [execute_value, run, h]

theorem execute_rejected (bits : Bits) (h : parse bits = none) :
    (execute bits).value = none := by
  simp [execute_value, run, h]

/-- For accepted inputs, the inner output option decides the existing matrix
feasibility predicate with the forced root count and the original fractions. -/
theorem execute_output_correct (bits : Bits) (I : Input) (h : parse bits = some I) :
    ((execute bits).value.bind (fun result => result.output)).isSome = true ↔
      MatrixFeasible (tree I) (decode I.H) (initialCount I) (fees I) (budget I) := by
  rw [execute_accepted bits I h]
  exact runInput_output_correct I

theorem execute_output_roundtrip (bits : Bits) (I : Input) (h : parse bits = some I) :
    ((execute bits).value.bind (fun result => result.output)).bind parseMatrix =
      (preparedSearch I).value.1.map (fun rows => rows.map Vector.toList) := by
  rw [execute_accepted bits I h]
  exact runInput_output_roundtrip I

/-- Every successful wire output decodes to the actual returned rows, whose
unit certificate passes the existing mathematical checker. -/
theorem execute_success_sound (bits : Bits) (I : Input) (h : parse bits = some I)
    (wire : Bits)
    (hw : (execute bits).value.bind (fun result => result.output) = some wire) :
    ∃ rows : RowsV I.n, (preparedSearch I).value.1 = some rows ∧
      parseMatrix wire = some (rows.map Vector.toList) ∧
      checkCertificate (tree I) (decode I.H) (initialCount I) (fees I) (budget I)
        (unitCertificate (decodeRows rows)) = true := by
  rw [execute_accepted bits I h] at hw
  change ((preparedSearch I).value.1.map
    (fun rows => encodeMatrix (rows.map Vector.toList))) = some wire at hw
  obtain ⟨rows, hrows, hwire⟩ := Option.map_eq_some_iff.mp hw
  refine ⟨rows, hrows, ?_, preparedSearch_certificate_sound I rows hrows⟩
  rw [← hwire, parseMatrix_encode]

/-- One compositional contract from raw input bits to all observable outputs.
The full result equality fixes its dependent vertex dimension as well. -/
theorem execute_refines (bits : Bits) (I : Input) (h : parse bits = some I) :
    (execute bits).value = some (runInput I) ∧
      (runInput I).output.bind parseMatrix =
        (preparedSearch I).value.1.map (fun rows => rows.map Vector.toList) ∧
      decodeCache (runInput I).cache = (reference I).1.2 ∧
      (runInput I).events = (reference I).2 := by
  exact ⟨execute_accepted bits I h, runInput_output_roundtrip I, runInput_cache_events I⟩

theorem execute_encode_correct (raw : RawInput) (I : Input)
    (h : decodeRaw raw = some I) :
    ((execute (encodeInput raw)).value.bind (fun result => result.output)).isSome = true ↔
      MatrixFeasible (tree I) (decode I.H) (initialCount I) (fees I) (budget I) := by
  apply execute_output_correct (encodeInput raw) I
  rw [parse_encode raw (decodeRaw_shape raw I h)]
  exact h

end UAVProof.TreeBudgetBinaryCorrectness

#print axioms UAVProof.TreeBudgetBinaryCorrectness.tree
#print axioms UAVProof.TreeBudgetBinaryCorrectness.fees
#print axioms UAVProof.TreeBudgetBinaryCorrectness.budget
#print axioms UAVProof.TreeBudgetBinaryCorrectness.normalized
#print axioms UAVProof.TreeBudgetBinaryCorrectness.initialCount
#print axioms UAVProof.TreeBudgetBinaryCorrectness.reference
#print axioms UAVProof.TreeBudgetBinaryCorrectness.preparedSearch_value_scaled
#print axioms UAVProof.TreeBudgetBinaryCorrectness.preparedSearch_refines
#print axioms UAVProof.TreeBudgetBinaryCorrectness.runInput_output_correct
#print axioms UAVProof.TreeBudgetBinaryCorrectness.runInput_output_roundtrip
#print axioms UAVProof.TreeBudgetBinaryCorrectness.runInput_cache_events
#print axioms UAVProof.TreeBudgetBinaryCorrectness.preparedSearch_certificate_sound
#print axioms UAVProof.TreeBudgetBinaryCorrectness.execute_accepted
#print axioms UAVProof.TreeBudgetBinaryCorrectness.execute_rejected
#print axioms UAVProof.TreeBudgetBinaryCorrectness.execute_output_correct
#print axioms UAVProof.TreeBudgetBinaryCorrectness.execute_output_roundtrip
#print axioms UAVProof.TreeBudgetBinaryCorrectness.execute_success_sound
#print axioms UAVProof.TreeBudgetBinaryCorrectness.execute_refines
#print axioms UAVProof.TreeBudgetBinaryCorrectness.execute_encode_correct
