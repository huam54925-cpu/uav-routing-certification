import LeanCompletion.UAV.TreeBudgetStoredPreparation
import LeanCompletion.UAV.TreeBudgetStoredOutput
import LeanCompletion.UAV.TreeBudgetBinaryCorrectness

/-! One executable path from input bits through checked preparation, initialized
storage, memoD, and charged output. Its costs are its own; the common observer
compares only dimension, output, ordered cache and six logical events. -/
namespace UAVProof.TreeBudgetStoredExecution
open TreeBudgetBitMachine TreeBudgetAllocationBounds TreeBudgetTypedStore
open TreeBudgetSearchStore TreeBudgetSharedAnswerStore TreeBudgetChargedCache
open TreeBudgetStoredSearch TreeBudgetStoredPreparation TreeBudgetStoredOutput
open TreeBudgetBinaryInput TreeBudgetBinaryCodec TreeBudgetBinaryPipeline
open TreeBudgetCostedParsing TreeBudgetCostedInput TreeBudgetBinarySearch
open TreeBudgetVectorMemoState TreeBudgetSearchStats

structure StoredResult where
  n : ℕ
  output : Option Bits
  heap : Heap
  answer : ℕ
  cache : ℕ
  events : Counts

inductive Outcome where
  | invalid
  | storageError
  | accepted (result : StoredResult)

structure Observation where
  n : ℕ
  output : Option Bits
  cache : WireCache
  events : Counts
  deriving DecidableEq

def observeReference (out : Option TreeBudgetBinaryPipeline.Result) : Option Observation :=
  out.map fun r => ⟨r.n, r.output, wireCache r.cache, r.events⟩

def observeResult (r : StoredResult) : Option Observation :=
  (observeCache (r.heap.size + 1) r.heap r.cache).map fun cs => ⟨r.n, r.output, cs, r.events⟩

def observeStored : Outcome → Option (Option Observation)
  | .invalid => some none
  | .storageError => none
  | .accepted r => (observeResult r).map some

def executeInput (I : Input) : Costed (Option StoredResult) :=
  TreeBudgetBitMachine.bind (prepareInput I) fun prepared =>
    TreeBudgetBitMachine.bind (initializeStore prepared) fun initial =>
      thenD (memoD I.n initial.candidates prepared.depth initial.heap
        initial.residual initial.cache initial.parent) fun searched =>
        thenD (emitStored searched.heap searched.answer) fun output =>
          charge 1 6 (ret ⟨I.n, output, searched.heap, searched.answer, searched.cache, searched.events⟩)

def executeChecked : Option Input → Costed Outcome
  | none => ⟨.invalid, 1, 1⟩
  | some I =>
    let out := executeInput I
    ⟨match out.value with | none => .storageError | some r => .accepted r,
      out.steps + 1, out.allocations + 1⟩

def executeRaw : Option RawInput → Costed Outcome
  | none => ⟨.invalid, 1, 1⟩
  | some I =>
    let checked := decodeRawCost I
    let out := executeChecked checked.value
    ⟨out.value, checked.steps + out.steps + 1, checked.allocations + out.allocations + 1⟩

def executeStored (bits : Bits) : Costed Outcome :=
  let parsed := parseInputD bits
  let out := executeRaw parsed.value
  ⟨out.value, parsed.steps + out.steps + 1, parsed.allocations + out.allocations + 1⟩

def InputResultRep (I : Input) (out : StoredResult) : Prop :=
  out.n = I.n ∧ out.output = (runInput I).output ∧
    SharedAnswerRep out.heap out.answer (wireAnswer (preparedSearch I).value.1) ∧
    TreeBudgetChargedCache.CacheRep out.heap out.cache (wireCache (runInput I).cache) ∧
    out.events = (runInput I).events ∧ WellFormed out.heap

theorem executeInput_correct (I : Input) :
    ∃ out, (executeInput I).value = some out ∧ InputResultRep I out := by
  let prepared := (prepareInput I).value
  let initial := (initializeStore prepared).value
  obtain ⟨hh, hp, hr, hc, hf, hparent⟩ := initializeStore_correct prepared
  have hs := memoD_refines_cost (backend I.n) prepared.candidates initial.candidates prepared.depth
    initial.heap initial.residual initial.cache initial.parent prepared.residual [] hh hp hr hc hparent
  have hv := (prepareInput_search I).1
  have he := (prepareInput_search I).2
  change (preparedSearch I).value = _ at hv
  rw [← hv, ← he] at hs
  obtain ⟨searched, hsearched, ha, hcache, hw, hext, hevents⟩ := hs
  have hout := emitStored_correct searched.heap searched.answer _ hw ha
  have hwire : (wireAnswer (preparedSearch I).value.1).map encodeMatrix =
      matrixBits (preparedSearch I).value.1 := by
    cases (preparedSearch I).value.1 <;> rfl
  rw [hwire] at hout
  refine ⟨⟨I.n, matrixBits (preparedSearch I).value.1, searched.heap,
    searched.answer, searched.cache, searched.events⟩, ?_, rfl, rfl, ha, hcache, hevents, hw⟩
  simp only [executeInput, costBind_value]
  change (thenD (memoD I.n initial.candidates prepared.depth initial.heap
    initial.residual initial.cache initial.parent) _).value = _
  simp [hsearched, hout, charge, ret]

theorem input_observe (I : Input) (out : StoredResult) (h : InputResultRep I out) :
    observeResult out = some ⟨I.n, (runInput I).output, wireCache (runInput I).cache, (runInput I).events⟩ := by
  obtain ⟨hn, ho, ha, hc, he, hw⟩ := h
  have hb := TreeBudgetChargedCache.cacheRep_address_lt hc
  simp [observeResult, observeCache_correct out.heap out.cache (wireCache (runInput I).cache)
    hw hc (out.heap.size + 1) (by omega), hn, ho, he]

theorem executeChecked_observe (input : Option Input) :
    observeStored (executeChecked input).value = some (observeReference (input.map runInput)) := by
  cases input with
  | none => rfl
  | some I =>
    obtain ⟨out, hv, hr⟩ := executeInput_correct I
    simp [executeChecked, hv, observeStored, input_observe I out hr, observeReference,
      TreeBudgetBinaryPipeline.runInput]

theorem executeRaw_observe (raw : Option RawInput) :
    observeStored (executeRaw raw).value = some (observeReference ((raw.bind decodeRaw).map runInput)) := by
  cases raw with
  | none => rfl
  | some I => simp [executeRaw, executeChecked_observe]

/-- Exact observation equality for every input, including malformed bitstrings. -/
theorem executeStored_refines (bits : Bits) :
    observeStored (executeStored bits).value = some (observeReference (run bits)) := by
  simp [executeStored, executeRaw_observe, run, TreeBudgetBinaryInput.parse]

theorem executeStored_no_storage_error (bits : Bits) :
    (executeStored bits).value ≠ .storageError := by
  intro he
  have h := executeStored_refines bits
  rw [he] at h
  cases h

theorem executeStored_rejected (bits : Bits) (h : parse bits = none) :
    (executeStored bits).value = .invalid := by
  unfold executeStored
  simp only [parseInputD_value]
  cases hp : parseInput bits with
  | none => rfl
  | some raw =>
    have hd : decodeRaw raw = none := by simpa [TreeBudgetBinaryInput.parse, hp] using h
    simp [executeRaw, hd, executeChecked]

theorem executeStored_accepted (bits : Bits) (I : Input) (h : parse bits = some I) :
    ∃ out, (executeStored bits).value = .accepted out ∧ InputResultRep I out := by
  obtain ⟨raw, hp, hd⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨out, ho, hr⟩ := executeInput_correct I
  exact ⟨out, by simp [executeStored, hp, executeRaw, hd, executeChecked, ho], hr⟩

def publicOutput : Outcome → Option Bits
  | .accepted r => r.output
  | _ => none

theorem executeStored_output_correct (bits : Bits) (I : Input) (h : parse bits = some I) :
    (publicOutput (executeStored bits).value).isSome = true ↔
      TreeBudgetMatrix.MatrixFeasible (TreeBudgetBinaryCorrectness.tree I)
        (TreeBudgetVector.decode I.H) (TreeBudgetBinaryCorrectness.initialCount I)
        (TreeBudgetBinaryCorrectness.fees I) (TreeBudgetBinaryCorrectness.budget I) := by
  obtain ⟨out, ho, hr⟩ := executeStored_accepted bits I h
  rw [ho]
  change out.output.isSome = true ↔ _
  rw [hr.2.1]
  exact TreeBudgetBinaryCorrectness.runInput_output_correct I

theorem executeStored_success_sound (bits : Bits) (I : Input) (h : parse bits = some I)
    (wire : Bits) (hw : publicOutput (executeStored bits).value = some wire) :
    ∃ rows : RowsV I.n, (preparedSearch I).value.1 = some rows ∧
      parseMatrix wire = some (rows.map Vector.toList) ∧
      TreeBudgetCertificate.checkCertificate (TreeBudgetBinaryCorrectness.tree I)
        (TreeBudgetVector.decode I.H) (TreeBudgetBinaryCorrectness.initialCount I)
        (TreeBudgetBinaryCorrectness.fees I) (TreeBudgetBinaryCorrectness.budget I)
        (TreeBudgetResidualSearch.unitCertificate (decodeRows rows)) = true := by
  obtain ⟨out, ho, hr⟩ := executeStored_accepted bits I h
  rw [ho] at hw
  change out.output = some wire at hw
  rw [hr.2.1] at hw
  apply TreeBudgetBinaryCorrectness.execute_success_sound bits I h wire
  rw [TreeBudgetBinaryCorrectness.execute_accepted bits I h]
  exact hw

end UAVProof.TreeBudgetStoredExecution
