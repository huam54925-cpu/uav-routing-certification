import LeanCompletion.UAV.TreeBudgetStoredSearch

/-! Charged materialization of a shared answer followed by canonical encoding.
Only the final answer is expanded by the production output path. Cache decoding
below is a proof observation and is not part of the executable output. -/
namespace UAVProof.TreeBudgetStoredOutput
open TreeBudgetStoredCursor TreeBudgetBitPrimitives
open TreeBudgetBitMachine TreeBudgetAllocationBounds TreeBudgetTypedStore
open TreeBudgetSearchStore TreeBudgetSharedAnswerStore TreeBudgetChargedCache
open TreeBudgetStoredSearch TreeBudgetBinaryCodec TreeBudgetCostedCodec TreeBudgetCostedParsing

def rowRead (heap : Heap) (a : ℕ) : Costed (Option (List ℕ)) :=
  thenD (blobRead heap a) fun bits => thenD (parseNatsD bits) fun out =>
    match out.2 with
    | [] => ret out.1
    | _ :: _ => bad

theorem rowRead_correct (heap : Heap) (a : ℕ) (row : List ℕ)
    (hh : WellFormed heap) (hr : RowRep heap a row) :
    (rowRead heap a).value = some row := by
  have hp := parseNats_append row []
  simp only [List.append_nil] at hp
  simp [rowRead, blobRead_correct _ _ _ hh hr, hp, ret]

def rowsRead (fuel : ℕ) (heap : Heap) (a : ℕ) : Costed (Option Matrix) :=
  thenD (cursorStep fuel) fun remaining =>
    thenD (rowsHead heap a) fun node => match node with
    | none => ret []
    | some (row, tail) => thenD (rowRead heap row) fun p =>
        thenD (rowsRead remaining.val heap tail) fun ps => charge 1 1 (ret (p :: ps))
termination_by fuel
decreasing_by exact remaining.isLt

theorem rowsRead_succ_value (fuel : ℕ) (heap : Heap) (a : ℕ) :
    (rowsRead (fuel + 1) heap a).value =
      (thenD (rowsHead heap a) fun node => match node with
    | none => ret []
    | some (row, tail) => thenD (rowRead heap row) fun p =>
        thenD (rowsRead fuel heap tail) fun ps => charge 1 1 (ret (p :: ps))).value := by
  rw [rowsRead]
  simp only [thenD_value, cursorStep_succ, Option.bind_some]


theorem rowsRead_correct (heap : Heap) (a : ℕ) (rows : Matrix)
    (hh : WellFormed heap) (hr : RowsRep heap a rows) (fuel : ℕ) (hf : a < fuel) :
    (rowsRead fuel heap a).value = some rows := by
  induction hr generalizing fuel with
  | nil a header =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [rowsRead_succ_value, rowsHead_nil _ _ hh header, ret]
  | cons a row tail p ps header hp hps hl ht ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [rowsRead_succ_value, rowsHead_cons _ _ _ _ hh header, rowRead_correct _ _ _ hh hp,
        ih fuel (by omega), charge, ret]

def answerRead (heap : Heap) (a : ℕ) : Costed (Option WireAnswer) :=
  thenD (answerHead heap a) fun answer => match answer with
  | none => ret none
  | some rows => TreeBudgetBitMachine.bind (addNatD heap.size 1) fun fuel =>
      thenD (rowsRead fuel heap rows) fun matrix => charge 1 1 (ret (some matrix))

theorem answerRead_correct (heap : Heap) (a : ℕ) (ans : WireAnswer)
    (hh : WellFormed heap) (hr : SharedAnswerRep heap a ans) :
    (answerRead heap a).value = some ans := by
  cases ans with
  | none => simp [answerRead, answerHead_failure _ _ hh hr, ret]
  | some rows =>
    obtain ⟨r, hread, hrows⟩ := answerHead_success _ _ _ hh hr
    have hb := rowsRep_address_lt hrows
    simp [answerRead, hread, rowsRead_correct heap r rows hh hrows (heap.size + 1) (by omega), charge, ret]

/-- Outer `none` is a storage error; `some none` is a valid failed answer. -/
def emitStored (heap : Heap) (a : ℕ) : Costed (Option (Option Bits)) :=
  thenD (answerRead heap a) fun answer => match answer with
  | none => ret none
  | some rows => TreeBudgetBitMachine.bind (encodeMatrixD rows) fun bits =>
      charge 1 1 (ret (some bits))

theorem emitStored_correct (heap : Heap) (a : ℕ) (ans : WireAnswer)
    (hh : WellFormed heap) (hr : SharedAnswerRep heap a ans) :
    (emitStored heap a).value = some (ans.map encodeMatrix) := by
  cases ans <;> simp [emitStored, answerRead_correct _ _ _ hh hr, charge, ret]

theorem emitStored_roundtrip (heap : Heap) (a : ℕ) (rows : Matrix)
    (hh : WellFormed heap) (hr : SharedAnswerRep heap a (some rows)) :
    ((emitStored heap a).value.bind id).bind parseMatrix = some rows := by
  simp [emitStored_correct _ _ _ hh hr]

/-- Read-only output leaves the heap and every old representation unchanged. -/
theorem emitStored_preserves (heap : Heap) (a : ℕ) (ans : WireAnswer)
    (hh : WellFormed heap) (hr : SharedAnswerRep heap a ans) :
    (emitStored heap a).value = some (ans.map encodeMatrix) ∧ Extends heap heap ∧ WellFormed heap :=
  ⟨emitStored_correct heap a ans hh hr, extends_refl heap, hh⟩

def observeCache : ℕ → Heap → ℕ → Option WireCache
  | 0, _, _ => none
  | fuel + 1, heap, a => do
    let node ← (headRead heap a).value
    match node with
    | none => some []
    | some (key, answer, tail) =>
      let q ← (keyRead heap key).value
      let ans ← (answerRead heap answer).value
      let cs ← observeCache fuel heap tail
      some ((q, ans) :: cs)

theorem observeCache_correct (heap : Heap) (a : ℕ) (cs : WireCache)
    (hh : WellFormed heap) (hr : TreeBudgetChargedCache.CacheRep heap a cs)
    (fuel : ℕ) (hf : a < fuel) : observeCache fuel heap a = some cs := by
  induction hr generalizing fuel with
  | nil a header =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [observeCache, headRead_nil _ _ hh header]
  | cons a key answer tail q ans cs header hk ha ht hl ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp [observeCache, headRead_cons _ _ _ _ _ hh header, keyRead_correct _ _ _ hh hk,
        answerRead_correct _ _ _ hh ha, ih fuel (by omega)]

end UAVProof.TreeBudgetStoredOutput
