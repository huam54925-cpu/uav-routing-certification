import LeanCompletion.UAV.TreeBudgetSearchStatsBounds

/-! Kernel-checked regressions for growth and operation counts in the existing measured executor.
These raw lists deliberately include repeated candidates and inconsistent duplicate
cache answers. No semantic cache validity is assumed. Concrete counts below check
boundary cases for the general bounds proved in the imported module. -/
namespace UAVProof.TreeBudgetSearchStatsBoundsExamples
open TreeBudgetMemoState TreeBudgetSearchStats TreeBudgetSearchStatsBounds

def zeroRow : Fin 1 → ℕ := fun _ => 0
def oneRow : Fin 1 → ℕ := fun _ => 1
def twoRow : Fin 1 → ℕ := fun _ => 2

def zeroSuccess := memoStat [] 0 zeroRow emptyCache
def zeroFailure := memoStat [] 0 oneRow emptyCache

theorem zero_steps_success_grows :
    zeroSuccess.1.1 = some [] ∧ zeroSuccess.1.2.length = 1 ∧
      zeroSuccess.2.expansions = 1 ∧
      lookup zeroSuccess.1.2 (0, zeroRow) = some (some []) := by
  decide +kernel

theorem zero_steps_failure_grows :
    zeroFailure.1.1 = none ∧ zeroFailure.1.2.length = 1 ∧
      zeroFailure.2.expansions = 1 ∧
      lookup zeroFailure.1.2 (0, oneRow) = some none := by
  decide +kernel

def emptyCandidates := memoStat [] 2 oneRow emptyCache

theorem positive_depth_empty_candidates :
    emptyCandidates.1.1 = none ∧ emptyCandidates.1.2.length = 1 ∧
      emptyCandidates.2.expansions = 1 ∧ emptyCandidates.2.calls = 1 ∧
      emptyCandidates.2.candidates = 0 := by
  decide +kernel

def guardFailure := memoStat [twoRow] 1 oneRow emptyCache

/-- A rejected guard must not evaluate a child at the truncated residual zero. -/
theorem rejected_guard_does_not_recurse :
    guardFailure.1.1 = none ∧ guardFailure.1.2.length = 1 ∧
      guardFailure.2.expansions = 1 ∧ guardFailure.2.calls = 1 ∧
      guardFailure.2.candidates = 1 ∧
      lookup guardFailure.1.2 (0, zeroRow) = none := by
  decide +kernel

def duplicateOld : Cache 1 :=
  [((7, zeroRow), none), ((7, zeroRow), some [])]

/-- Two unrelated duplicate entries remain verbatim after a missing-key insert. -/
theorem unrelated_duplicates_are_retained :
    (memoStat [] 0 zeroRow duplicateOld).1.2 =
      ((0, zeroRow), some []) :: duplicateOld ∧
    (memoStat [] 0 zeroRow duplicateOld).1.2.length = 3 ∧
    (memoStat [] 0 zeroRow duplicateOld).2.expansions = 1 ∧
    (memoStat [] 0 zeroRow duplicateOld).2.insertionScans = 2 := by
  decide +kernel

def duplicateCurrent : Cache 1 :=
  [((2, oneRow), none), ((2, oneRow), some [])]
def cachedFailure := memoStat [zeroRow, oneRow] 2 oneRow duplicateCurrent

/-- Outer `some none` is a hit; even conflicting duplicates are left untouched. -/
theorem cached_failure_is_not_a_miss :
    lookup duplicateCurrent (2, oneRow) = some none ∧
      cachedFailure.1 = (none, duplicateCurrent) ∧
      cachedFailure.1.2.length = 2 ∧ cachedFailure.2.calls = 1 ∧
      cachedFailure.2.hits = 1 ∧ cachedFailure.2.expansions = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem cached_empty_success_is_not_a_miss :
    (memoStat [] 0 zeroRow zeroSuccess.1.2).1 = zeroSuccess.1 ∧
      (memoStat [] 0 zeroRow zeroSuccess.1.2).2.hits = 1 ∧
      (memoStat [] 0 zeroRow zeroSuccess.1.2).2.expansions = 0 := by
  decide +kernel

def repeatedZero := memoStat [zeroRow, zeroRow] 1 oneRow emptyCache

/-- The second zero candidate reuses the failed child at the same full key. -/
theorem repeated_zero_candidate_reuses_failure :
    repeatedZero.1.1 = none ∧ repeatedZero.1.2.length = 2 ∧
      repeatedZero.2.expansions = 2 ∧ repeatedZero.2.calls = 3 ∧
      repeatedZero.2.hits = 1 ∧ repeatedZero.2.candidates = 2 ∧
      lookup repeatedZero.1.2 (0, oneRow) = some none ∧
      lookup repeatedZero.1.2 (1, oneRow) = some none := by
  decide +kernel

def backtrack := memoStat [zeroRow, oneRow, twoRow] 1 oneRow emptyCache

/-- The failed child survives; the successful next candidate stops the scan
before the third candidate. The parent is inserted only after both children. -/
theorem child_failure_then_success_stops_scan :
    backtrack.1.1 = some [oneRow] ∧ backtrack.1.2.length = 3 ∧
      backtrack.2.expansions = 3 ∧ backtrack.2.calls = 3 ∧
      backtrack.2.hits = 0 ∧ backtrack.2.candidates = 2 ∧
      lookup backtrack.1.2 (0, oneRow) = some none ∧
      lookup backtrack.1.2 (0, zeroRow) = some (some []) ∧
      lookup backtrack.1.2 (1, oneRow) = some (some [oneRow]) := by
  decide +kernel

/-- The general theorem accepts this duplicate raw cache for every call. -/
theorem arbitrary_execution_from_duplicates (ps : List (Fin 1 → ℕ))
    (k : ℕ) (r : Fin 1 → ℕ) :
    (memoStat ps k r duplicateOld).1.2.length =
      2 + (memoStat ps k r duplicateOld).2.expansions := by
  simpa only [duplicateOld, List.length_cons, List.length_nil] using
    memoStat_cache_length ps k r duplicateOld

/-- A warm hit in a nonempty raw cache does no expansion, insertion or candidate check. -/
theorem warm_hit_has_no_search_work :
    cachedFailure.2.expansions = 0 ∧ cachedFailure.2.insertionScans = 0 ∧
      cachedFailure.2.candidates = 0 ∧ cachedFailure.2.calls = 1 ∧
      cachedFailure.2.hits = 1 := by
  decide +kernel

/-- The two old entries contribute K0*E = 2; triangle E alone would give zero. -/
theorem duplicate_cache_needs_initial_scan_term :
    (memoStat [] 0 zeroRow duplicateOld).2.insertionScans =
      duplicateOld.length * (memoStat [] 0 zeroRow duplicateOld).2.expansions +
        triangle (memoStat [] 0 zeroRow duplicateOld).2.expansions ∧
    (memoStat [] 0 zeroRow duplicateOld).2.insertionScans ≠
      triangle (memoStat [] 0 zeroRow duplicateOld).2.expansions := by
  decide +kernel

/-- Counting a rejected candidate need not create a recursive call. -/
theorem rejected_guard_call_bound_is_strict :
    guardFailure.2.calls < 1 + guardFailure.2.candidates := by
  decide +kernel

/-- Three cold insertions scan 0+1+2 old entries; only two candidates are visited. -/
theorem backtrack_scan_accounting :
    backtrack.2.insertionScans = 3 ∧
      backtrack.2.insertionScans = triangle backtrack.2.expansions ∧
      backtrack.2.candidates = 2 ∧
      backtrack.2.candidates < [zeroRow, oneRow, twoRow].length := by
  decide +kernel

end UAVProof.TreeBudgetSearchStatsBoundsExamples

#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.zero_steps_success_grows
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.zero_steps_failure_grows
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.positive_depth_empty_candidates
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.rejected_guard_does_not_recurse
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.unrelated_duplicates_are_retained
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.cached_failure_is_not_a_miss
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.cached_empty_success_is_not_a_miss
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.repeated_zero_candidate_reuses_failure
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.child_failure_then_success_stops_scan
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.arbitrary_execution_from_duplicates
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.warm_hit_has_no_search_work
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.duplicate_cache_needs_initial_scan_term
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.rejected_guard_call_bound_is_strict
#print axioms UAVProof.TreeBudgetSearchStatsBoundsExamples.backtrack_scan_accounting
