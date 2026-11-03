import LeanCompletion.UAV.TreeBudgetMemoState
import LeanCompletion.UAV.TreeBudgetStateSeparationExamples

/-! Kernel-checked regressions for the first cache package. Every semantic cache
below uses one fixed R,H,s,T. There is no memoized recursive search in this file. -/
namespace UAVProof.TreeBudgetMemoStateExamples
open TreeBudgetMemoState TreeBudgetResidualSearch TreeBudgetPatterns
open TreeBudgetStateSeparationExamples TreeBudgetCheckerExamples

def goodKey : Key 5 := (2, good)
def badKey : Key 5 := (2, bad)
def zeroKey : Key 5 := (0, 0)
def oneZeroKey : Key 5 := (1, 0)
def missingKey : Key 5 := (99, 0)

/-- Costs are respectively 5+5 and 3+3+4, both exactly 10. -/
def goodRows : Rows 5 := [![0, 1, 0, 0, 2], ![0, 1, 2, 1, 0]]

theorem good_answer_valid : AnswerValid hubTree H fees 10 goodKey (some goodRows) := by
  change ResidualWitness hubTree H fees 10 2 good goodRows
  refine ⟨rfl, ?_, ?_⟩
  · intro p hp
    simp only [goodRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> decide +kernel
  · decide +kernel

theorem bad_answer_valid : AnswerValid hubTree H fees 10 badKey none := bad_infeasible

theorem empty_answer_valid : AnswerValid hubTree H fees 10 zeroKey (some []) := by
  simp [AnswerValid, zeroKey, ResidualWitness]

theorem one_zero_answer_valid : AnswerValid hubTree H fees 10 oneZeroKey none := by
  change ¬ ResidualFeasible hubTree H fees 10 1 0
  rintro ⟨rows, hw⟩
  have hk := residualWitness_rootCount hubTree H fees 10 1 0 rows hw
  simp [rootCount] at hk

def separationCache : Cache 5 :=
  insert (insert emptyCache goodKey (some goodRows)) badKey none

theorem separation_cache_valid : CacheValid hubTree H fees 10 separationCache := by
  apply cacheValid_insert
  · exact cacheValid_insert hubTree H fees 10 emptyCache goodKey (some goodRows)
      (cacheValid_empty hubTree H fees 10) good_answer_valid
  · exact bad_answer_valid

def testCache : Cache 5 :=
  insert (insert separationCache zeroKey (some [])) oneZeroKey none

theorem test_cache_valid : CacheValid hubTree H fees 10 testCache := by
  apply cacheValid_insert
  · exact cacheValid_insert hubTree H fees 10 separationCache zeroKey (some [])
      separation_cache_valid empty_answer_valid
  · exact one_zero_answer_valid

theorem test_cache_nodup : KeysNodup testCache := by
  unfold testCache separationCache
  apply keysNodup_insert
  apply keysNodup_insert
  apply keysNodup_insert
  exact keysNodup_insert emptyCache goodKey (some goodRows) keysNodup_empty

/-- Outer none, cached failure, empty success and nonempty success are distinct. -/
theorem four_lookup_outcomes :
    lookup testCache missingKey = none ∧
    lookup testCache badKey = some none ∧
    lookup testCache zeroKey = some (some []) ∧
    lookup testCache goodKey = some (some goodRows) := by decide +kernel

theorem same_residual_different_steps :
    zeroKey.2 = oneZeroKey.2 ∧ zeroKey ≠ oneZeroKey ∧
    lookup testCache zeroKey = some (some []) ∧
    lookup testCache oneZeroKey = some none := by decide +kernel

/-- Equality of the old summary does not merge either full key or its answer. -/
theorem equal_summary_separate_entries :
    summary 2 good = summary 2 bad ∧ goodKey ≠ badKey ∧
    lookup testCache goodKey = some (some goodRows) ∧
    lookup testCache badKey = some none := by
  exact ⟨same_summary, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem empty_cache_misses : lookup (emptyCache : Cache 5) zeroKey = none := rfl

theorem reversed_answer_valid :
    AnswerValid hubTree H fees 10 goodKey (some goodRows.reverse) := by
  change ResidualWitness hubTree H fees 10 2 good goodRows.reverse
  refine ⟨rfl, ?_, ?_⟩
  · intro p hp
    have hp' : p ∈ goodRows := List.mem_reverse.mp hp
    exact good_answer_valid.2.1 p hp'
  · decide +kernel

def replacedCache : Cache 5 := insert testCache goodKey (some goodRows.reverse)

theorem replacement_valid : CacheValid hubTree H fees 10 replacedCache :=
  cacheValid_insert hubTree H fees 10 testCache goodKey (some goodRows.reverse)
    test_cache_valid reversed_answer_valid

theorem replacement_updates_only_one_key :
    lookup replacedCache goodKey = some (some goodRows.reverse) ∧
    lookup replacedCache badKey = lookup testCache badKey ∧
    lookup replacedCache zeroKey = lookup testCache zeroKey ∧
    lookup replacedCache oneZeroKey = lookup testCache oneZeroKey ∧
    lookup replacedCache missingKey = lookup testCache missingKey ∧
    replacedCache.length = testCache.length := by decide +kernel

/-- Even a raw cache with two stale copies of this key is replaced completely.
The old raw cache is deliberately not claimed to satisfy CacheValid. -/
theorem duplicate_key_cleanup :
    insert [(goodKey, none), (badKey, none), (goodKey, some [])]
      goodKey (some goodRows) = [(goodKey, some goodRows), (badKey, none)] := by
  decide +kernel

theorem repeated_replacement_bounded :
    (insert (insert (insert emptyCache goodKey none) goodKey (some []))
      goodKey (some goodRows)).length = 1 := by decide +kernel

/-- Raw storage permits wrong data, but the semantic invariant rejects it. -/
theorem false_failure_not_valid :
    ¬ CacheValid hubTree H fees 10 (insert emptyCache goodKey none) := by
  intro hc
  have ha := hc goodKey none (lookup_insert_same ..)
  exact ha good_feasible

theorem false_empty_success_not_valid :
    ¬ CacheValid hubTree H fees 10 (insert emptyCache badKey (some [])) := by
  intro hc
  have ha := hc badKey (some []) (lookup_insert_same ..)
  exact bad_infeasible ⟨[], ha⟩

end UAVProof.TreeBudgetMemoStateExamples

#print axioms UAVProof.TreeBudgetMemoStateExamples.good_answer_valid
#print axioms UAVProof.TreeBudgetMemoStateExamples.bad_answer_valid
#print axioms UAVProof.TreeBudgetMemoStateExamples.empty_answer_valid
#print axioms UAVProof.TreeBudgetMemoStateExamples.one_zero_answer_valid
#print axioms UAVProof.TreeBudgetMemoStateExamples.separation_cache_valid
#print axioms UAVProof.TreeBudgetMemoStateExamples.test_cache_valid
#print axioms UAVProof.TreeBudgetMemoStateExamples.test_cache_nodup
#print axioms UAVProof.TreeBudgetMemoStateExamples.four_lookup_outcomes
#print axioms UAVProof.TreeBudgetMemoStateExamples.same_residual_different_steps
#print axioms UAVProof.TreeBudgetMemoStateExamples.equal_summary_separate_entries
#print axioms UAVProof.TreeBudgetMemoStateExamples.empty_cache_misses
#print axioms UAVProof.TreeBudgetMemoStateExamples.reversed_answer_valid
#print axioms UAVProof.TreeBudgetMemoStateExamples.replacement_valid
#print axioms UAVProof.TreeBudgetMemoStateExamples.replacement_updates_only_one_key
#print axioms UAVProof.TreeBudgetMemoStateExamples.duplicate_key_cleanup
#print axioms UAVProof.TreeBudgetMemoStateExamples.repeated_replacement_bounded
#print axioms UAVProof.TreeBudgetMemoStateExamples.false_failure_not_valid
#print axioms UAVProof.TreeBudgetMemoStateExamples.false_empty_success_not_valid
