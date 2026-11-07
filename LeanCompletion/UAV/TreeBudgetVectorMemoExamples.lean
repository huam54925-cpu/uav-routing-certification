import LeanCompletion.UAV.TreeBudgetVectorMemoIntegration
import LeanCompletion.UAV.TreeBudgetVectorCandidatesExamples

/-! Kernel-checked control-flow regressions for the explicit vector executor.
The one-dimensional raw programs deliberately do not assert tree validity.
Complete ordered caches and all six counters make lost failure state, duplicate
elimination, altered short-circuiting and truncated-subtraction bugs observable. -/
namespace UAVProof.TreeBudgetVectorMemoExamples

open TreeBudgetVector TreeBudgetVectorMemoState TreeBudgetVectorMemoSearch
open TreeBudgetVectorSearchStats TreeBudgetVectorMemoIntegration
open TreeBudgetVectorCandidatesExamples TreeBudgetCertificate

/-- The first conflicting key wins; insertion deletes every old copy while
retaining the relative order of all unrelated entries. -/
theorem conflicting_keys_and_stable_insert :
    lookupV [((1, encode ![2]), none), ((0, encode ![1]), some []),
      ((1, encode ![2]), some [encode ![2]]), ((2, encode ![2]), none)]
      (1, encode ![2]) = some none ∧
    insertV [((1, encode ![2]), none), ((0, encode ![1]), some []),
      ((1, encode ![2]), some [encode ![2]]), ((2, encode ![2]), none)]
      (1, encode ![2]) (some []) =
      [((1, encode ![2]), some []), ((0, encode ![1]), some []),
       ((2, encode ![2]), none)] := by
  decide +kernel

/-- Miss, stored failure and stored empty success remain distinct; the layer
number is part of the key even when the residual is identical. -/
theorem three_lookup_outcomes :
    lookupV [((0, encode ![0]), some []), ((1, encode ![0]), none)]
      (2, encode ![0]) = none ∧
    lookupV [((0, encode ![0]), some []), ((1, encode ![0]), none)]
      (1, encode ![0]) = some none ∧
    lookupV [((0, encode ![0]), some []), ((1, encode ![0]), none)]
      (0, encode ![0]) = some (some []) := by
  decide +kernel

/-- Raw cached failure takes precedence over the zero-layer zero test. -/
theorem zero_layer_cache_precedes_zero_test :
    memoStatV [] 0 (encode ![0]) [((0, encode ![0]), none)] =
      ((none, [((0, encode ![0]), none)]),
       { calls := 1, hits := 1, lookupComparisons := 1 }) := by
  apply Prod.ext
  · apply Prod.ext <;> decide +kernel
  · decide +kernel

/-- A later stored empty success is still a hit. Lookup charges each visited
entry, including the matching one, and does not insert or expand. -/
theorem later_empty_success_hit :
    memoStatV [] 0 (encode ![1])
      [((1, encode ![1]), none), ((0, encode ![1]), some [])] =
      ((some [], [((1, encode ![1]), none), ((0, encode ![1]), some [])]),
       { calls := 1, hits := 1, lookupComparisons := 2 }) := by
  apply Prod.ext
  · apply Prod.ext <;> decide +kernel
  · decide +kernel

theorem empty_success_and_failed_base_case :
    memoRowsWithV [] 0 (encode ![0]) [] =
      (some [], [((0, encode ![0]), some [])]) ∧
    memoRowsWithV [] 0 (encode ![1]) [] =
      (none, [((0, encode ![1]), none)]) := by
  constructor <;> apply Prod.ext <;> decide +kernel

/-- The second duplicate hits the first candidate's cached failure. The exact
six-field count is (3,1,2,2,1,1), although the final answer is only `none`. -/
theorem duplicate_candidate_failure_hit :
    memoStatV [encode ![1], encode ![1]] 1 (encode ![2]) [] =
      ((none, [((1, encode ![2]), none), ((0, encode ![1]), none)]),
       { calls := 3, hits := 1, expansions := 2, candidates := 2,
         lookupComparisons := 1, insertionScans := 1 }) := by
  apply Prod.ext
  · apply Prod.ext <;> decide +kernel
  · decide +kernel

/-- Oversized rows are skipped before subtraction; no spurious zero child is
entered, and the parent is the only stored state. -/
theorem oversized_candidate_guard :
    memoStatV [encode ![2]] 1 (encode ![1]) [] =
      ((none, [((1, encode ![1]), none)]),
       { calls := 1, expansions := 1, candidates := 1 }) := by
  apply Prod.ext
  · apply Prod.ext <;> decide +kernel
  · decide +kernel

/-- Later success retains the earlier failed child's cache. Parent insertion
scans both children, including the retained failed state. -/
theorem failed_child_retained_before_success :
    memoStatV [encode ![1], encode ![2]] 1 (encode ![2]) [] =
      ((some [encode ![2]],
        [((1, encode ![2]), some [encode ![2]]),
         ((0, encode ![0]), some []), ((0, encode ![1]), none)]),
       { calls := 3, expansions := 3, candidates := 2,
         lookupComparisons := 1, insertionScans := 3 }) := by
  apply Prod.ext
  · apply Prod.ext <;> decide +kernel
  · decide +kernel

/-- Success stops before examining the remaining candidate. -/
theorem successful_candidate_short_circuits :
    memoStatV [encode ![2], encode ![1]] 1 (encode ![2]) [] =
      ((some [encode ![2]],
        [((1, encode ![2]), some [encode ![2]]), ((0, encode ![0]), some [])]),
       { calls := 2, expansions := 2, candidates := 1, insertionScans := 1 }) := by
  apply Prod.ext
  · apply Prod.ext <;> decide +kernel
  · decide +kernel

/-- Recursive children use the whole candidate table, allowing the same row
to be selected more than once. -/
theorem repeated_row_uses_full_candidate_table :
    memoStatV [encode ![1]] 2 (encode ![2]) [] =
      ((some [encode ![1], encode ![1]],
        [((2, encode ![2]), some [encode ![1], encode ![1]]),
         ((1, encode ![1]), some [encode ![1]]), ((0, encode ![0]), some [])]),
       { calls := 3, expansions := 3, candidates := 2, insertionScans := 3 }) := by
  apply Prod.ext
  · apply Prod.ext <;> decide +kernel
  · decide +kernel

/-- The real entry normalizes a nonfirst root before creating both candidates
and the initial residual. Signed fees and a negative budget are accepted. -/
theorem normalized_signed_initial_answer :
    (initialRowsV middleRootStar starBound (Vector.ofFn ![-2, 999, -2]) (-2) 2).1 =
      some [encode ![0, 0, 1], encode ![1, 0, 0]] ∧
    (initialRowsV middleRootStar starBound (Vector.ofFn ![-2, 999, -2]) (-3) 2).1 =
      none := by
  decide +kernel

/-- Formal initialization also normalizes every reachable stored key. The
oversized first candidate of the child is counted, but makes no recursive call. -/
theorem normalized_signed_initial_execution :
    initialRowsStatV middleRootStar starBound (Vector.ofFn ![-2, 999, -2]) (-2) 2 =
      ((some [encode ![0, 0, 1], encode ![1, 0, 0]],
        [((2, encode ![1, 0, 1]), some [encode ![0, 0, 1], encode ![1, 0, 0]]),
         ((1, encode ![1, 0, 0]), some [encode ![1, 0, 0]]),
         ((0, encode ![0, 0, 0]), some [])]),
       { calls := 3, expansions := 3, candidates := 3, insertionScans := 3 }) := by
  apply Prod.ext
  · apply Prod.ext <;> decide +kernel
  · decide +kernel

/-- Unreduced fractions preserve their signed boundary. Both nonroot rows are
needed, so admitting only the -3/4 row does not solve the full instance. -/
theorem unreduced_signed_initial_answer :
    (initialRowsVScaled middleRootStar starBound (Vector.ofFn ![-2, 999, -6])
      (encode ![4, 2, 8]) (-4) 8 2).1 =
        some [encode ![0, 0, 1], encode ![1, 0, 0]] ∧
    (initialRowsVScaled middleRootStar starBound (Vector.ofFn ![-2, 999, -6])
      (encode ![4, 2, 8]) (-6) 8 2).1 = none := by
  decide +kernel

/-- The exported certificate is checked against the original, unnormalized
input and rational costs, not merely its success flag. -/
theorem unreduced_signed_certificate_checked :
    (searchMemoVScaled middleRootStar starBound (Vector.ofFn ![-2, 999, -6])
      (encode ![4, 2, 8]) (-4) 8 2).map
        (checkCertificate middleRootStar ![1, 7, 1] 2 ![-1/2, 999/2, -3/4] (-1/2)) =
      some true := by
  decide +kernel

end UAVProof.TreeBudgetVectorMemoExamples

#print axioms UAVProof.TreeBudgetVectorMemoExamples.conflicting_keys_and_stable_insert
#print axioms UAVProof.TreeBudgetVectorMemoExamples.three_lookup_outcomes
#print axioms UAVProof.TreeBudgetVectorMemoExamples.zero_layer_cache_precedes_zero_test
#print axioms UAVProof.TreeBudgetVectorMemoExamples.later_empty_success_hit
#print axioms UAVProof.TreeBudgetVectorMemoExamples.empty_success_and_failed_base_case
#print axioms UAVProof.TreeBudgetVectorMemoExamples.duplicate_candidate_failure_hit
#print axioms UAVProof.TreeBudgetVectorMemoExamples.oversized_candidate_guard
#print axioms UAVProof.TreeBudgetVectorMemoExamples.failed_child_retained_before_success
#print axioms UAVProof.TreeBudgetVectorMemoExamples.successful_candidate_short_circuits
#print axioms UAVProof.TreeBudgetVectorMemoExamples.repeated_row_uses_full_candidate_table
#print axioms UAVProof.TreeBudgetVectorMemoExamples.normalized_signed_initial_answer
#print axioms UAVProof.TreeBudgetVectorMemoExamples.normalized_signed_initial_execution
#print axioms UAVProof.TreeBudgetVectorMemoExamples.unreduced_signed_initial_answer
#print axioms UAVProof.TreeBudgetVectorMemoExamples.unreduced_signed_certificate_checked
