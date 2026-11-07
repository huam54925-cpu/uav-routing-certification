import LeanCompletion.UAV.TreeBudgetVectorMemoState

/-! An executable vector search without instrumentation. Each recursive child
uses the complete candidate list, while failed scans advance only their local
suffix and thread the child's updated cache. -/
namespace UAVProof.TreeBudgetVectorMemoSearch
open TreeBudgetVector TreeBudgetVectorMemoState
variable {n : ℕ}

def scanCandidatesV (solve : Vector ℕ n → CacheV n → AnswerV n × CacheV n)
    (r : Vector ℕ n) : List (Vector ℕ n) → CacheV n → AnswerV n × CacheV n
  | [], cache => (none, cache)
  | p :: ps, cache =>
    if leB p r then
      let out := solve (sub r p) cache
      match out.1 with
      | some rows => (some (p :: rows), out.2)
      | none => scanCandidatesV solve r ps out.2
    else scanCandidatesV solve r ps cache

def memoRowsWithV (ps : List (Vector ℕ n)) :
    ℕ → Vector ℕ n → CacheV n → AnswerV n × CacheV n
  | 0, r, cache =>
    match lookupV cache (0, r) with
    | some answer => (answer, cache)
    | none =>
      let answer := if isZero r then some [] else none
      (answer, insertV cache (0, r) answer)
  | k + 1, r, cache =>
    match lookupV cache (k + 1, r) with
    | some answer => (answer, cache)
    | none =>
      let out := scanCandidatesV (memoRowsWithV ps k) r ps cache
      (out.1, insertV out.2 (k + 1, r) out.1)

end UAVProof.TreeBudgetVectorMemoSearch
