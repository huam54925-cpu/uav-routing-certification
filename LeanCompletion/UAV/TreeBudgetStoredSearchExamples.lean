import LeanCompletion.UAV.TreeBudgetStoredSearch

/-! Executable regressions. The encoders and observers in this file are test
fixtures, not the input/output implementation promised by package D. -/
namespace UAVProof.TreeBudgetStoredSearchExamples
open TreeBudgetAllocationBounds TreeBudgetTypedStore TreeBudgetSearchStore
open TreeBudgetSharedAnswerStore TreeBudgetChargedCache TreeBudgetStoredSearch
open TreeBudgetBinaryCodec TreeBudgetVectorMemoState TreeBudgetVectorSearchStats

def putRows : Heap → Matrix → ℕ × Heap
  | heap, [] => emptyRows heap
  | heap, row :: rows =>
    let tail := putRows heap rows
    let head := allocateBlob tail.2 (encodeNats row)
    prependRows head.2 head.1 tail.1

def putAnswer (heap : Heap) : WireAnswer → ℕ × Heap
  | none => failure heap
  | some rows => let out := putRows heap rows; success out.2 out.1

def putCache : Heap → WireCache → ℕ × Heap
  | heap, [] => TreeBudgetSearchStore.emptyCache heap
  | heap, (key, answer) :: cs =>
    let tail := putCache heap cs
    let k := allocateBlob tail.2 (encodeKey key)
    let v := putAnswer k.2 answer
    prependCache v.2 k.1 v.1 tail.1

def getRows : ℕ → Heap → ℕ → Option Matrix
  | 0, _, _ => none
  | fuel + 1, heap, a => do
    let head ← (rowsHead heap a).value
    match head with
    | none => some []
    | some (row, tail) =>
      let bits ← readBlob heap row
      let (p, rest) ← parseNats bits
      if rest = [] then return p :: (← getRows fuel heap tail) else none

def getAnswer (heap : Heap) (a : ℕ) : Option WireAnswer := do
  let head ← (answerHead heap a).value
  match head with
  | none => some none
  | some rows => (getRows (heap.size + 1) heap rows).map some

def getCache : ℕ → Heap → ℕ → Option WireCache
  | 0, _, _ => none
  | fuel + 1, heap, a => do
    let head ← (headRead heap a).value
    match head with
    | none => some []
    | some (key, answer, tail) =>
      let q ← readKey heap key
      let ans ← getAnswer heap answer
      return (q, ans) :: (← getCache fuel heap tail)

def check {n : ℕ} (ps : List (Vector ℕ n)) (k : ℕ) (r : Vector ℕ n) (cs : CacheV n) : Bool :=
  let candidates := putRows #[.bit false] (ps.map Vector.toList)
  let residual := allocateBlob candidates.2 (encodeNats r.toList)
  let cache := putCache residual.2 (wireCache cs)
  let actual := (memoD n candidates.1 k cache.2 residual.1 cache.1 0).value
  let expected := memoStatV ps k r cs
  match actual with
  | none => false
  | some out => decide (getAnswer out.heap out.answer = some (wireAnswer expected.1.1) ∧
      getCache (out.heap.size + 1) out.heap out.cache = some (wireCache expected.1.2) ∧
      out.events = expected.2)

-- Successful empty matrix, failure at zero depth, and immediate success.
#guard check [] 0 (#v[0] : Vector ℕ 1) []
#guard check [] 0 (#v[1] : Vector ℕ 1) []
#guard check [#v[1]] 1 (#v[1] : Vector ℕ 1) []
-- Duplicate conflicting keys: the first cached failure is a hit.
#guard check [#v[1]] 1 (#v[1] : Vector ℕ 1)
  [((1, #v[1]), none), ((1, #v[1]), some [#v[1]])]
-- Cached successful empty answer is distinct from cached failure.
#guard check [] 3 (#v[7] : Vector ℕ 1) [((3, #v[7]), some [])]
-- First child fails; its inserted cache must feed the next candidate.
#guard check [#v[0], #v[1], #v[2]] 1 (#v[1] : Vector ℕ 1) []
-- Rejected guard, early success, and repeated candidates.
#guard check [#v[2], #v[1], #v[1]] 2 (#v[2] : Vector ℕ 1) []

def replacementTest : Bool :=
  let q : WireKey := (1, [2])
  let other : WireKey := (2, [1])
  let cs : WireCache := [(other, none), (q, some []), (other, some [[1]]), (q, none)]
  let cache := putCache #[.bit false] cs
  let key := allocateBlob cache.2 (encodeKey q)
  let answer := putAnswer key.2 (some [[2]])
  match (insertD answer.2 cache.1 key.1 answer.1).value with
  | none => false
  | some ((root, heap), count) => decide
      (getCache (heap.size + 1) heap root = some ((q, some [[2]]) :: keep cs q) ∧
       count = cs.length ∧ heap.size = answer.2.size + 12)

#guard replacementTest

def boundaryTest (size : ℕ) : Bool :=
  let heap : Heap := (List.replicate size (.bit false)).toArray
  let out := alloc heap [.bit true, .ref 0, .ref 0]
  decide (out.value.1 = size ∧ out.value.2.size = size + 3 ∧
    (load out.value.2 (size + 1)).value = some (.ref 0))

#guard boundaryTest 7
#guard boundaryTest 15
#guard boundaryTest 31

end UAVProof.TreeBudgetStoredSearchExamples
