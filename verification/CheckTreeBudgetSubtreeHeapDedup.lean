import LeanCompletion.UAV.TreeBudgetSubtreeHeapDedup

namespace UAVProof.TreeBudgetSubtreeHeapDedup.Check
open TreeBudgetAllocationBounds TreeBudgetSearchStore

-- Equal key contents live at distinct addresses. Each entry also has its own
-- payload pointer. The output must share the right-hand entry at the collision.
private def collision : Bool := Id.run do
  let z : Heap := #[.bit false]
  let kl := allocateBlob z [false]
  let kr := allocateBlob kl.2 [false]
  let kb := allocateBlob kr.2 [true]
  let left := push kb.2 kl.1 kl.1
  let right := push left.2 kr.1 kb.1
  let other := push right.2 kb.1 kb.1
  let tail := push other.2 other.1 0
  let middle := push tail.2 right.1 tail.1
  let input := push middle.2 left.1 middle.1
  let out := dedup input.2 0 input.1 3
  let second := refAt out.heap (out.head+2)
  return kl.1 != kr.1 && out.heap.size == input.2.size+33 &&
    out.length == 2 && out.comparisons == 2 && out.keyMapCells == 3 && out.stack == 0 &&
    refAt out.heap (out.head+1) == right.1 && refAt out.heap (second+1) == other.1 &&
    refAt out.heap (second+2) == 0 && readBlob out.heap (refAt out.heap (right.1+2)) == some [true]

#guard collision
#guard (dedup #[.bit false] 0 0 0).heap.size == 1
#print axioms mapKeys_spec
#print axioms member_spec
#print axioms run_spec
#print axioms dedup_correct
#print axioms entry_key
#print axioms entry_persist

end UAVProof.TreeBudgetSubtreeHeapDedup.Check
