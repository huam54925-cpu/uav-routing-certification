import LeanCompletion.UAV.TreeBudgetSubtreeHeapDedupWork

namespace UAVProof.TreeBudgetSubtreeHeapDedup.Work.Check
open TreeBudgetAllocationBounds TreeBudgetSearchStore

private def sample (bits : List Bool) (last : Bool) := Id.run do
  let key₁ := allocateBlob #[.bit false] bits
  let key₂ := allocateBlob key₁.2 (bits ++ (if last then [true] else []))
  let e₁ := push key₂.2 key₁.1 0
  let e₂ := push e₁.2 key₂.1 e₁.1
  let tail := push e₂.2 e₂.1 0
  let xs := push tail.2 e₁.1 tail.1
  let r := dedupD xs.2 0 xs.1 2
  let growth := r.value.heap.size - xs.2.size
  return (r, growth, refAt r.value.heap (r.value.head+1) == e₂.1)

#guard (Id.run do
  let (short, growth, right) := sample [false] false
  let (long, growthLong, rightLong) := sample (List.replicate 12 false) false
  let (miss, growthMiss, _) := sample [false] true
  return right && rightLong && growth == 15 && growthLong == 15 && growthMiss == 18 &&
    short.work.persistentSlots == growth && long.work.persistentSlots == growthLong &&
    miss.work.persistentSlots == growthMiss && short.value.comparisons == 1 &&
    long.value.comparisons == 1 && long.work.keySteps > short.work.keySteps &&
    long.work.temporaryCells > short.work.temporaryCells &&
    short.work.refSteps > 0 && short.work.nodeSteps > 0)

#print axioms execute_value
#print axioms dedupD_value
#print axioms keyMap_slots
#print axioms scan_slots
#print axioms execute_slots
#print axioms charged_slots_eq_growth

end UAVProof.TreeBudgetSubtreeHeapDedup.Work.Check
