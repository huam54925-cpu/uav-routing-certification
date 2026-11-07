import LeanCompletion.UAV.TreeBudgetAddressedBlocks

/-! Kernel-evaluated boundary and sharing regressions for the addressed store. -/
namespace UAVProof.TreeBudgetAddressedBlocksExamples
open TreeBudgetAllocationBounds TreeBudgetTypedStore TreeBudgetAddressedBlocks
set_option maxRecDepth 4096

def heap7 : Heap := #[.bit true, .bit false, .bit true, .bit false,
  .bit true, .bit false, .bit true]

def heap18 : Heap := #[.bit true, .bit false, .bit true, .bit false,
  .bit true, .bit false, .bit true, .bit false, .bit true, .bit false,
  .bit true, .bit false, .bit true, .bit false, .bit true, .bit false,
  .bit true, .bit false]

def sharedRefs : Block × Heap := allocateRefs heap18 [7, 8, 15, 16, 7]

/-- The actual binary address increment carries from address 15 to 16. -/
theorem read_crosses_sixteen :
    (readBlockD 5 heap18 14 4).value =
      some [.bit true, .bit false, .bit true, .bit false] := by decide +kernel

/-- The new block starts at 7 and crosses 8; the old word is still readable. -/
theorem copy_crosses_eight_preserves_old :
    (match (copyBlockD 5 heap7 ⟨4, 3⟩).value with
    | none => false
    | some (fresh, after) =>
      decide (fresh.base = 7 ∧ fresh.length = 3 ∧ after.size = 10 ∧
        (readWordD 5 after fresh).value = some [true, false, true] ∧
        (readWordD 5 after ⟨0, 7⟩).value = some [true, false, true, false, true, false, true])) = true := by
  decide +kernel

/-- Both references to address 7 remain shared after copying the reference
array; payloads on both sides of 8 and 16 decode without changing their value. -/
theorem copy_preserves_shared_references :
    (match (copyBlockD 6 sharedRefs.2 sharedRefs.1).value with
    | none => false
    | some (fresh, after) =>
      decide ((readRefsD 6 after fresh).value = some [7, 8, 15, 16, 7] ∧
        (readRefsD 6 after sharedRefs.1).value = some [7, 8, 15, 16, 7])) = true := by
  decide +kernel

end UAVProof.TreeBudgetAddressedBlocksExamples

#print axioms UAVProof.TreeBudgetAddressedBlocksExamples.read_crosses_sixteen
#print axioms UAVProof.TreeBudgetAddressedBlocksExamples.copy_crosses_eight_preserves_old
#print axioms UAVProof.TreeBudgetAddressedBlocksExamples.copy_preserves_shared_references
