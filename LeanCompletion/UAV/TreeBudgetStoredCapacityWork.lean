import LeanCompletion.UAV.TreeBudgetStoredInputBounds
import LeanCompletion.UAV.TreeBudgetStoredWorkInvariant
import LeanCompletion.UAV.TreeBudgetStoredSearchWork

/-! Capacity is proved from allocations before it is used to bound the address
width or time. All hypotheses of the generic search cost theorem are discharged
by the decoded input; no guessed capacity or total-cost bound is assumed. -/
namespace UAVProof.TreeBudgetStoredCapacityWork
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedParsing
open TreeBudgetAllocationBounds TreeBudgetTypedStore TreeBudgetSearchStore
open TreeBudgetSharedAnswerStore TreeBudgetChargedCache TreeBudgetStoredSearch
open TreeBudgetStoredAllocation TreeBudgetStoredHeapGrowth TreeBudgetStoredPreparation
open TreeBudgetStoredExecution TreeBudgetVectorMemoState TreeBudgetSearchStats
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetBinaryPipeline
open TreeBudgetCostedSearchBounds TreeBudgetVectorSearchStats TreeBudgetCostedSearch
open TreeBudgetBinaryPreprocessing TreeBudgetCostedCandidates TreeBudgetParentArray
open TreeBudgetVectorCandidates TreeBudgetVectorMemoIntegration TreeBudgetVector TreeBudgetVectorChecker
open TreeBudgetBinarySearchInputBounds TreeBudgetBinaryTotalWork TreeBudgetMemoBounds
open TreeBudgetStoredInputBounds TreeBudgetStoredWorkInvariant TreeBudgetStoredSearchWork

def inputObjects (I : RawInput) (J : Input) : ℕ := objectBudget J.n (2 * (encodeInput I).length)
noncomputable def inputCapacity (I : RawInput) (J : Input) : ℕ := 4096 * (states J) ^ 3 * ((encodeInput I).length + 1) ^ 2
noncomputable def inputWidth (I : RawInput) (J : Input) : ℕ := (8 * (inputCapacity I J + inputObjects I J + 1)).size

set_option maxHeartbeats 1000000 in
theorem input_payload (I : RawInput) (J : Input) (hj : decodeRaw I = some J) :
    PayloadBounds (prepareInput J).value.depth (prepareInput J).value.residual (inputObjects I J) := by
  obtain ⟨hn, hk, hH⟩ := prepared_widths I J hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [inputObjects, objectBudget]
    have h : 0 < 16 * (J.n + 1) * (2 * (encodeInput I).length + 1) := by positivity
    exact h
  · dsimp [inputObjects, objectBudget]; nlinarith only [Nat.zero_le (J.n * (encodeInput I).length)]
  · dsimp [inputObjects, objectBudget]; nlinarith only [hk, Nat.zero_le (J.n * (encodeInput I).length)]
  · intro i
    have hi := hH i
    simp only [Fin.getElem_fin] at hi ⊢
    dsimp [inputObjects, objectBudget]
    nlinarith only [hi, Nat.zero_le (J.n * (encodeInput I).length)]
  · intro v hs
    exact rowSlots_bound v _ (fun i => (Nat.size_le_size (hs i)).trans (hH i))
  · intro k v hk' hs
    exact keySlots_bound k v _ ((Nat.size_le_size hk').trans hk)
      (fun i => (Nat.size_le_size (hs i)).trans (hH i))

theorem input_objects_bound (I : RawInput) (J : Input) (hj : decodeRaw I = some J) :
    inputObjects I J ≤ 32 * ((encodeInput I).length + 1) ^ 2 := by
  have hn := (prepared_widths I J hj).1
  have hm := Nat.mul_le_mul_right (2 * (encodeInput I).length + 1) (Nat.add_le_add_right hn 1)
  dsimp [inputObjects, objectBudget]
  nlinarith only [hm]

theorem input_envelope (I : RawInput) (J : Input) (hj : decodeRaw I = some J) :
    (initializeStore (prepareInput J).value).value.heap.size +
      (inputObjects I J + 20) * eventWeight (preparedSearch J).events ≤ inputCapacity I J := by
  have hi := initial_heap_bound J (inputObjects I J) (input_payload I J hj).rows
  have hw := prepared_events J
  have hS := states_positive J
  have hcube : states J ≤ (states J) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hS (show 1 ≤ 3 by omega)
  have h1 : 1 ≤ (states J) ^ 3 := hS.trans hcube
  have hB := input_objects_bound I J hj
  have hL : 1 ≤ ((encodeInput I).length + 1) ^ 2 := one_le_pow₀ (by omega)
  have h₁ := Nat.mul_le_mul_left (inputObjects I J + 3) hcube
  have h₂ := Nat.mul_le_mul_left (inputObjects I J + 3) h1
  have h₃ := Nat.mul_le_mul_left (inputObjects I J + 20) hw
  have h₄ := Nat.mul_le_mul_right ((states J) ^ 3) hB
  have h₅ := Nat.mul_le_mul_left ((states J) ^ 3) hL
  dsimp [inputCapacity]
  nlinarith only [hi, h₁, h₂, h₃, h₄, h₅]

theorem input_width_positive (I : RawInput) (J : Input) : 1 ≤ inputWidth I J := by
  have h : 1 ≤ 8 * (inputCapacity I J + inputObjects I J + 1) := by omega
  exact Nat.size_le_size h

theorem input_width_bound (I : RawInput) (J : Input) (hj : decodeRaw I = some J) :
    inputWidth I J ≤ 11 * (encodeInput I).length + 24 := by
  have hS := TreeBudgetBitLength.size_stateBound_normalized_of_input I
    (decodeRaw_shape I J hj) (toRootedTree J.parents J.valid) J.H (decodeRaw_fields I J hj).2.2.1
  change (states J).size ≤ 3 * (encodeInput I).length + 1 at hS
  have hB := input_objects_bound I J hj
  have hS1 : 1 ≤ (states J) ^ 3 := one_le_pow₀ (states_positive J)
  have hL1 : 1 ≤ ((encodeInput I).length + 1) ^ 2 := one_le_pow₀ (by omega)
  have hSL := Nat.mul_le_mul_left (((encodeInput I).length + 1) ^ 2) hS1
  have hcap : 8 * (inputCapacity I J + inputObjects I J + 1) ≤
      65536 * (states J) ^ 3 * ((encodeInput I).length + 1) ^ 2 := by
    dsimp [inputCapacity]
    nlinarith only [hB, hSL, hL1]
  have hs := Nat.size_le_size hcap
  have h₁ := TreeBudgetBitLength.size_mul_le 65536 ((states J) ^ 3)
  have h₂ := TreeBudgetBitLength.size_mul_le (65536 * (states J) ^ 3) (((encodeInput I).length + 1) ^ 2)
  have h₃ := size_pow_le (states J) 3
  have h₄ := size_pow_le ((encodeInput I).length + 1) 2
  have h₅ := TreeBudgetAllocationBounds.size_le_self ((encodeInput I).length + 1)
  have hconstant : (65536 : ℕ).size = 17 := by decide +kernel
  rw [hconstant] at h₁
  exact (show inputWidth I J ≤ _ from hs).trans (by omega)

theorem input_rate_bound (I : RawInput) (J : Input) (hj : decodeRaw I = some J) :
    searchRate (inputObjects I J) (inputWidth I J) ≤ 2 ^ 40 * ((encodeInput I).length + 1) ^ 7 := by
  have hb := input_objects_bound I J hj
  have hw := input_width_bound I J hj
  have hL : 1 ≤ ((encodeInput I).length + 1) ^ 2 := one_le_pow₀ (by omega)
  have hb' : inputObjects I J + 1 ≤ 33 * ((encodeInput I).length + 1) ^ 2 := by omega
  have hw' : inputWidth I J + 2 ≤ 26 * ((encodeInput I).length + 1) := by omega
  have hm := Nat.mul_le_mul (Nat.pow_le_pow_left hb' 3) hw'
  have hr := Nat.mul_le_mul_left 1048576 hm
  dsimp [searchRate]
  nlinarith only [hr, Nat.zero_le (((encodeInput I).length + 1) ^ 7)]

end UAVProof.TreeBudgetStoredCapacityWork
