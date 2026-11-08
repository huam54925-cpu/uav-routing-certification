import LeanCompletion.UAV.TreeBudgetStoredHeapGrowth
import LeanCompletion.UAV.TreeBudgetStoredExecution
import LeanCompletion.UAV.TreeBudgetBinaryTotalWork

/-! Heap allocation bounds derived from the real decoded input. The search
growth theorem concerns the new executor; only its logical event counts are
transferred from the old ordered-search semantics. -/
namespace UAVProof.TreeBudgetStoredInputBounds
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

def objectBudget (n β : ℕ) : ℕ := 16 * (n + 1) * (β + 1)

theorem rowSlots_bound {n : ℕ} (v : Vector ℕ n) (β : ℕ)
    (hv : ∀ i : Fin n, v[i].size ≤ β) : rowSlots v ≤ objectBudget n β := by
  have hm : ∀ x ∈ v.toList, x.size ≤ β := by
    intro x hx
    obtain ⟨i, hi, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    subst x
    exact hv ⟨i, hi⟩
  have h := encodeNats_length_bound v.toList n β (by simp) hm
  have hn := TreeBudgetAllocationBounds.size_le_self n
  dsimp [rowSlots, objectBudget]
  nlinarith

theorem keySlots_bound {n : ℕ} (k : ℕ) (v : Vector ℕ n) (β : ℕ)
    (hk : k.size ≤ β) (hv : ∀ i : Fin n, v[i].size ≤ β) :
    keySlots k v ≤ objectBudget n β := by
  have hm : ∀ x ∈ v.toList, x.size ≤ β := by
    intro x hx
    obtain ⟨i, hi, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    subst x
    exact hv ⟨i, hi⟩
  have h := encodeNats_length_bound v.toList n β (by simp) hm
  have hn := TreeBudgetAllocationBounds.size_le_self n
  simp only [keySlots, encodeKey, List.length_append, encodeNat_length, objectBudget]
  nlinarith

theorem prepared_values (J : Input) :
    (prepareInput J).value.residual = normalize (toRootedTree J.parents J.valid) J.H ∧
    (prepareInput J).value.candidates =
      candidatesV (toRootedTree J.parents J.valid) (normalize (toRootedTree J.parents J.valid) J.H)
        (scaleFees J.numerators J.denominators J.budgetDenominator)
        (scaleBudget J.denominators J.budgetNumerator J.budgetDenominator) ∧
    (prepareInput J).value.depth =
      TreeBudgetPatterns.rootCount (toRootedTree J.parents J.valid)
        (decode (normalize (toRootedTree J.parents J.valid) J.H)) := by
  simp [prepareInput, normalizeCost_value J.parents J.valid,
    candidateCost_value J.parents J.valid, rootCountCost_value J.parents J.valid,
    scaleFeesCost_value _ _ _ J.positive, scaleBudgetCost_value _ _ _ J.budgetPositive]

theorem prepared_events (J : Input) :
    eventWeight (preparedSearch J).events ≤ 56 * (states J) ^ 3 := by
  let R := toRootedTree J.parents J.valid
  let A := scaleFees J.numerators J.denominators J.budgetDenominator
  let AT := scaleBudget J.denominators J.budgetNumerator J.budgetDenominator
  have h := eventWeight_le_cube (initial_eventBoundsV_stateBound R J.H A AT
    (fun v => (A[v] : ℚ)) (AT : ℚ) 1 (by norm_num) (by simp) (by simp))
  have he := congrArg Prod.snd (preparedSearch_observe J)
  change (preparedSearch J).events = _ at he
  rw [decode_normalize] at he
  rw [← he] at h
  have hc := cube_add_one_le (states J) (states_positive J)
  change _ ≤ 7 * (states J + 1) ^ 3 at h
  omega

theorem prepared_candidate_bounds (J : Input) :
    (prepareInput J).value.candidates.length ≤ states J ∧
      ∀ p ∈ (prepareInput J).value.candidates, VecSmall (prepareInput J).value.residual p := by
  let R := toRootedTree J.parents J.valid
  let H := normalize R J.H
  let A := scaleFees J.numerators J.denominators J.budgetDenominator
  let AT := scaleBudget J.denominators J.budgetNumerator J.budgetDenominator
  have hm := map_decode_candidatesV R H A AT
    (fun v => (A[v] : ℚ)) (AT : ℚ) 1 (by norm_num) (by simp) (by simp)
  have hl := TreeBudgetCandidateCount.candidates_length_le_stateBound R (decode H)
    (fun v => (A[v] : ℚ)) (AT : ℚ)
  rw [← hm, List.length_map] at hl
  have hs := candidates_small R H A AT
    (fun v => (A[v] : ℚ)) (AT : ℚ) 1 (by norm_num) (by simp) (by simp)
  rw [(prepared_values J).2.1, (prepared_values J).1]
  exact ⟨by simpa only [states, H, decode_normalize, R] using hl, hs⟩

theorem prepared_widths (I : RawInput) (J : Input) (hj : decodeRaw I = some J) :
    J.n ≤ (encodeInput I).length ∧
    (prepareInput J).value.depth.size ≤ 2 * (encodeInput I).length ∧
    ∀ i : Fin J.n, (prepareInput J).value.residual[i].size ≤ 2 * (encodeInput I).length := by
  have hn : J.n ≤ (encodeInput I).length :=
    (decodeRaw_fields I J hj).1.trans_le (vertexCount_le_length I (decodeRaw_shape I J hj))
  have hH := normalize_width (toRootedTree J.parents J.valid) J.H _ (decoded_coordinate_width I J hj)
  have hk := rootCount_width (toRootedTree J.parents J.valid)
    (normalize (toRootedTree J.parents J.valid) J.H) _ hn hH
  rw [(prepared_values J).2.2, (prepared_values J).1]
  exact ⟨hn, hk, fun i => (hH i).trans (by omega)⟩

theorem initial_heap_bound (J : Input) (B : ℕ)
    (hrows : ∀ v, VecSmall (prepareInput J).value.residual v → rowSlots v ≤ B) :
    (initializeStore (prepareInput J).value).value.heap.size ≤
      3 + B + (B + 3) * states J := by
  rw [initializeStore_size]
  have hr := hrows _ (fun _ => le_rfl)
  have hc := prepared_candidate_bounds J
  have hs : ((prepareInput J).value.candidates.map fun p => rowSlots p + 3).sum ≤
      (B + 3) * (prepareInput J).value.candidates.length := by
    have h := List.sum_le_card_nsmul
      ((prepareInput J).value.candidates.map fun p => rowSlots p + 3) (B + 3) (by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact Nat.add_le_add_right (hrows p (hc.2 p hp)) 3)
    simpa [List.length_map, Nat.mul_comm] using h
  have hm := Nat.mul_le_mul_left (B + 3) hc.1
  omega

set_option maxHeartbeats 2000000 in
-- Combines the complete preparation and search allocation envelopes.
theorem executeInput_heap_bound (I : RawInput) (J : Input) (hj : decodeRaw I = some J)
    (result : StoredResult) (hv : (TreeBudgetStoredExecution.executeInput J).value = some result) :
    result.heap.size ≤ 4096 * (states J) ^ 3 * ((encodeInput I).length + 1) ^ 2 := by
  let P := (prepareInput J).value
  let initial := (initializeStore P).value
  let B := objectBudget J.n (2 * (encodeInput I).length)
  obtain ⟨hn, hk, hH⟩ := prepared_widths I J hj
  have hrows : ∀ v, VecSmall P.residual v → rowSlots v ≤ B := by
    intro v hs
    exact rowSlots_bound v _ (fun i => (Nat.size_le_size (hs i)).trans (hH i))
  have hkeys : ∀ k v, k ≤ P.depth → VecSmall P.residual v → keySlots k v ≤ B := by
    intro k v hk' hs
    exact keySlots_bound k v _ ((Nat.size_le_size hk').trans hk)
      (fun i => (Nat.size_le_size (hs i)).trans (hH i))
  obtain ⟨hh, hp, hr, hc, hf, hparent⟩ := initializeStore_correct P
  have hg := memoD_growth P.candidates initial.candidates P.depth P.residual P.depth B
    hrows hkeys initial.heap initial.residual initial.cache initial.parent P.residual []
    hh hp hr hc hparent (fun _ => le_rfl) le_rfl
  have he := congrArg Prod.snd (memoCost_observe (TreeBudgetBinarySearch.backend J.n)
    P.candidates P.depth P.residual [])
  change (memoCost _ _ _ _ _).events = _ at he
  rw [← he, ← (prepareInput_search J).2] at hg
  have hi := initial_heap_bound J B hrows
  have hw := prepared_events J
  have hS := states_positive J
  have hcube : states J ≤ (states J) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hS (show 1 ≤ 3 by omega)
  have h1 : 1 ≤ (states J) ^ 3 := hS.trans hcube
  have hB : B ≤ 32 * ((encodeInput I).length + 1) ^ 2 := by
    have hm := Nat.mul_le_mul_right (2 * (encodeInput I).length + 1)
      (Nat.add_le_add_right hn 1)
    dsimp [B, objectBudget]
    nlinarith only [hm]
  have hL : 1 ≤ ((encodeInput I).length + 1) ^ 2 := one_le_pow₀ (by omega)
  have envelope : initial.heap.size + (B + 20) * eventWeight (preparedSearch J).events ≤
      4096 * (states J) ^ 3 * ((encodeInput I).length + 1) ^ 2 := by
    have h₁ := Nat.mul_le_mul_left (B + 3) hcube
    have h₂ := Nat.mul_le_mul_left (B + 3) h1
    have h₃ := Nat.mul_le_mul_left (B + 20) hw
    have h₄ := Nat.mul_le_mul_right ((states J) ^ 3) hB
    have h₅ := Nat.mul_le_mul_left ((states J) ^ 3) hL
    change initial.heap.size ≤ _ at hi
    nlinarith only [hi, h₁, h₂, h₃, h₄, h₅]
  simp only [TreeBudgetStoredExecution.executeInput, costBind_value] at hv
  change (thenD (memoD J.n initial.candidates P.depth initial.heap initial.residual initial.cache initial.parent)
    _).value = some result at hv
  cases hs : (memoD J.n initial.candidates P.depth initial.heap
      initial.residual initial.cache initial.parent).value with
  | none => simp [hs] at hv
  | some searched =>
    have hsize := (hg searched hs).trans envelope
    simp only [thenD_value, hs, Option.bind_some] at hv
    cases ho : (TreeBudgetStoredOutput.emitStored searched.heap searched.answer).value with
    | none => simp [ho] at hv
    | some output =>
      simp only [ho, Option.bind_some, charge, ret, Option.some.injEq] at hv
      subst result
      exact hsize

theorem executeStored_heap_bound (bits : Bits) (I : RawInput) (J : Input)
    (hp : parseInput bits = some I) (hj : decodeRaw I = some J) :
    ∃ result, (executeStored bits).value = .accepted result ∧
      result.heap.size ≤ 4096 * (states J) ^ 3 * (bits.length + 1) ^ 2 := by
  obtain ⟨result, hv, hr⟩ := executeInput_correct J
  refine ⟨result, ?_, ?_⟩
  · simp [executeStored, hp, TreeBudgetStoredExecution.executeRaw,
      TreeBudgetStoredExecution.executeChecked, hj, hv]
  · rw [(parseInput_canonical bits I hp).1]
    exact executeInput_heap_bound I J hj result hv

theorem executeStored_address_width (bits : Bits) (I : RawInput) (J : Input)
    (hp : parseInput bits = some I) (hj : decodeRaw I = some J)
    (result : StoredResult) (ho : (executeStored bits).value = .accepted result)
    (earlier : Heap) (he : Extends earlier result.heap)
    (address : ℕ) (ha : address < earlier.size) : address.size ≤ 11 * bits.length + 20 := by
  obtain ⟨out, hout, hbound⟩ := executeStored_heap_bound bits I J hp hj
  have heq : out = result := by rw [ho] at hout; exact (Outcome.accepted.inj hout).symm
  subst out
  have hS := TreeBudgetBitLength.size_stateBound_normalized_of_input I
    (decodeRaw_shape I J hj) (toRootedTree J.parents J.valid) J.H (decodeRaw_fields I J hj).2.2.1
  rw [← (parseInput_canonical bits I hp).1] at hS
  change (states J).size ≤ 3 * bits.length + 1 at hS
  have h₁ := TreeBudgetBitLength.size_mul_le 4096 ((states J) ^ 3)
  have h₂ := TreeBudgetBitLength.size_mul_le (4096 * (states J) ^ 3) ((bits.length + 1) ^ 2)
  have h₃ := size_pow_le (states J) 3
  have h₄ := size_pow_le (bits.length + 1) 2
  have h₅ := TreeBudgetAllocationBounds.size_le_self (bits.length + 1)
  have hf := Nat.size_le_size ((ha.le.trans he.size_le).trans hbound)
  have hconstant : (4096 : ℕ).size = 13 := by decide +kernel
  rw [hconstant] at h₁
  omega

theorem executeStored_heap_mass (bits : Bits) (I : RawInput) (J : Input)
    (hp : parseInput bits = some I) (hj : decodeRaw I = some J) :
    ∃ result, (executeStored bits).value = .accepted result ∧
      result.heap.size ≤ 4096 * 2 ^ (3 * mass J) * (bits.length + 1) ^ 2 := by
  obtain ⟨out, ho, hb⟩ := executeStored_heap_bound bits I J hp hj
  refine ⟨out, ho, hb.trans ?_⟩
  have hS : states J ≤ 2 ^ mass J :=
    TreeBudgetStateParameters.stateBound_le_two_pow_totalMultiplicity _ _
  have h := Nat.mul_le_mul_right ((bits.length + 1) ^ 2)
    (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left hS 3))
  simpa only [← pow_mul, Nat.mul_comm (mass J) 3] using h

theorem executeStored_heap_support_maximum (bits : Bits) (I : RawInput) (J : Input)
    (hp : parseInput bits = some I) (hj : decodeRaw I = some J) :
    ∃ result, (executeStored bits).value = .accepted result ∧
      result.heap.size ≤ 4096 * (maximum J + 1) ^ (3 * support J) * (bits.length + 1) ^ 2 := by
  obtain ⟨out, ho, hb⟩ := executeStored_heap_bound bits I J hp hj
  refine ⟨out, ho, hb.trans ?_⟩
  have hS : states J ≤ (maximum J + 1) ^ support J :=
    TreeBudgetStateParameters.stateBound_le_maxMultiplicity_pow_positiveCount _ _
  have h := Nat.mul_le_mul_right ((bits.length + 1) ^ 2)
    (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left hS 3))
  simpa only [← pow_mul, Nat.mul_comm (support J) 3] using h

end UAVProof.TreeBudgetStoredInputBounds
