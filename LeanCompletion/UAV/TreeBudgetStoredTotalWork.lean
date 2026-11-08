import LeanCompletion.UAV.TreeBudgetStoredMemoWork
import LeanCompletion.UAV.TreeBudgetStoredPreparationWork
import LeanCompletion.UAV.TreeBudgetStoredOutputWork
import LeanCompletion.UAV.TreeBudgetStoredCapacityWork
import LeanCompletion.UAV.TreeBudgetStoredRejectionBounds

/-! Total recorded work of the actual addressed executor. The proof includes
auxiliary allocation costs, binary loop cursors, preparation, search, output and
rejected inputs. The capacity and address widths are conclusions derived from
input size, not assumptions of the exported total-time theorem. -/
namespace UAVProof.TreeBudgetStoredTotalWork
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedParsing TreeBudgetCostedInput
open TreeBudgetAllocationBounds TreeBudgetTypedStore TreeBudgetSearchStore
open TreeBudgetSharedAnswerStore TreeBudgetChargedCache TreeBudgetStoredSearch
open TreeBudgetStoredAllocation TreeBudgetStoredHeapGrowth TreeBudgetStoredPreparation TreeBudgetStoredOutput
open TreeBudgetStoredExecution TreeBudgetVectorMemoState TreeBudgetSearchStats
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetBinaryPipeline
open TreeBudgetCostedSearchBounds TreeBudgetVectorSearchStats TreeBudgetCostedSearch
open TreeBudgetBinaryPreprocessing TreeBudgetCostedCandidates TreeBudgetParentArray
open TreeBudgetBinaryTotalWork TreeBudgetMemoBounds TreeBudgetBinaryOutputBounds
open TreeBudgetStoredInputBounds TreeBudgetStoredWorkInvariant TreeBudgetStoredSearchWork
open TreeBudgetStoredWork TreeBudgetStoredMemoWork TreeBudgetStoredPreparationWork
open TreeBudgetStoredOutputWork TreeBudgetStoredCapacityWork

set_option maxHeartbeats 1000000 in
theorem prepared_output_work (I : RawInput) (J : Input) (hj : decodeRaw I = some J)
    (heap : Heap) (a : ℕ) (hh : WellFormed heap)
    (ha : SharedAnswerRep heap a (wireAnswer (preparedSearch J).value.1))
    (hsize : heap.size ≤ inputCapacity I J) :
    work (emitStored heap a) ≤ 65536 * (inputObjects I J + 1) ^ 3 * (inputWidth I J + 2) *
      (states J + 1) ^ 2 := by
  have hb := input_payload I J hj
  apply emitStored_work heap a (wireAnswer (preparedSearch J).value.1) (states J)
    (inputObjects I J) (inputWidth I J) hh ha
  · intro rows ho
    cases hv : (preparedSearch J).value.1 with
    | none => simp [wireAnswer, hv] at ho
    | some vs =>
      simp only [wireAnswer, hv, Option.map_some, Option.some.injEq] at ho
      subst rows
      have hl := preparedSearch_rows_length J vs hv
      simpa only [List.length_map] using (show vs.length ≤ states J by exact Nat.le_of_lt hl)
  · intro rows ho row hrow
    cases hv : (preparedSearch J).value.1 with
    | none => simp [wireAnswer, hv] at ho
    | some vs =>
      simp only [wireAnswer, hv, Option.map_some, Option.some.injEq] at ho
      subst rows
      obtain ⟨v, hvMem, rfl⟩ := List.mem_map.mp hrow
      have hbound := (preparedSearch_rows_bounds J vs hv).2 v hvMem
      have hvWidth : ∀ i : Fin J.n, v[i].size ≤ (encodeInput I).length := fun i =>
        (Nat.size_le_size (hbound i)).trans
          (TreeBudgetBinaryPipelineBounds.coordinate_width I J.H (decodeRaw_fields I J hj).2.2.1 i)
      have hslots := rowSlots_bound v (2 * (encodeInput I).length) (fun i => (hvWidth i).trans (by omega))
      have hβ : (encodeInput I).length ≤ inputObjects I J := by
        dsimp [inputObjects, objectBudget]
        nlinarith only [Nat.zero_le (J.n * (encodeInput I).length)]
      refine ⟨?_, by simpa using hb.dimension, ?_⟩
      · dsimp [rowSlots] at hslots
        change 2 * (encodeNats v.toList).length + 1 ≤ inputObjects I J at hslots
        omega
      · intro x hx
        obtain ⟨i, hi, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
        subst x
        exact (hvWidth ⟨i, hi⟩).trans hβ
  · exact input_width_positive I J
  · exact width_in_capacity _ _ _ _ le_rfl (by omega)

theorem total_work_envelope (ell S Q prep init search output : ℕ) (hS : 1 ≤ S)
    (hQ : Q ≤ 2 ^ 40 * (ell + 1) ^ 7)
    (hp : prep ≤ 1000000 * (ell + 1) ^ 4 * S ^ 3)
    (hi : init ≤ Q * (S + 2)) (hs : search ≤ Q * (56 * S ^ 3))
    (ho : output ≤ Q * (S + 1) ^ 2) :
    prep + init + search + output + 10 ≤ 2 ^ 48 * S ^ 3 * (ell + 1) ^ 7 := by
  have hSle : S ≤ S ^ 3 := by simpa only [pow_one] using Nat.pow_le_pow_right hS (show 1 ≤ 3 by omega)
  have hS1 : 1 ≤ S ^ 3 := one_le_pow₀ hS
  have hS2 : (S + 1) ^ 2 ≤ 4 * S ^ 3 := by
    have h2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by omega)
    nlinarith only [h2, hSle, hS1]
  have hinit := Nat.mul_le_mul_left Q (show S + 2 ≤ 3 * S ^ 3 by omega)
  have hout := Nat.mul_le_mul_left Q hS2
  have hrate := Nat.mul_le_mul_right (63 * S ^ 3) hQ
  have hdegree : (ell + 1) ^ 4 ≤ (ell + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hprep := Nat.mul_le_mul_right (S ^ 3) hdegree
  have hL : 1 ≤ (ell + 1) ^ 7 := one_le_pow₀ (by omega)
  have hpos := Nat.mul_le_mul hS1 hL
  nlinarith only [hp, hi, hs, ho, hinit, hout, hrate, hprep, hpos]

set_option maxHeartbeats 2000000 in
theorem executeInput_work (I : RawInput) (J : Input) (hj : decodeRaw I = some J) :
    work (TreeBudgetStoredExecution.executeInput J) ≤
      2 ^ 48 * (states J) ^ 3 * ((encodeInput I).length + 1) ^ 7 := by
  let P := (prepareInput J).value
  let initial := (initializeStore P).value
  let B := inputObjects I J
  let N := inputCapacity I J
  let W := inputWidth I J
  have hb := input_payload I J hj
  have hw := input_width_positive I J
  have henvelope := input_envelope I J hj
  have hcan := prepared_candidate_bounds J
  obtain ⟨hh, hp, hr, hc, hf, hparent⟩ := initializeStore_correct P
  have he := congrArg Prod.snd (memoCost_observe (TreeBudgetBinarySearch.backend J.n)
    P.candidates P.depth P.residual [])
  change (memoCost _ _ _ _ _).events = _ at he
  have hcap : initial.heap.size + (B + 20) * eventWeight (memoStatV P.candidates P.depth P.residual []).2 ≤ N := by
    rw [← he, ← (prepareInput_search J).2]
    exact henvelope
  have hs := memoD_work P.candidates initial.candidates P.depth P.residual P.depth B N W hb hw
    le_rfl hcan.2 initial.heap initial.residual initial.cache initial.parent P.residual []
    hh hp hr hc hparent (fun _ => le_rfl) le_rfl (by intro e he; simp at he) hcap
  rw [← he, ← (prepareInput_search J).2] at hs
  have hg := memoD_growth P.candidates initial.candidates P.depth P.residual P.depth B hb.rows hb.keys
    initial.heap initial.residual initial.cache initial.parent P.residual [] hh hp hr hc hparent
    (fun _ => le_rfl) le_rfl
  rw [← he, ← (prepareInput_search J).2] at hg
  have hspec := memoD_refines_cost (TreeBudgetBinarySearch.backend J.n) P.candidates initial.candidates P.depth
    initial.heap initial.residual initial.cache initial.parent P.residual [] hh hp hr hc hparent
  rw [← (prepareInput_search J).1, ← (prepareInput_search J).2] at hspec
  obtain ⟨out, hout, ha, hcache, hwout, hext, hevents⟩ := hspec
  have hsize := (hg out hout).trans henvelope
  have ho := prepared_output_work I J hj out.heap out.answer hwout ha hsize
  have hi := initializeStore_work P P.depth B N W hb hcan.2 le_rfl (by
    change initial.heap.size ≤ N
    exact (Nat.le_add_right _ _).trans hcap)
  have hprep := prepareInput_work I J hj
  have hrange := input_rate_bound I J hj
  have hsmallRate : 65536 * (B + 1) ^ 3 * (W + 2) ≤ searchRate B W := by
    dsimp [searchRate]; gcongr <;> norm_num
  have hi' : work (initializeStore P) ≤ searchRate B W * (states J + 2) :=
    hi.trans (Nat.mul_le_mul hsmallRate (Nat.add_le_add_right hcan.1 2))
  have hs' := hs.trans (Nat.mul_le_mul_left (searchRate B W) (prepared_events J))
  have ho' : work (emitStored out.heap out.answer) ≤ searchRate B W * (states J + 1) ^ 2 :=
    ho.trans (Nat.mul_le_mul_right _ hsmallRate)
  have ht := total_work_envelope (encodeInput I).length (states J) (searchRate B W) _ _ _ _
    (states_positive J) hrange hprep hi' hs' ho'
  rw [TreeBudgetStoredExecution.executeInput, work_bind, work_bind]
  rw [work_then_some _ _ _ hout,
    work_then_some _ _ _ (emitStored_correct out.heap out.answer _ hwout ha)]
  simp only [work_charge, work_ret]
  simpa only [P, Nat.add_assoc] using ht

set_option maxRecDepth 4096 in
theorem executeStored_work (bits : Bits) (I : RawInput) (J : Input)
    (hp : parseInput bits = some I) (hj : decodeRaw I = some J) :
    work (executeStored bits) ≤ 2 ^ 50 * (states J) ^ 3 * (bits.length + 1) ^ 7 := by
  have hc := parseInput_canonical bits I hp
  have hparser := parseInputD_steps bits
  have hpa := parseInputD_allocations_le_steps bits
  have hval := TreeBudgetBinaryTotalWork.decodeRawCost_work_encoded I hc.2
  have hexec := executeInput_work I J hj
  rw [← hc.1] at hval hexec
  have h2 : (bits.length + 1) ^ 2 ≤ (bits.length + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (bits.length + 1) ^ 3 ≤ (bits.length + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hS : 1 ≤ (states J) ^ 3 := one_le_pow₀ (states_positive J)
  have hm2 := Nat.mul_le_mul hS h2
  have hm3 := Nat.mul_le_mul hS h3
  have h1 : 1 ≤ (bits.length + 1) ^ 7 := one_le_pow₀ (by omega)
  have hm1 := Nat.mul_le_mul hS h1
  simp only [executeStored, parseInputD_value, hp, TreeBudgetStoredExecution.executeRaw,
    decodeRawCost_value, hj, TreeBudgetStoredExecution.executeChecked, work] at hval hexec ⊢
  nlinarith only [hparser, hpa, hval, hexec, hm2, hm3, hm1]

/-- Both actual steps and cumulative workspace allocations are bounded. -/
theorem executeStored_time_and_allocations (bits : Bits) (I : RawInput) (J : Input)
    (hp : parseInput bits = some I) (hj : decodeRaw I = some J) :
    (executeStored bits).steps ≤ 2 ^ 50 * (states J) ^ 3 * (bits.length + 1) ^ 7 ∧
    (executeStored bits).allocations ≤ 2 ^ 50 * (states J) ^ 3 * (bits.length + 1) ^ 7 := by
  have h := executeStored_work bits I J hp hj
  unfold work at h
  omega

theorem executeStored_work_mass (bits : Bits) (I : RawInput) (J : Input)
    (hp : parseInput bits = some I) (hj : decodeRaw I = some J) :
    work (executeStored bits) ≤ 2 ^ 50 * 2 ^ (3 * mass J) * (bits.length + 1) ^ 7 := by
  apply (executeStored_work bits I J hp hj).trans
  have hS : states J ≤ 2 ^ mass J := TreeBudgetStateParameters.stateBound_le_two_pow_totalMultiplicity _ _
  have h := Nat.mul_le_mul_right ((bits.length + 1) ^ 7)
    (Nat.mul_le_mul_left (2 ^ 50) (Nat.pow_le_pow_left hS 3))
  simpa only [← pow_mul, Nat.mul_comm (mass J) 3] using h

theorem executeStored_work_support_maximum (bits : Bits) (I : RawInput) (J : Input)
    (hp : parseInput bits = some I) (hj : decodeRaw I = some J) :
    work (executeStored bits) ≤ 2 ^ 50 * (maximum J + 1) ^ (3 * support J) * (bits.length + 1) ^ 7 := by
  apply (executeStored_work bits I J hp hj).trans
  have hS : states J ≤ (maximum J + 1) ^ support J := TreeBudgetStateParameters.stateBound_le_maxMultiplicity_pow_positiveCount _ _
  have h := Nat.mul_le_mul_right ((bits.length + 1) ^ 7)
    (Nat.mul_le_mul_left (2 ^ 50) (Nat.pow_le_pow_left hS 3))
  simpa only [← pow_mul, Nat.mul_comm (support J) 3] using h


/-- Invalid strings use parameter zero; all accepted inputs use the normalized
multiplicity parameter of the checked frontend. This is a specification only. -/
noncomputable def encodedMass (bits : Bits) : ℕ := ((TreeBudgetBinaryInput.parse bits).map mass).getD 0
noncomputable def encodedSupport (bits : Bits) : ℕ := ((TreeBudgetBinaryInput.parse bits).map support).getD 0
noncomputable def encodedMaximum (bits : Bits) : ℕ := ((TreeBudgetBinaryInput.parse bits).map maximum).getD 0

theorem rejection_work_polynomial (bits : Bits) (h : TreeBudgetBinaryInput.parse bits = none) :
    work (executeStored bits) ≤ 2 ^ 50 * (bits.length + 1) ^ 7 := by
  have hr := TreeBudgetStoredRejectionBounds.executeStored_rejection_work bits h
  have hd : (bits.length + 1) ^ 3 ≤ (bits.length + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold work
  nlinarith only [hr, hd]

/-- Uniform FPT bound for every bitstring in the addressed bit-cost model.
The exponent of input length is the fixed constant seven. -/
theorem executeStored_fpt_mass (bits : Bits) :
    work (executeStored bits) ≤ 2 ^ 50 * 2 ^ (3 * encodedMass bits) * (bits.length + 1) ^ 7 := by
  cases hp : parseInput bits with
  | none =>
    have h : TreeBudgetBinaryInput.parse bits = none := by simp [TreeBudgetBinaryInput.parse, hp]
    simpa [encodedMass, h] using rejection_work_polynomial bits h
  | some I =>
    cases hj : decodeRaw I with
    | none =>
      have h : TreeBudgetBinaryInput.parse bits = none := by simp [TreeBudgetBinaryInput.parse, hp, hj]
      simpa [encodedMass, h] using rejection_work_polynomial bits h
    | some J =>
      simpa [encodedMass, TreeBudgetBinaryInput.parse, hp, hj] using executeStored_work_mass bits I J hp hj

theorem executeStored_fpt_support_maximum (bits : Bits) :
    work (executeStored bits) ≤ 2 ^ 50 * (encodedMaximum bits + 1) ^ (3 * encodedSupport bits) *
      (bits.length + 1) ^ 7 := by
  cases hp : parseInput bits with
  | none =>
    have h : TreeBudgetBinaryInput.parse bits = none := by simp [TreeBudgetBinaryInput.parse, hp]
    simpa [encodedSupport, encodedMaximum, h] using rejection_work_polynomial bits h
  | some I =>
    cases hj : decodeRaw I with
    | none =>
      have h : TreeBudgetBinaryInput.parse bits = none := by simp [TreeBudgetBinaryInput.parse, hp, hj]
      simpa [encodedSupport, encodedMaximum, h] using rejection_work_polynomial bits h
    | some J =>
      simpa [encodedSupport, encodedMaximum, TreeBudgetBinaryInput.parse, hp, hj] using
        executeStored_work_support_maximum bits I J hp hj

end UAVProof.TreeBudgetStoredTotalWork
