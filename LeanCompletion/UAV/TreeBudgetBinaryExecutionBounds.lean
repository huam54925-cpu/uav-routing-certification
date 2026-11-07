import LeanCompletion.UAV.TreeBudgetBinaryPipeline
import LeanCompletion.UAV.TreeBudgetBinarySearchInputBounds
import LeanCompletion.UAV.TreeBudgetBinaryPipelineBounds
import LeanCompletion.UAV.TreeBudgetBinarySearchStorage

/-! Composition of preprocessing, enumeration, checking and search costs.
The frontend and output are separate. This theorem bounds actual accumulated
phase work; it does not assume a total-time bound as a premise. -/
namespace UAVProof.TreeBudgetBinaryExecutionBounds
open TreeBudgetBinaryInput TreeBudgetBinaryCodec TreeBudgetBinaryPreprocessing
open TreeBudgetBinaryPipeline TreeBudgetBinaryPipelineBounds TreeBudgetBinarySearchInputBounds
open TreeBudgetBinarySearch TreeBudgetCostedSearch TreeBudgetCostedSearchBounds
open TreeBudgetCostedCandidates TreeBudgetParentArray TreeBudgetVector TreeBudgetVectorChecker
open TreeBudgetIntegerCost TreeBudgetBitLength TreeBudgetPatterns TreeBudgetMemoBounds

theorem denominator_eq_input (I : RawInput) (J : Input) (h : decodeRaw I = some J) :
    commonDenominator (decode J.denominators) J.budgetDenominator = inputDenominator I := by
  have hf := decodeRaw_fields I J h
  rw [commonDenominator, ← vector_prod, hf.2.2.2.2.1, hf.2.2.2.2.2.2]
  rfl

theorem numerator_width (I : RawInput) (J : Input) (h : decodeRaw I = some J) (v : Fin J.n) :
    J.numerators[v].natAbs.size ≤ (encodeInput I).length := by
  apply size_input_numerator_le_length
  rw [← (decodeRaw_fields I J h).2.2.2.1]
  apply Vector.mem_toList_iff.mpr
  exact Vector.mem_iff_getElem.mpr ⟨v.val, v.isLt, by simp⟩

theorem scaled_fee_width (I : RawInput) (J : Input) (h : decodeRaw I = some J) :
    ∀ v : Fin J.n,
      (scaleFees J.numerators J.denominators J.budgetDenominator)[v].natAbs.size ≤
        2 * (encodeInput I).length + 1 := by
  intro v
  have hm : J.numerators[v] ∈ I.numerators := by
    rw [← (decodeRaw_fields I J h).2.2.2.1]
    apply Vector.mem_toList_iff.mpr
    exact Vector.mem_iff_getElem.mpr ⟨v.val, v.isLt, by simp⟩
  simpa only [scaleFees, Fin.getElem_fin, Vector.getElem_ofFn, denominator_eq_input I J h]
    using size_input_scaled_fee I J.numerators[v] hm J.denominators[v]

theorem scaled_budget_width (I : RawInput) (J : Input) (h : decodeRaw I = some J) :
    (scaleBudget J.denominators J.budgetNumerator J.budgetDenominator).natAbs.size ≤
      2 * (encodeInput I).length + 1 := by
  have hf := decodeRaw_fields I J h
  rw [scaleBudget, denominator_eq_input I J h, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2]
  exact size_input_scaled_budget I

theorem normalized_le (J : Input) :
    ∀ i : Fin J.n, (normalizeCost J.parents J.H).value[i] ≤ J.H[i] := by
  intro i
  simp only [normalizeCost, copyVector_value, Fin.getElem_fin, Vector.getElem_set]
  split_ifs <;> omega

theorem preprocessing_steps (I : RawInput) (J : Input) (h : decodeRaw I = some J) :
    (scaleFeesCost J.numerators J.denominators J.budgetDenominator).steps +
      (scaleBudgetCost J.denominators J.budgetNumerator).steps ≤
        32768 * ((encodeInput I).length + 1) ^ 4 := by
  let ell := (encodeInput I).length
  have hf := decodeRaw_fields I J h
  have hn : J.n ≤ ell := hf.1.trans_le (vertexCount_le_length I (decodeRaw_shape I J h))
  have hw := inputWeight_le_length I
  have hden : J.budgetDenominator.size + (J.denominators.toList.map Nat.size).sum ≤ ell := by
    rw [hf.2.2.2.2.1, hf.2.2.2.2.2.2]
    dsimp [inputWeight] at hw
    omega
  have hnum : J.budgetNumerator.natAbs.size ≤ ell := by
    rw [hf.2.2.2.2.2.1]
    dsimp [inputWeight] at hw
    omega
  have hfees := scaleFeesCost_steps J.numerators J.denominators J.budgetDenominator ell
    hden (numerator_width I J h)
  have hbudget := scaleBudgetCost_steps J.denominators J.budgetNumerator ell
    (by omega) hnum
  have hc₁ : 1024 * (J.n + 1) * (J.n + 3) * (ell + 2) ^ 2 ≤
      1024 * (ell + 1) * (ell + 3) * (ell + 2) ^ 2 := by gcongr
  have hc₂ : (J.n + 2) * (512 * (ell + 2) ^ 2) ≤
      (ell + 2) * (512 * (ell + 2) ^ 2) := by gcongr
  change _ ≤ 32768 * (ell + 1) ^ 4
  nlinarith only [hfees, hbudget, hc₁, hc₂, Nat.zero_le (ell ^ 4), Nat.zero_le (ell ^ 3)]

theorem phase_envelope (ell S norm pre cand count srch : ℕ)
    (hn : norm ≤ 128 * (ell + 1) ^ 2)
    (hp : pre ≤ 32768 * (ell + 1) ^ 4)
    (hc : cand ≤ 310000 * (ell + 1) ^ 3 * S)
    (hk : count ≤ 1024 * (ell + 1) ^ 2)
    (hs : srch ≤ 15000 * (ell + 1) ^ 2 * (S + 1) ^ 3) :
    norm + pre + cand + count + srch ≤ 500000 * (ell + 1) ^ 4 * (S + 1) ^ 3 := by
  have h2 : (ell + 1) ^ 2 ≤ (ell + 1) ^ 4 := by nlinarith
  have h3 : (ell + 1) ^ 3 ≤ (ell + 1) ^ 4 := by nlinarith
  have hS : S ≤ (S + 1) ^ 3 := by nlinarith only [Nat.zero_le (S ^ 3), Nat.zero_le (S ^ 2)]
  have hS1 : 1 ≤ (S + 1) ^ 3 := by
    have hpos : 0 < (S + 1) ^ 3 := by positivity
    omega
  have a := Nat.mul_le_mul h2 hS1
  have b := Nat.mul_le_mul h3 hS
  have c := Nat.mul_le_mul_left ((ell + 1) ^ 4) hS1
  have d := Nat.mul_le_mul_right ((S + 1) ^ 3) h2
  nlinarith only [hn, hp, hc, hk, hs, a, b, c, d]

set_option maxRecDepth 4096 in
theorem preparedSearch_work (I : RawInput) (J : Input) (h : decodeRaw I = some J) :
    (preparedSearch J).work ≤ 500000 * ((encodeInput I).length + 1) ^ 4 *
      (stateBound (toRootedTree J.parents J.valid)
        (TreeBudgetPatterns.normalize (toRootedTree J.parents J.valid) (decode J.H)) + 1) ^ 3 := by
  let R := toRootedTree J.parents J.valid
  let H := (normalizeCost J.parents J.H).value
  let A := (scaleFeesCost J.numerators J.denominators J.budgetDenominator).value
  let AT := (scaleBudgetCost J.denominators J.budgetNumerator).value
  let ell := (encodeInput I).length
  let s := fun v : Fin J.n => (J.numerators[v] : ℚ) / (J.denominators[v] : ℚ)
  let T : ℚ := (J.budgetNumerator : ℚ) / (J.budgetDenominator : ℚ)
  let D : ℚ := commonDenominator (decode J.denominators) J.budgetDenominator
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast commonDenominator_pos (decode J.denominators) J.budgetDenominator
      J.positive J.budgetPositive
  have hA : ∀ v : Fin J.n, (A[v] : ℚ) = D * s v := by
    intro v
    simp only [A, scaleFeesCost_value _ _ _ J.positive, scaleFees,
      Fin.getElem_fin, Vector.getElem_ofFn]
    exact scaledNumerator_cast _ _ _
      (denominator_dvd_commonDenominator (decode J.denominators) J.budgetDenominator v)
  have hAT : (AT : ℚ) = D * T := by
    simp only [AT, scaleBudgetCost_value _ _ _ J.budgetPositive, scaleBudget]
    exact scaledNumerator_cast _ _ _
      (budget_denominator_dvd_commonDenominator (decode J.denominators) J.budgetDenominator)
  have hnorm := normalizeCost_work_input I J.parents J.H (decodeRaw_fields I J h).2.2.1
  have hpre := preprocessing_steps I J h
  have hcand := candidateCost_work_input_poly I (decodeRaw_shape I J h)
    J.parents J.valid J.H H A AT (decodeRaw_fields I J h).2.2.1 (normalized_le J)
    (by simpa only [A, scaleFeesCost_value _ _ _ J.positive] using scaled_fee_width I J h)
    (by simpa only [AT, scaleBudgetCost_value _ _ _ J.budgetPositive] using scaled_budget_width I J h)
  have hcount := rootCountCost_work_input I (decodeRaw_shape I J h)
    J.parents J.H H (decodeRaw_fields I J h).2.2.1 (normalized_le J)
  have hsearch := decoded_search_work I J h R A AT s T D hD hA hAT
  have hn : J.n ≤ ell := (decodeRaw_fields I J h).1.trans_le
    (vertexCount_le_length I (decodeRaw_shape I J h))
  have hnorm' : (normalizeCost J.parents J.H).steps ≤ 128 * (ell + 1) ^ 2 := by
    unfold work at hnorm
    have hm := Nat.mul_le_mul_right (ell + 1) (Nat.add_le_add_right hn 1)
    nlinarith only [hnorm, hm]
  have hcount' : (rootCountCost J.parents H).steps ≤ 1024 * (ell + 1) ^ 2 := by
    unfold work at hcount
    have hm := Nat.mul_le_mul_right (2 * ell + 1) (Nat.add_le_add_right hn 1)
    nlinarith only [hcount, hm]
  have hcand' := Nat.le_add_right (candidateCost J.parents H A AT).steps
    (candidateCost J.parents H A AT).allocations |>.trans hcand
  have hh : H = TreeBudgetVector.normalize R J.H := normalizeCost_value J.parents J.valid J.H
  simp only [hh, decode_normalize] at hcand'
  have hs : (search (candidateCost J.parents H A AT).value
      (rootCountCost J.parents H).value H []).work ≤
      15000 * (ell + 1) ^ 2 *
        (stateBound R (TreeBudgetPatterns.normalize R (decode J.H)) + 1) ^ 3 := by
    simpa only [candidateCost_value J.parents J.valid, rootCountCost_value J.parents J.valid,
      hh, search, initialCost] using hsearch
  have hout := phase_envelope ell _ _ _ _ _ _ hnorm' hpre hcand' hcount' hs
  simpa only [preparedSearch, H, A, AT, R, ell,
    normalizeCost_value J.parents J.valid, Nat.add_assoc] using hout

end UAVProof.TreeBudgetBinaryExecutionBounds
