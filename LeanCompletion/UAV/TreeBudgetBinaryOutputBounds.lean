import LeanCompletion.UAV.TreeBudgetBinaryOutput
import LeanCompletion.UAV.TreeBudgetBinaryPipelineBounds

/-! Output bounds use success semantics before serialization. Shared rows are
materialized by `matrixBitsCost`; its work is bounded from the actual decoded
input length and the same finite state box as the memoized search. -/
namespace UAVProof.TreeBudgetBinaryOutputBounds
open TreeBudgetBinaryInput TreeBudgetBinaryCodec TreeBudgetBinaryPipeline
open TreeBudgetBinaryOutput TreeBudgetBinaryPipelineBounds TreeBudgetBitLength
open TreeBudgetParentArray TreeBudgetCostedSearch TreeBudgetVectorMemoState
open TreeBudgetVectorMemoIntegration TreeBudgetVectorSearchStats TreeBudgetVectorChecker
open TreeBudgetVector TreeBudgetPatterns TreeBudgetStateParameters TreeBudgetMemoBounds
open TreeBudgetCacheEntryBounds

theorem preparedSearch_rows_bounds (J : Input) (rows : RowsV J.n)
    (hout : (preparedSearch J).value.1 = some rows) :
    let R := toRootedTree J.parents J.valid
    rows.length ≤ totalMultiplicity R (TreeBudgetPatterns.normalize R (decode J.H)) ∧
      ∀ p ∈ rows, ∀ i : Fin J.n, p[i] ≤ J.H[i] := by
  let R := toRootedTree J.parents J.valid
  let H := TreeBudgetVector.normalize R J.H
  let A := scaleFees J.numerators J.denominators J.budgetDenominator
  let AT := scaleBudget J.denominators J.budgetNumerator J.budgetDenominator
  have he := congrArg (fun out => out.1.1) (preparedSearch_observe J)
  change (preparedSearch J).value.1 =
    (initialRowsStatV R J.H A AT (rootCount R (decode H))).1.1 at he
  rw [hout] at he
  have hresult : (memoRowsV R H A AT (rootCount R (decode H)) H []).1 = some rows := by
    simpa only [initialRowsStatV, memoRowsStatV, memoRowsV,
      memoStatV_erase, H] using he.symm
  have hb := temporary_answer_bounds R H A AT (fun i => (A[i] : ℚ)) (AT : ℚ) 1
    (by norm_num) (by intro i; simp) (by simp)
    (rootCount R (decode H)) H .initial [] (cacheReady_empty ..) rows hresult
  refine ⟨?_, ?_⟩
  · simpa only [H, decode_normalize] using hb.2.1
  · intro p hp i
    apply (hb.2.2 p hp i).trans
    change decode (TreeBudgetVector.normalize R J.H) i ≤ decode J.H i
    rw [decode_normalize]
    by_cases hi : i = R.root <;> simp [TreeBudgetPatterns.normalize, hi]

theorem sum_add_one_le_product {α : Type*} (s : Finset α) (H : α → ℕ) :
    (∑ i ∈ s, H i) + 1 ≤ ∏ i ∈ s, (H i + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    have hm := Nat.mul_le_mul_left (H a + 1) ih
    calc
      H a + (∑ i ∈ s, H i) + 1 ≤
          H a + (∑ i ∈ s, H i) + 1 + H a * (∑ i ∈ s, H i) := Nat.le_add_right _ _
      _ = (H a + 1) * ((∑ i ∈ s, H i) + 1) := by ring
      _ ≤ _ := hm

theorem totalMultiplicity_add_one_le_stateBound {n : ℕ}
    (R : TreeFlowExistence.RootedTree (Fin n)) (H : Fin n → ℕ) :
    totalMultiplicity R H + 1 ≤ stateBound R H :=
  sum_add_one_le_product (nonrootVertices R) H

theorem preparedSearch_rows_length (J : Input) (rows : RowsV J.n)
    (hout : (preparedSearch J).value.1 = some rows) :
    let R := toRootedTree J.parents J.valid
    rows.length + 1 ≤ stateBound R (TreeBudgetPatterns.normalize R (decode J.H)) := by
  have hb := (preparedSearch_rows_bounds J rows hout).1
  have hm := totalMultiplicity_add_one_le_stateBound (toRootedTree J.parents J.valid)
    (TreeBudgetPatterns.normalize (toRootedTree J.parents J.valid) (decode J.H))
  omega

theorem matrixBitsCost_steps_poly {n : ℕ} (rows : RowsV n) (S ell : ℕ)
    (hm : rows.length ≤ S) (hn : n ≤ ell)
    (hp : ∀ p ∈ rows, ∀ i : Fin n, p[i].size ≤ ell) :
    (matrixBitsCost (some rows)).steps ≤ 1024 * (ell + 1) ^ 3 * (S + 1) ^ 2 := by
  have hw := matrixBitsCost_steps rows S ell hm hp
  have hx : 1 ≤ (ell + 1) ^ 3 := by
    have h : 0 < (ell + 1) ^ 3 := by positivity
    omega
  have hxy : ell + 1 ≤ (ell + 1) ^ 3 := Nat.le_self_pow (by decide) _
  have hy : S + 1 ≤ (S + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have hb : (n + 1) ^ 2 * (ell + 1) ≤ (ell + 1) ^ 3 := by
    have h := Nat.mul_le_mul_right (ell + 1)
      (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2)
    simpa only [pow_succ, pow_two] using h
  have hc : (n + 1) * (ell + 1) ≤ (ell + 1) ^ 3 := by
    have h := Nat.mul_le_mul_right (ell + 1) (Nat.add_le_add_right hn 1)
    nlinarith
  have ht₁ : S * (n + 2) ≤ 2 * (ell + 1) ^ 3 * (S + 1) ^ 2 := by
    have h := Nat.mul_le_mul (by omega : S ≤ (S + 1) ^ 2)
      (by omega : n + 2 ≤ 2 * (ell + 1) ^ 3)
    nlinarith
  have hinner : 512 * (n + 1) ^ 2 * (ell + 1) +
      8 * (n + 1) * (ell + 1) + 3 ≤ 523 * (ell + 1) ^ 3 := by nlinarith
  have ht₂ := Nat.mul_le_mul hy hinner
  have ht₃ := Nat.mul_le_mul_right (256 * (S + 1) ^ 2) hx
  have ht₄ : 1 ≤ (ell + 1) ^ 3 * (S + 1) ^ 2 := by
    have h : 0 < (ell + 1) ^ 3 * (S + 1) ^ 2 := by positivity
    omega
  nlinarith

theorem preparedSearch_output_steps (I : RawInput) (J : Input)
    (h : decodeRaw I = some J) :
    let R := toRootedTree J.parents J.valid
    let S := stateBound R (TreeBudgetPatterns.normalize R (decode J.H))
    (matrixBitsCost (preparedSearch J).value.1).steps ≤
      1024 * ((encodeInput I).length + 1) ^ 3 * (S + 1) ^ 2 := by
  dsimp only
  cases hout : (preparedSearch J).value.1 with
  | none =>
    simp only [matrixBitsCost]
    have hh : 0 < 1024 * ((encodeInput I).length + 1) ^ 3 *
        (stateBound (toRootedTree J.parents J.valid)
          (TreeBudgetPatterns.normalize (toRootedTree J.parents J.valid) (decode J.H)) + 1) ^ 2 :=
      by positivity
    omega
  | some rows =>
    have hr := preparedSearch_rows_bounds J rows hout
    have hl := preparedSearch_rows_length J rows hout
    have hfields := decodeRaw_fields I J h
    apply matrixBitsCost_steps_poly rows _ (encodeInput I).length (by omega)
      (dimension_bound I (decodeRaw_shape I J h) J.H hfields.2.2.1)
    intro p hp i
    exact (Nat.size_le_size (hr.2 p hp i)).trans (coordinate_width I J.H hfields.2.2.1 i)

end UAVProof.TreeBudgetBinaryOutputBounds

#print axioms UAVProof.TreeBudgetBinaryOutputBounds.preparedSearch_rows_bounds
#print axioms UAVProof.TreeBudgetBinaryOutputBounds.sum_add_one_le_product
#print axioms UAVProof.TreeBudgetBinaryOutputBounds.totalMultiplicity_add_one_le_stateBound
#print axioms UAVProof.TreeBudgetBinaryOutputBounds.preparedSearch_rows_length
#print axioms UAVProof.TreeBudgetBinaryOutputBounds.matrixBitsCost_steps_poly
#print axioms UAVProof.TreeBudgetBinaryOutputBounds.preparedSearch_output_steps
