import LeanCompletion.UAV.TreeBudgetVectorMemoIntegration
import Mathlib.Data.Nat.Size
import LeanCompletion.UAV.TreeBudgetBinaryCodec

/-! Explicit binary-width inequalities, including signed intermediate sums.
These are value/representation bounds, independent of a later cost ledger. -/
namespace UAVProof.TreeBudgetBitLength
open TreeFlowExistence TreeBudgetIntegerCost TreeBudgetStateParameters
open TreeBudgetVector TreeBudgetVectorMemoState TreeBudgetVectorMemoIntegration
open TreeBudgetMemoReachability TreeBudgetCacheEntryBounds TreeBudgetParameterizedBounds
variable {n : ℕ}

theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  rw [pow_add]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have hp : 0 < 2 ^ Nat.size a := by positivity
  nlinarith

theorem size_add_le (a b : ℕ) : Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  apply Nat.size_le.mpr
  rw [pow_succ, pow_add]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have hpa : 0 < 2 ^ Nat.size a := by positivity
  have hpb : 0 < 2 ^ Nat.size b := by positivity
  nlinarith

theorem size_sum_le {α : Type*} (s : Finset α) (f : α → ℕ) :
    Nat.size (∑ i ∈ s, f i) ≤ s.card + ∑ i ∈ s, Nat.size (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    exact (size_add_le _ _).trans (by omega)

theorem size_prod_le {α : Type*} (s : Finset α) (f : α → ℕ) :
    Nat.size (∏ i ∈ s, f i) ≤ 1 + ∑ i ∈ s, Nat.size (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (size_mul_le _ _).trans (by omega)

theorem size_commonDenominator (b : Fin n → ℕ) (bT : ℕ) :
    Nat.size (commonDenominator b bT) ≤ Nat.size bT + 1 + ∑ v, Nat.size (b v) := by
  exact (size_mul_le bT _).trans (by have h := size_prod_le Finset.univ b; omega)

theorem size_scaledNumerator (D : ℕ) (a : ℤ) (b : ℕ) :
    Nat.size (scaledNumerator D a b).natAbs ≤ Nat.size a.natAbs + Nat.size D := by
  simp only [scaledNumerator, Int.natAbs_mul, Int.natAbs_natCast]
  exact (size_mul_le _ _).trans (Nat.add_le_add_left (Nat.size_le_size (Nat.div_le_self ..)) _)

theorem size_signed_add (a b : ℤ) :
    Nat.size (a + b).natAbs ≤ Nat.size a.natAbs + Nat.size b.natAbs + 1 :=
  (Nat.size_le_size (Int.natAbs_add_le a b)).trans (size_add_le ..)

/-- All subsets, and therefore every running partial sum, are bounded. Signed
cancellation in the final result cannot invalidate this inequality. -/
theorem partial_sum_natAbs_le {α : Type*} (s : Finset α) (c : α → ℤ)
    (p : α → ℕ) (C M : ℕ) (hc : ∀ v ∈ s, (c v).natAbs ≤ C)
    (hp : ∑ v ∈ s, p v ≤ M) :
    (∑ v ∈ s, c v * (p v : ℤ)).natAbs ≤ C * M := by
  calc
    _ ≤ ∑ v ∈ s, (c v * (p v : ℤ)).natAbs := Int.natAbs_sum_le _ _
    _ = ∑ v ∈ s, (c v).natAbs * p v := by simp only [Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ ∑ v ∈ s, C * p v := Finset.sum_le_sum (fun v hv => Nat.mul_le_mul_right _ (hc v hv))
    _ = C * ∑ v ∈ s, p v := (Finset.mul_sum ..).symm
    _ ≤ C * M := Nat.mul_le_mul_left C hp

theorem partial_sum_size_le {α : Type*} (s : Finset α) (c : α → ℤ)
    (p : α → ℕ) (C M : ℕ) (hc : ∀ v ∈ s, (c v).natAbs ≤ C)
    (hp : ∑ v ∈ s, p v ≤ M) :
    Nat.size (∑ v ∈ s, c v * (p v : ℤ)).natAbs ≤ Nat.size C + Nat.size M :=
  (Nat.size_le_size (partial_sum_natAbs_le s c p C M hc hp)).trans (size_mul_le C M)

theorem size_residual_coordinate (H r : Vector ℕ n) (hr : decode r ≤ decode H) (v : Fin n) :
    Nat.size r[v] ≤ Nat.size H[v] := Nat.size_le_size (hr v)

theorem size_totalMultiplicity (R : RootedTree (Fin n)) (H : Fin n → ℕ) :
    Nat.size (totalMultiplicity R H) ≤ n + ∑ v, Nat.size (H v) := by
  have h := size_sum_le (nonrootVertices R) H
  have hc : (nonrootVertices R).card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ (nonrootVertices R))
  have hs : (∑ v ∈ nonrootVertices R, Nat.size (H v)) ≤ ∑ v, Nat.size (H v) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  exact h.trans (by omega)

/-- Temporary successful return values are bounded before they are stored in
their parent's cache. This uses success semantics, not membership in that cache. -/
theorem temporary_answer_bounds (R : RootedTree (Fin n)) (H : Vector ℕ n)
    (A : Vector ℤ n) (AT : ℤ) (s : Fin n → ℚ) (T D : ℚ)
    (hD : 0 < D) (hA : ∀ v : Fin n, (A[v] : ℚ) = D * s v)
    (hAT : (AT : ℚ) = D * T) (k : ℕ) (r : Vector ℕ n)
    (hr : ReachableResidual R (decode H) s T k (decode r))
    (cs : CacheV n) (hc : CacheReadyV R H s T cs) (rows : RowsV n)
    (hout : (memoRowsV R H A AT k r cs).1 = some rows) :
    rows.length = k ∧ rows.length ≤ totalMultiplicity R (decode H) ∧
      ∀ p ∈ rows, ∀ v : Fin n, p[v] ≤ H[v] := by
  have he := congrArg Prod.fst (memoRowsV_refines R H A AT s T D hD hA hAT k r cs)
  change decodeAnswer (memoRowsV R H A AT k r cs).1 = _ at he
  rw [hout, decodeAnswer_some] at he
  have hw := TreeBudgetMemoSearch.memoRows_sound R (decode H) s T k (decode r)
    (decodeCache cs) (decodeRows rows) hc.valid he.symm
  have hlen : rows.length = k := by simpa using hw.1
  refine ⟨hlen, ?_, ?_⟩
  · rw [hlen]
    exact (reachable_count_le_initial R (decode H) s T hr).trans
      (rootCount_le_totalMultiplicity R (decode H))
  · intro p hp v
    have hv := hw.2.1 (decode p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    by_cases hvr : v = R.root
    · subst v
      change decode p R.root ≤ decode H R.root
      rw [hv.1]
      exact Nat.zero_le _
    · exact hv.2.1 v hvr

open TreeBudgetBinaryCodec

theorem size_list_prod_le (xs : List ℕ) :
    Nat.size xs.prod ≤ 1 + (xs.map Nat.size).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    exact (size_mul_le _ _).trans (by omega)

theorem size_list_sum_le (xs : List ℕ) :
    Nat.size xs.sum ≤ xs.length + (xs.map Nat.size).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons, List.length_cons]
    exact (size_add_le _ _).trans (by omega)

/-- Product preprocessing value on the actual parsed denominator fields. -/
def inputDenominator (I : RawInput) : ℕ := I.budgetDenominator * I.denominators.prod

theorem size_inputDenominator_le_length (I : RawInput) :
    Nat.size (inputDenominator I) ≤ (encodeInput I).length + 1 := by
  have h := (size_mul_le I.budgetDenominator I.denominators.prod).trans
    (Nat.add_le_add_left (size_list_prod_le I.denominators) _)
  have he := inputWeight_le_length I
  dsimp [inputDenominator]
  dsimp [inputWeight] at he
  omega

theorem size_input_numerator_le_length (I : RawInput) (a : ℤ) (ha : a ∈ I.numerators) :
    Nat.size a.natAbs ≤ (encodeInput I).length := by
  have hm : Nat.size a.natAbs ∈ I.numerators.map (fun z => Nat.size z.natAbs) :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  have hs := List.le_sum_of_mem hm
  have he := inputWeight_le_length I
  dsimp [inputWeight] at he
  omega

theorem size_input_scaled_fee (I : RawInput) (a : ℤ) (ha : a ∈ I.numerators) (b : ℕ) :
    Nat.size (scaledNumerator (inputDenominator I) a b).natAbs ≤
      2 * (encodeInput I).length + 1 := by
  have h := size_scaledNumerator (inputDenominator I) a b
  have hd := size_inputDenominator_le_length I
  have ha' := size_input_numerator_le_length I a ha
  omega

theorem size_input_scaled_budget (I : RawInput) :
    Nat.size (scaledNumerator (inputDenominator I) I.budgetNumerator
      I.budgetDenominator).natAbs ≤ 2 * (encodeInput I).length + 1 := by
  have h := size_scaledNumerator (inputDenominator I) I.budgetNumerator I.budgetDenominator
  have hd := size_inputDenominator_le_length I
  have he := inputWeight_le_length I
  dsimp [inputWeight] at he
  omega

theorem size_input_scaled_coefficient (I : RawInput) (a a' : ℤ)
    (ha : a ∈ I.numerators) (ha' : a' ∈ I.numerators) (b b' : ℕ) :
    Nat.size (scaledNumerator (inputDenominator I) a b +
      scaledNumerator (inputDenominator I) a' b').natAbs ≤
      4 * (encodeInput I).length + 3 := by
  have h := size_signed_add (scaledNumerator (inputDenominator I) a b)
    (scaledNumerator (inputDenominator I) a' b')
  have h₁ := size_input_scaled_fee I a ha b
  have h₂ := size_input_scaled_fee I a' ha' b'
  omega

theorem size_input_multiplicity_sum (I : RawInput) (hs : Shape I) :
    Nat.size I.multiplicities.sum ≤ 2 * (encodeInput I).length := by
  have h := size_list_sum_le I.multiplicities
  have hn := vertexCount_le_length I hs
  have he := inputWeight_le_length I
  have hh := hs.2.1
  dsimp [inputWeight] at he
  omega

theorem width_budget_le_input (I : RawInput) (hs : Shape I) (M : ℕ)
    (hM : M ≤ I.multiplicities.sum) :
    (encodeInput I).length + Nat.size (M + 1) + 2 ≤ 3 * (encodeInput I).length + 4 := by
  have h := size_add_le M 1
  have hm := (Nat.size_le_size hM).trans (size_input_multiplicity_sum I hs)
  norm_num at h
  omega

theorem size_list_state_product (xs : List ℕ) :
    Nat.size ((xs.map (· + 1)).prod) ≤ 1 + 2 * xs.length + (xs.map Nat.size).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h := size_mul_le (x + 1) ((xs.map (· + 1)).prod)
    have hx := size_add_le x 1
    simp only [List.map_cons, List.prod_cons, List.length_cons, List.sum_cons]
    norm_num at hx
    omega

/-- A conservative address-width bridge: the logarithm of the entire raw
state box is linear in the genuine input length, even with a nonzero root. -/
theorem size_input_state_product (I : RawInput) (hs : Shape I) :
    Nat.size ((I.multiplicities.map (· + 1)).prod) ≤ 3 * (encodeInput I).length + 1 := by
  have h := size_list_state_product I.multiplicities
  have hn := vertexCount_le_length I hs
  have he := inputWeight_le_length I
  have hh := hs.2.1
  dsimp [inputWeight] at he
  omega

/-- Division-free preprocessing can use this product of all other denominators. -/
def denominatorCofactor (b : Fin n → ℕ) (bT : ℕ) (v : Fin n) : ℕ :=
  bT * ∏ w ∈ Finset.univ.erase v, b w

theorem denominator_mul_cofactor (b : Fin n → ℕ) (bT : ℕ) (v : Fin n) :
    b v * denominatorCofactor b bT v = commonDenominator b bT := by
  unfold denominatorCofactor commonDenominator
  rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ v)]
  ring

theorem denominatorCofactor_eq_div (b : Fin n → ℕ) (bT : ℕ) (v : Fin n)
    (hb : 0 < b v) : denominatorCofactor b bT v = commonDenominator b bT / b v := by
  rw [← denominator_mul_cofactor b bT v, Nat.mul_div_cancel_left _ hb]

theorem partial_sum_size_encoded {α : Type*} (I : RawInput) (hs : Shape I)
    (s : Finset α) (c : α → ℤ) (p : α → ℕ) (M : ℕ)
    (hM : M ≤ I.multiplicities.sum)
    (hc : ∀ v ∈ s, Nat.size (c v).natAbs ≤ 4 * (encodeInput I).length + 3)
    (hp : ∑ v ∈ s, p v ≤ M) :
    Nat.size (∑ v ∈ s, c v * (p v : ℤ)).natAbs ≤ 6 * (encodeInput I).length + 4 := by
  have hc' : ∀ v ∈ s, (c v).natAbs ≤ 2 ^ (4 * (encodeInput I).length + 3) :=
    fun v hv => (Nat.size_le.mp (hc v hv)).le
  have h := partial_sum_size_le s c p _ M hc' hp
  rw [Nat.size_pow] at h
  have hm := (Nat.size_le_size hM).trans (size_input_multiplicity_sum I hs)
  omega

theorem vector_list_prod (H : Vector ℕ n) :
    (H.toList.map (· + 1)).prod = ∏ v : Fin n, (H[v] + 1) := by
  have he : H.toList = List.ofFn (fun v : Fin n => H[v]) := by
    simpa only [Vector.toList_ofFn] using
      congrArg Vector.toList (Vector.ofFn_getElem (xs := H)).symm
  rw [he, List.map_ofFn, List.prod_ofFn]
  rfl

theorem stateBound_le_list_product (R : RootedTree (Fin n)) (H : Vector ℕ n) :
    TreeBudgetMemoBounds.stateBound R (decode H) ≤ (H.toList.map (· + 1)).prod := by
  rw [vector_list_prod]
  unfold TreeBudgetMemoBounds.stateBound
  exact Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
    (fun _ _ => Nat.zero_le _) (fun _ _ _ => by omega)

theorem size_stateBound_of_input (I : RawInput) (hs : Shape I)
    (R : RootedTree (Fin n)) (H : Vector ℕ n) (hH : H.toList = I.multiplicities) :
    Nat.size (TreeBudgetMemoBounds.stateBound R (decode H)) ≤
      3 * (encodeInput I).length + 1 := by
  have h := Nat.size_le_size (stateBound_le_list_product R H)
  rw [hH] at h
  exact h.trans (size_input_state_product I hs)

theorem stateBound_normalize (R : RootedTree (Fin n)) (H : Fin n → ℕ) :
    TreeBudgetMemoBounds.stateBound R (TreeBudgetPatterns.normalize R H) =
      TreeBudgetMemoBounds.stateBound R H := by
  unfold TreeBudgetMemoBounds.stateBound
  apply Finset.prod_congr rfl
  intro v hv
  have hn := (Finset.mem_filter.mp hv).2
  simp [TreeBudgetPatterns.normalize, hn]

theorem size_stateBound_normalized_of_input (I : RawInput) (hs : Shape I)
    (R : RootedTree (Fin n)) (H : Vector ℕ n) (hH : H.toList = I.multiplicities) :
    Nat.size (TreeBudgetMemoBounds.stateBound R (TreeBudgetPatterns.normalize R (decode H))) ≤
      3 * (encodeInput I).length + 1 := by
  rw [stateBound_normalize]
  exact size_stateBound_of_input I hs R H hH

end UAVProof.TreeBudgetBitLength

#print axioms UAVProof.TreeBudgetBitLength.size_mul_le
#print axioms UAVProof.TreeBudgetBitLength.size_add_le
#print axioms UAVProof.TreeBudgetBitLength.size_sum_le
#print axioms UAVProof.TreeBudgetBitLength.size_prod_le
#print axioms UAVProof.TreeBudgetBitLength.size_commonDenominator
#print axioms UAVProof.TreeBudgetBitLength.size_scaledNumerator
#print axioms UAVProof.TreeBudgetBitLength.size_signed_add
#print axioms UAVProof.TreeBudgetBitLength.partial_sum_natAbs_le
#print axioms UAVProof.TreeBudgetBitLength.partial_sum_size_le
#print axioms UAVProof.TreeBudgetBitLength.size_residual_coordinate
#print axioms UAVProof.TreeBudgetBitLength.size_totalMultiplicity
#print axioms UAVProof.TreeBudgetBitLength.temporary_answer_bounds
#print axioms UAVProof.TreeBudgetBitLength.size_list_prod_le
#print axioms UAVProof.TreeBudgetBitLength.size_list_sum_le
#print axioms UAVProof.TreeBudgetBitLength.inputDenominator
#print axioms UAVProof.TreeBudgetBitLength.size_inputDenominator_le_length
#print axioms UAVProof.TreeBudgetBitLength.size_input_numerator_le_length
#print axioms UAVProof.TreeBudgetBitLength.size_input_scaled_fee
#print axioms UAVProof.TreeBudgetBitLength.size_input_scaled_budget
#print axioms UAVProof.TreeBudgetBitLength.size_input_scaled_coefficient
#print axioms UAVProof.TreeBudgetBitLength.size_input_multiplicity_sum
#print axioms UAVProof.TreeBudgetBitLength.width_budget_le_input
#print axioms UAVProof.TreeBudgetBitLength.size_list_state_product
#print axioms UAVProof.TreeBudgetBitLength.size_input_state_product
#print axioms UAVProof.TreeBudgetBitLength.denominatorCofactor
#print axioms UAVProof.TreeBudgetBitLength.denominator_mul_cofactor
#print axioms UAVProof.TreeBudgetBitLength.denominatorCofactor_eq_div
#print axioms UAVProof.TreeBudgetBitLength.partial_sum_size_encoded
#print axioms UAVProof.TreeBudgetBitLength.vector_list_prod
#print axioms UAVProof.TreeBudgetBitLength.stateBound_le_list_product
#print axioms UAVProof.TreeBudgetBitLength.size_stateBound_of_input
#print axioms UAVProof.TreeBudgetBitLength.stateBound_normalize
#print axioms UAVProof.TreeBudgetBitLength.size_stateBound_normalized_of_input
