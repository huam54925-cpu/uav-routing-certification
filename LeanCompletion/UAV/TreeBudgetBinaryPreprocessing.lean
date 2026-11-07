import LeanCompletion.UAV.TreeBudgetBitPrimitives
import LeanCompletion.UAV.TreeBudgetBitLength

/-! Division-free fraction preprocessing. Products are evaluated by the
digit-recursive multiplier. Each numerator is multiplied by the product of
the other denominators, including the budget denominator. Raw fractions are
not reduced and signed numerators are preserved. -/
namespace UAVProof.TreeBudgetBinaryPreprocessing
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetBitLength
open TreeBudgetVector TreeBudgetVectorChecker TreeBudgetIntegerCost
variable {n : ℕ}

def productCost : List ℕ → Costed ℕ
  | [] => ⟨1, 1, 1⟩
  | a :: xs =>
    let tail := productCost xs
    let out := mulNatD a tail.value
    ⟨out.value, tail.steps + out.steps + 1, tail.allocations + out.allocations⟩

@[simp] theorem productCost_value (xs : List ℕ) : (productCost xs).value = xs.prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [productCost, ih]

theorem productCost_steps (xs : List ℕ) (B : ℕ) (h : (xs.map Nat.size).sum ≤ B) :
    (productCost xs).steps ≤ xs.length * (201 * (B + 2) ^ 2) + 1 := by
  induction xs with
  | nil => simp [productCost]
  | cons a xs ih =>
    have ht : (xs.map Nat.size).sum ≤ B := by simpa using (le_trans (by simp) h)
    have ha : a.size ≤ B + 1 := by simpa using (le_trans (by simp) (Nat.le_succ_of_le h))
    have hp : xs.prod.size ≤ B + 1 := (size_list_prod_le xs).trans (by omega)
    have hm := mulNatD_steps a xs.prod (B + 1) ha hp
    have hi := ih ht
    simp only [productCost, productCost_value, List.length_cons]
    nlinarith

theorem productCost_allocations (xs : List ℕ) :
    (productCost xs).allocations ≤ (productCost xs).steps := by
  induction xs with
  | nil => simp [productCost]
  | cons a xs ih =>
    have hm := mulNatD_allocations_le_steps a (productCost xs).value
    simp only [productCost]
    omega

/-- The index is a bounded unary traversal cursor. No array is allocated
according to an unchecked binary length. Existing natural words are shared. -/
def omitAt : ℕ → List ℕ → Costed (List ℕ)
  | _, [] => ⟨[], 1, 0⟩
  | 0, _ :: xs => ⟨xs, 1, 0⟩
  | k + 1, a :: xs =>
    let tail := omitAt k xs
    ⟨a :: tail.value, tail.steps + 2, tail.allocations + 1⟩

@[simp] theorem omitAt_value (k : ℕ) (xs : List ℕ) :
    (omitAt k xs).value = xs.eraseIdx k := by
  induction xs generalizing k with
  | nil => simp [omitAt]
  | cons a xs ih => cases k <;> simp [omitAt, ih]

theorem omitAt_bounds (k : ℕ) (xs : List ℕ) :
    (omitAt k xs).steps ≤ 2 * xs.length + 1 ∧
      (omitAt k xs).allocations ≤ xs.length := by
  induction xs generalizing k with
  | nil => simp [omitAt]
  | cons a xs ih =>
    cases k with
    | zero => simp [omitAt]
    | succ k =>
      have h := ih k
      simp only [omitAt, List.length_cons]
      constructor <;> omega

def cofactorCost (b : Vector ℕ n) (bT : ℕ) (v : Fin n) : Costed ℕ :=
  let rest := omitAt v.val b.toList
  let out := productCost (bT :: rest.value)
  ⟨out.value, rest.steps + out.steps + 1, rest.allocations + out.allocations + 1⟩

theorem vector_prod (b : Vector ℕ n) : b.toList.prod = ∏ v, decode b v := by
  have he : b.toList = List.ofFn (decode b) := by
    apply List.ext_getElem <;> simp [decode]
  rw [he, List.prod_ofFn]

theorem cofactorCost_value (b : Vector ℕ n) (bT : ℕ) (v : Fin n) (hb : 0 < b[v]) :
    (cofactorCost b bT v).value = commonDenominator (decode b) bT / b[v] := by
  have hi : v.val < b.toList.length := by simp
  have hm := List.CommMonoid.mul_prod_eraseIdx (l := b.toList) hi
  have he : b[v] * (bT * (b.toList.eraseIdx v.val).prod) =
      commonDenominator (decode b) bT := by
    rw [commonDenominator, ← vector_prod]
    simpa [Nat.mul_left_comm] using congrArg (bT * ·) hm
  simp only [cofactorCost, productCost_value, omitAt_value, List.prod_cons]
  rw [← he, Nat.mul_div_cancel_left _ hb]

def scaleFeeCost (a : Vector ℤ n) (b : Vector ℕ n) (bT : ℕ) (v : Fin n) : Costed ℤ :=
  let factor := cofactorCost b bT v
  let out := mulIntD a[v] (factor.value : ℤ)
  ⟨out.value, factor.steps + out.steps + 1, factor.allocations + out.allocations⟩

@[simp] theorem scaleFeeCost_value (a : Vector ℤ n) (b : Vector ℕ n) (bT : ℕ)
    (v : Fin n) (hb : 0 < b[v]) :
    (scaleFeeCost a b bT v).value = scaledNumerator (commonDenominator (decode b) bT) a[v] b[v] := by
  simp [scaleFeeCost, cofactorCost_value b bT v hb, scaledNumerator]

def scaleFeesCost (a : Vector ℤ n) (b : Vector ℕ n) (bT : ℕ) : Costed (Vector ℤ n) :=
  vectorize (Vector.ofFn (scaleFeeCost a b bT))

theorem scaleFeesCost_value (a : Vector ℤ n) (b : Vector ℕ n) (bT : ℕ)
    (hb : ∀ v : Fin n, 0 < b[v]) :
    (scaleFeesCost a b bT).value = scaleFees a b bT := by
  apply Vector.ext
  intro i hi
  simp [scaleFeesCost, scaleFees, scaleFeeCost_value _ _ _ ⟨i, hi⟩ (hb ⟨i, hi⟩)]

def scaleBudgetCost (b : Vector ℕ n) (aT : ℤ) : Costed ℤ :=
  let factor := productCost b.toList
  let out := mulIntD aT (factor.value : ℤ)
  ⟨out.value, factor.steps + out.steps + 1, factor.allocations + out.allocations⟩

theorem scaleBudgetCost_value (b : Vector ℕ n) (aT : ℤ) (bT : ℕ) (hbT : 0 < bT) :
    (scaleBudgetCost b aT).value = scaleBudget b aT bT := by
  simp [scaleBudgetCost, scaleBudget, scaledNumerator, commonDenominator,
    Nat.mul_div_cancel_left _ hbT, vector_prod]

theorem eraseIdx_size_sum_le (xs : List ℕ) (k : ℕ) :
    ((xs.eraseIdx k).map Nat.size).sum ≤ (xs.map Nat.size).sum := by
  induction xs generalizing k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k => simpa using Nat.add_le_add_left (ih k) x.size

theorem cofactorCost_size (b : Vector ℕ n) (bT B : ℕ) (v : Fin n)
    (h : bT.size + (b.toList.map Nat.size).sum ≤ B) :
    (cofactorCost b bT v).value.size ≤ B + 1 := by
  have he := eraseIdx_size_sum_le b.toList v.val
  have hp := size_list_prod_le (bT :: b.toList.eraseIdx v.val)
  simp only [List.map_cons, List.sum_cons] at hp
  simp only [cofactorCost, productCost_value, omitAt_value]
  omega

theorem cofactorCost_steps (b : Vector ℕ n) (bT B : ℕ) (v : Fin n)
    (h : bT.size + (b.toList.map Nat.size).sum ≤ B) :
    (cofactorCost b bT v).steps ≤ (n + 2) * (203 * (B + 2) ^ 2) := by
  have he := eraseIdx_size_sum_le b.toList v.val
  have hp := productCost_steps (bT :: b.toList.eraseIdx v.val) B (by
    simp only [List.map_cons, List.sum_cons]; omega)
  have ho := (omitAt_bounds v.val b.toList).1
  have hl : (b.toList.eraseIdx v.val).length ≤ n := by
    simpa only [Vector.length_toList] using List.length_eraseIdx_le b.toList v.val
  have hsq : 1 ≤ (B + 2) ^ 2 := by nlinarith
  simp only [cofactorCost, omitAt_value, List.length_cons, Vector.length_toList] at *
  nlinarith

theorem scaleFeeCost_steps (a : Vector ℤ n) (b : Vector ℕ n) (bT B : ℕ) (v : Fin n)
    (h : bT.size + (b.toList.map Nat.size).sum ≤ B) (ha : a[v].natAbs.size ≤ B) :
    (scaleFeeCost a b bT v).steps ≤ (n + 3) * (512 * (B + 2) ^ 2) := by
  have hf := cofactorCost_steps b bT B v h
  have hw := cofactorCost_size b bT B v h
  have hm := (mulIntD_bounds a[v] ((cofactorCost b bT v).value : ℤ) (B + 1)
    (by omega) (by simpa only [Int.natAbs_natCast] using hw)).1
  simp only [scaleFeeCost]
  nlinarith [show 1 ≤ (B + 2) ^ 2 by nlinarith]

theorem scaleFeesCost_steps (a : Vector ℤ n) (b : Vector ℕ n) (bT B : ℕ)
    (h : bT.size + (b.toList.map Nat.size).sum ≤ B)
    (ha : ∀ v : Fin n, a[v].natAbs.size ≤ B) :
    (scaleFeesCost a b bT).steps ≤ 1024 * (n + 1) * (n + 3) * (B + 2) ^ 2 := by
  have hv := vectorize_steps (Vector.ofFn (scaleFeeCost a b bT))
    ((n + 3) * (512 * (B + 2) ^ 2)) (by
      intro v; simpa using scaleFeeCost_steps a b bT B v h (ha v))
  simp only [scaleFeesCost]
  nlinarith [show 1 ≤ (B + 2) ^ 2 by nlinarith]

theorem scaleBudgetCost_steps (b : Vector ℕ n) (aT : ℤ) (B : ℕ)
    (h : (b.toList.map Nat.size).sum ≤ B) (ha : aT.natAbs.size ≤ B) :
    (scaleBudgetCost b aT).steps ≤ (n + 2) * (512 * (B + 2) ^ 2) := by
  have hp := productCost_steps b.toList B h
  have hw : (productCost b.toList).value.size ≤ B + 1 := by
    rw [productCost_value]
    exact (size_list_prod_le _).trans (by omega)
  have hm := (mulIntD_bounds aT ((productCost b.toList).value : ℤ) (B + 1)
    (by omega) (by simpa only [Int.natAbs_natCast] using hw)).1
  simp only [Vector.length_toList] at hp
  simp only [scaleBudgetCost]
  nlinarith [show 1 ≤ (B + 2) ^ 2 by nlinarith]

theorem omitAt_allocations (k : ℕ) (xs : List ℕ) :
    (omitAt k xs).allocations ≤ (omitAt k xs).steps := by
  induction xs generalizing k with
  | nil => simp [omitAt]
  | cons a xs ih =>
    cases k with
    | zero => simp [omitAt]
    | succ k =>
      have h := ih k
      simp only [omitAt]
      omega

theorem cofactorCost_allocations (b : Vector ℕ n) (bT : ℕ) (v : Fin n) :
    (cofactorCost b bT v).allocations ≤ (cofactorCost b bT v).steps := by
  have h₁ := omitAt_allocations v.val b.toList
  have h₂ := productCost_allocations (bT :: (omitAt v.val b.toList).value)
  simp only [cofactorCost]
  omega

theorem scaleFeeCost_allocations (a : Vector ℤ n) (b : Vector ℕ n) (bT : ℕ) (v : Fin n) :
    (scaleFeeCost a b bT v).allocations ≤ (scaleFeeCost a b bT v).steps := by
  have h₁ := cofactorCost_allocations b bT v
  have h₂ := (signed_allocations_le_steps a[v] ((cofactorCost b bT v).value : ℤ)).2.1
  simp only [scaleFeeCost]
  omega

theorem scaleFeesCost_allocations (a : Vector ℤ n) (b : Vector ℕ n) (bT : ℕ) :
    (scaleFeesCost a b bT).allocations ≤ (scaleFeesCost a b bT).steps := by
  apply vectorize_allocations_le_steps
  intro v
  simpa using scaleFeeCost_allocations a b bT v

theorem scaleBudgetCost_allocations (b : Vector ℕ n) (aT : ℤ) :
    (scaleBudgetCost b aT).allocations ≤ (scaleBudgetCost b aT).steps := by
  have h₁ := productCost_allocations b.toList
  have h₂ := (signed_allocations_le_steps aT ((productCost b.toList).value : ℤ)).2.1
  simp only [scaleBudgetCost]
  omega

end UAVProof.TreeBudgetBinaryPreprocessing
