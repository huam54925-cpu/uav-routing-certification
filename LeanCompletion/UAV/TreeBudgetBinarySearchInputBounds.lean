import LeanCompletion.UAV.TreeBudgetBinarySearch
import LeanCompletion.UAV.TreeBudgetBinaryInput
import LeanCompletion.UAV.TreeBudgetBitLength

/-! Search-phase bounds whose size parameter is the real input encoding length.
These bounds do not include the frontend, candidate generation or output. -/
namespace UAVProof.TreeBudgetBinarySearchInputBounds
open TreeBudgetBinaryInput TreeBudgetBinaryCodec TreeBudgetBinarySearch
open TreeBudgetCostedSearchBounds TreeBudgetVector TreeFlowExistence TreeBudgetPatterns
open TreeBudgetMemoBounds
variable {n : ℕ}

theorem decoded_coordinate_width (I : RawInput) (J : Input)
    (h : decodeRaw I = some J) (i : Fin J.n) : J.H[i].size ≤ (encodeInput I).length := by
  have hf := decodeRaw_fields I J h
  have hm : J.H[i] ∈ I.multiplicities := by
    rw [← hf.2.2.1]
    apply Vector.mem_toList_iff.mpr
    exact Vector.mem_iff_getElem.mpr ⟨i.val, i.isLt, by simp⟩
  have hs := List.le_sum_of_mem
    (List.mem_map.mpr ⟨J.H[i], hm, rfl⟩ : J.H[i].size ∈ I.multiplicities.map Nat.size)
  have hl := inputWeight_le_length I
  dsimp [inputWeight] at hl
  omega

theorem normalize_width (R : RootedTree (Fin n)) (H : Vector ℕ n) (ell : ℕ)
    (hH : ∀ i : Fin n, H[i].size ≤ ell) :
    ∀ i : Fin n, (TreeBudgetVector.normalize R H)[i].size ≤ ell := by
  intro i
  change (decode (TreeBudgetVector.normalize R H) i).size ≤ ell
  rw [decode_normalize]
  by_cases hi : i = R.root
  · simp [TreeBudgetPatterns.normalize, hi]
  · simpa [TreeBudgetPatterns.normalize, hi] using hH i

theorem rootCount_width (R : RootedTree (Fin n)) (H : Vector ℕ n) (ell : ℕ)
    (hn : n ≤ ell) (hH : ∀ i : Fin n, H[i].size ≤ ell) :
    (rootCount R (decode H)).size ≤ 2 * ell := by
  have hp : 0 < 2 ^ ell := by positivity
  have hn' : n < 2 ^ ell := hn.trans_lt (Nat.lt_two_pow_self (n := ell))
  have hc : (children R R.root).card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ (children R R.root))
  have hb : rootCount R (decode H) ≤ n * 2 ^ ell := by
    calc
      _ ≤ ∑ _v ∈ children R R.root, 2 ^ ell :=
        Finset.sum_le_sum (fun i _ => (Nat.size_le.mp (hH i)).le)
      _ = (children R R.root).card * 2 ^ ell := by simp
      _ ≤ n * 2 ^ ell := Nat.mul_le_mul_right _ hc
  apply Nat.size_le.mpr
  calc
    _ ≤ n * 2 ^ ell := hb
    _ < 2 ^ ell * 2 ^ ell := Nat.mul_lt_mul_of_pos_right hn' hp
    _ = 2 ^ (2 * ell) := by rw [← pow_add]; congr 1; omega

set_option maxRecDepth 2048 in
/-- The constant is uniform. This measures intrinsic search bit-cell work,
not all phases of the binary-input algorithm or Lean runtime. -/
theorem decoded_search_work (I : RawInput) (J : Input) (h : decodeRaw I = some J)
    (R : RootedTree (Fin J.n)) (A : Vector ℤ J.n) (AT : ℤ)
    (s : Fin J.n → ℚ) (T D : ℚ) (hD : 0 < D)
    (hA : ∀ v : Fin J.n, (A[v] : ℚ) = D * s v) (hAT : (AT : ℚ) = D * T) :
    (initialCost (backend J.n) R J.H A AT).work ≤
      15000 * ((encodeInput I).length + 1) ^ 2 *
        (stateBound R (TreeBudgetPatterns.normalize R (decode J.H)) + 1) ^ 3 := by
  let ell := (encodeInput I).length
  have hn : J.n ≤ ell := by
    rw [(decodeRaw_fields I J h).1]
    exact vertexCount_le_length I (decodeRaw_shape I J h)
  have hH := normalize_width R J.H ell (decoded_coordinate_width I J h)
  have hk := rootCount_width R (TreeBudgetVector.normalize R J.H) ell hn hH
  have hw := initial_search_work R J.H A AT s T D hD hA hAT (2 * ell) hk
    (fun i => (hH i).trans (by omega))
  have hcoef : (1024 * (J.n + 1) * (2 * ell + 1) + 8) * 7 ≤
      15000 * (ell + 1) ^ 2 := by
    have hm := Nat.mul_le_mul_right (2 * ell + 1) (Nat.add_le_add_right hn 1)
    nlinarith only [hm]
  exact hw.trans (Nat.mul_le_mul_right _ hcoef)

end UAVProof.TreeBudgetBinarySearchInputBounds
