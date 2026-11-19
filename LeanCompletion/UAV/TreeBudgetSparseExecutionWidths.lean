import LeanCompletion.UAV.TreeBudgetSparseWeightedCost
import LeanCompletion.UAV.TreeBudgetBinaryExecutionBounds
import LeanCompletion.UAV.TreeBudgetSparseCostedParsing

/-! Bounds for arbitrary decoded certificate rows, not only valid patterns.
Signed intermediate costs are bounded by the sum of absolute values. -/
namespace UAVProof.TreeBudgetSparseExecutionWidths
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetSparsePrefixBounds
open TreeBudgetSparseWeightedCost TreeBudgetCostedCandidates TreeBudgetParentArray

theorem size_sum_fields (xs : List ℕ) : xs.sum.size ≤ (xs.map Nat.size).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have := TreeBudgetSparsePrefixBounds.size_add_le x xs.sum
    simp only [List.sum_cons, List.map_cons]
    omega

theorem size_sum_uniform (xs : List ℕ) (B : ℕ) (h : ∀ x ∈ xs, x.size ≤ B) :
    xs.sum.size ≤ xs.length * B := by
  apply (size_sum_fields xs).trans
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem rootTerms_width {n : ℕ} (P : ParentArray n) (p : Vector ℕ n) (B : ℕ)
    (h : ∀ v : Fin n, p[v].size ≤ B) : (rootTerms P p).sum.size ≤ n * B := by
  have ht := size_sum_uniform (rootTerms P p) B (by
    intro x hx
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hx
    split_ifs <;> simp_all)
  simpa [rootTerms] using ht

theorem costTerms_width {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (p : Vector ℕ n) (F B : ℕ)
    (ha : ∀ v : Fin n, A[v].natAbs.size ≤ F) (hp : ∀ v : Fin n, p[v].size ≤ B) :
    ((costTerms P A p).map Int.natAbs).sum.size ≤ n * (2 * F + B) := by
  have ht := size_sum_uniform ((costTerms P A p).map Int.natAbs) (2 * F + B) (by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hz
    split_ifs with hr hparent
    · simp
    · have hm : (A[v].natAbs * p[v]).size ≤ F + B :=
        (TreeBudgetSparsePrefixBounds.size_mul_le _ _).trans (Nat.add_le_add (ha v) (hp v))
      simpa only [add_zero, Int.natAbs_mul, Int.natAbs_natCast] using
        hm.trans (by omega : F + B ≤ 2 * F + B)
    · have hs := (Nat.size_le_size (Int.natAbs_add_le A[v] A[P.parents[v]])).trans
        (TreeBudgetSparsePrefixBounds.size_add_le _ _)
      have hm := TreeBudgetSparsePrefixBounds.size_mul_le
        (A[v] + A[P.parents[v]]).natAbs p[v]
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
      have := ha v
      have := ha (P.parents[v])
      have := hp v
      omega)
  simpa [costTerms] using ht

theorem decoded_fields {n : ℕ} (wire : Bits)
    (C : TreeBudgetCertificate.Certificate (Fin n)) (h : decodeCertificate n wire = some C) :
    C.size ≤ wire.length ∧ (∀ i, (C.count i).size ≤ wire.length) ∧
      (∀ i v, (C.row i v).size ≤ wire.length) := by
  have ho := decoded_occupation wire C h
  have hb := occupied_field_bits wire (toRaw C) ho
  have hn := occupied_entry_count wire (toRaw C) ho
  have hi (i : Fin C.size) : fieldBits (C.count i, List.ofFn (C.row i)) ≤ prefixBits (toRaw C) :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩)
  refine ⟨by simpa using hn, ?_, ?_⟩
  · intro i
    have := hi i
    dsimp only [fieldBits] at this
    omega
  · intro i v
    have hx : (C.row i v).size ≤ ((List.ofFn (C.row i)).map Nat.size).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨v, rfl⟩, rfl⟩)
    have := hi i
    dsimp only [fieldBits] at this
    omega

/-- Uniform row bound, with no `Valid`, coordinate-bound, or budget premise. -/
theorem arbitrary_row_work {n : ℕ} (P : ParentArray n) (H : Vector ℕ n)
    (A : Vector ℤ n) (T : ℤ) (p : Vector ℕ n) (N : ℕ)
    (hn : n ≤ N) (hH : ∀ v : Fin n, H[v].size ≤ N)
    (hA : ∀ v : Fin n, A[v].natAbs.size ≤ 2 * N + 1)
    (hT : T.natAbs.size ≤ 2 * N + 1) (hp : ∀ v : Fin n, p[v].size ≤ N) :
    work (rowCheck P H A T p) ≤ 524288 * (N + 1) ^ 5 := by
  let B := 6 * (N + 1) ^ 2
  have hNB : N ≤ B := by dsimp [B]; nlinarith
  have hFB : 2 * N + 1 ≤ B := by dsimp [B]; nlinarith
  have hr := rootTerms_width P p N hp
  have hc := costTerms_width P A p (2 * N + 1) N hA hp
  have hm₁ := Nat.mul_le_mul_right N hn
  have hm₂ := Nat.mul_le_mul_right (2 * (2 * N + 1) + N) hn
  have ht := rowCheck_work P H A T p B (by dsimp [B]; nlinarith)
    ((TreeBudgetCostedCodec.nat_size_le n).trans (hn.trans hNB))
    (fun v => (hH v).trans hNB) (fun v => (hA v).trans hFB) (hT.trans hFB)
    (fun v => (hp v).trans hNB) (by dsimp [B]; nlinarith) (by dsimp [B]; nlinarith)
  have hB : B + 2 ≤ 8 * (N + 1) ^ 2 := by dsimp [B]; nlinarith
  calc
    _ ≤ 8192 * (n + 1) * (B + 2) ^ 2 := ht
    _ ≤ 8192 * (N + 1) * (8 * (N + 1) ^ 2) ^ 2 := by gcongr
    _ = _ := by ring

end UAVProof.TreeBudgetSparseExecutionWidths
