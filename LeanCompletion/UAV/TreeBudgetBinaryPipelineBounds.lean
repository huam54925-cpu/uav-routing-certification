import LeanCompletion.UAV.TreeBudgetCostedCandidates
import LeanCompletion.UAV.TreeBudgetBitLength
import LeanCompletion.UAV.TreeBudgetBinaryInput

/-! Bounds for actual candidate checks, using the canonical binary input
length. In particular the absolute-value sum bounds every intermediate signed
addition, regardless of cancellation. No final-time bound is assumed. -/
namespace UAVProof.TreeBudgetBinaryPipelineBounds
open TreeBudgetBinaryCodec TreeBudgetParentArray TreeBudgetCostedCandidates
open TreeBudgetBitLength TreeBudgetVectorCandidates
variable {n : ℕ}

theorem vector_sum (H : Vector ℕ n) : H.toList.sum = ∑ i : Fin n, H[i] := by
  have he : H.toList = List.ofFn (fun i : Fin n => H[i]) := by
    simpa only [Vector.toList_ofFn] using
      congrArg Vector.toList (Vector.ofFn_getElem (xs := H)).symm
  rw [he, List.sum_ofFn]

theorem coordinate_width (I : RawInput) (H : Vector ℕ n)
    (hH : H.toList = I.multiplicities) (i : Fin n) :
    H[i].size ≤ (encodeInput I).length := by
  have hm : H[i] ∈ I.multiplicities := by
    rw [← hH]
    apply Vector.mem_toList_iff.mpr
    exact Vector.mem_iff_getElem.mpr ⟨i.val, i.isLt, by simp⟩
  have hm' : H[i].size ∈ I.multiplicities.map Nat.size :=
    List.mem_map.mpr ⟨H[i], hm, rfl⟩
  have hb := List.le_sum_of_mem hm'
  have hl := inputWeight_le_length I
  dsimp [inputWeight] at hl
  omega

theorem dimension_bound (I : RawInput) (hs : Shape I) (H : Vector ℕ n)
    (hH : H.toList = I.multiplicities) : n ≤ (encodeInput I).length := by
  have hh := congrArg List.length hH
  simp only [Vector.length_toList] at hh
  have hn := vertexCount_le_length I hs
  have hi := hs.2.1
  omega

theorem rootTerms_sum_le (P : ParentArray n) (H p : Vector ℕ n)
    (hp : ∀ i : Fin n, p[i] ≤ H[i]) : (rootTerms P p).sum ≤ H.toList.sum := by
  rw [vector_sum]
  simp only [rootTerms, List.sum_ofFn]
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> simp_all

theorem rootTerms_width (I : RawInput) (hs : Shape I) (P : ParentArray n)
    (H p : Vector ℕ n) (hH : H.toList = I.multiplicities)
    (hp : ∀ i : Fin n, p[i] ≤ H[i]) :
    (rootTerms P p).sum.size ≤ 2 * (encodeInput I).length := by
  have h := Nat.size_le_size (rootTerms_sum_le P H p hp)
  rw [hH] at h
  exact h.trans (size_input_multiplicity_sum I hs)

theorem costTerms_abs_width (I : RawInput) (hs : Shape I) (P : ParentArray n)
    (H p : Vector ℕ n) (A : Vector ℤ n) (hH : H.toList = I.multiplicities)
    (hp : ∀ i : Fin n, p[i] ≤ H[i])
    (hA : ∀ i : Fin n, A[i].natAbs.size ≤ 2 * (encodeInput I).length + 1) :
    ((costTerms P A p).map Int.natAbs).sum.size ≤ 6 * (encodeInput I).length + 4 := by
  let C := 2 ^ (4 * (encodeInput I).length + 3)
  have hcoeff (i : Fin n) :
      (A[i] + if P.parents[i] = P.root then 0 else A[P.parents[i]]).natAbs ≤ C := by
    apply (Nat.size_le.mp (show
      (A[i] + if P.parents[i] = P.root then 0 else A[P.parents[i]]).natAbs.size ≤
        4 * (encodeInput I).length + 3 from ?_)).le
    split_ifs
    · simpa only [add_zero] using (hA i).trans (by omega)
    · have h := size_signed_add A[i] A[P.parents[i]]
      have hi := hA i
      have hj := hA P.parents[i]
      omega
  have hsum : ((costTerms P A p).map Int.natAbs).sum ≤ C * H.toList.sum := by
    rw [vector_sum]
    simp only [costTerms, List.map_ofFn, List.sum_ofFn]
    calc
      _ ≤ ∑ i : Fin n, C * p[i] := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i = P.root
        · simp [hi]
        · simpa [hi, Int.natAbs_mul, Int.natAbs_natCast] using
            Nat.mul_le_mul_right p[i] (hcoeff i)
      _ = C * ∑ i : Fin n, p[i] := (Finset.mul_sum ..).symm
      _ ≤ C * ∑ i : Fin n, H[i] :=
        Nat.mul_le_mul_left C (Finset.sum_le_sum (fun i _ => hp i))
  have hw := (Nat.size_le_size hsum).trans (size_mul_le C H.toList.sum)
  have hc : C.size = 4 * (encodeInput I).length + 4 := by simp [C, Nat.size_pow]
  rw [hH] at hw
  have hm := size_input_multiplicity_sum I hs
  omega

theorem rowCheck_work_input (I : RawInput) (hs : Shape I) (P : ParentArray n)
    (Hraw H p : Vector ℕ n) (A : Vector ℤ n) (budget : ℤ)
    (hraw : Hraw.toList = I.multiplicities)
    (hH : ∀ i : Fin n, H[i] ≤ Hraw[i]) (hp : ∀ i : Fin n, p[i] ≤ Hraw[i])
    (hA : ∀ i : Fin n, A[i].natAbs.size ≤ 2 * (encodeInput I).length + 1)
    (hT : budget.natAbs.size ≤ 2 * (encodeInput I).length + 1) :
    work (rowCheck P H A budget p) ≤
      8192 * (n + 1) * (6 * (encodeInput I).length + 6) ^ 2 := by
  have hn := dimension_bound I hs Hraw hraw
  have hnsize : n.size ≤ (encodeInput I).length :=
    (Nat.size_le.mpr n.lt_two_pow_self).trans hn
  have hcoords := coordinate_width I Hraw hraw
  have hr := rootTerms_width I hs P Hraw p hraw hp
  have hc := costTerms_abs_width I hs P Hraw p A hraw hp hA
  exact rowCheck_work P H A budget p (6 * (encodeInput I).length + 4)
    (by omega) (by omega)
    (fun i => ((Nat.size_le_size (hH i)).trans (hcoords i)).trans (by omega))
    (fun i => (hA i).trans (by omega)) (hT.trans (by omega))
    (fun i => ((Nat.size_le_size (hp i)).trans (hcoords i)).trans (by omega))
    (by omega) hc

theorem candidateCost_work_input (I : RawInput) (hs : Shape I) (P : ParentArray n)
    (Hraw H : Vector ℕ n) (A : Vector ℤ n) (budget : ℤ)
    (hraw : Hraw.toList = I.multiplicities) (hH : ∀ i : Fin n, H[i] ≤ Hraw[i])
    (hA : ∀ i : Fin n, A[i].natAbs.size ≤ 2 * (encodeInput I).length + 1)
    (hT : budget.natAbs.size ≤ 2 * (encodeInput I).length + 1) :
    work (candidateCost P H A budget) ≤
      (2048 * (n + 1) ^ 2 * (6 * (encodeInput I).length + 5) +
        8192 * (n + 1) * (6 * (encodeInput I).length + 6) ^ 2 + 8) *
        (boundedVectorsV n (H.set P.root.val 0 P.root.isLt)).length := by
  apply candidateCost_work P H A budget (6 * (encodeInput I).length + 4) _ (by omega)
  · intro i
    have hh := (Nat.size_le_size (hH i)).trans (coordinate_width I Hraw hraw i)
    have ha := size_add_le H[i] 1
    norm_num at ha
    simp only [Fin.getElem_fin] at hh ha ⊢
    omega
  · intro p hp
    have hb := boundedVectorsV_mem _ p hp
    apply rowCheck_work_input I hs P Hraw H p A budget hraw hH _ hA hT
    intro i
    have hi := hb i
    simp only [Fin.getElem_fin, Vector.getElem_set] at hi
    split_ifs at hi
    · exact hi.trans (Nat.zero_le _)
    · exact hi.trans (hH i)

theorem bounded_length_stateBound (P : ParentArray n) (hP : Valid P) (H : Vector ℕ n) :
    (boundedVectorsV n (H.set P.root.val 0 P.root.isLt)).length =
      TreeBudgetMemoBounds.stateBound (toRootedTree P hP) (TreeBudgetVector.decode H) := by
  rw [boundedVectorsV_length, TreeBudgetMemoBounds.stateBound, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i = P.root
  · subst i
    simp
  · have hv : i.val ≠ P.root.val := fun h => hi (Fin.ext h)
    simp [TreeBudgetVector.decode, hi, Ne.symm hv]

theorem candidateCost_work_input_poly (I : RawInput) (hs : Shape I)
    (P : ParentArray n) (hP : Valid P) (Hraw H : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) (hraw : Hraw.toList = I.multiplicities)
    (hH : ∀ i : Fin n, H[i] ≤ Hraw[i])
    (hA : ∀ i : Fin n, A[i].natAbs.size ≤ 2 * (encodeInput I).length + 1)
    (hT : budget.natAbs.size ≤ 2 * (encodeInput I).length + 1) :
    work (candidateCost P H A budget) ≤
      310000 * ((encodeInput I).length + 1) ^ 3 *
        TreeBudgetMemoBounds.stateBound (toRootedTree P hP) (TreeBudgetVector.decode H) := by
  have hw := candidateCost_work_input I hs P Hraw H A budget hraw hH hA hT
  rw [bounded_length_stateBound P hP H] at hw
  have hn := dimension_bound I hs Hraw hraw
  have hc : 2048 * (n + 1) ^ 2 * (6 * (encodeInput I).length + 5) +
      8192 * (n + 1) * (6 * (encodeInput I).length + 6) ^ 2 + 8 ≤
      310000 * ((encodeInput I).length + 1) ^ 3 := by
    have h₁ := Nat.mul_le_mul_right (6 * (encodeInput I).length + 5)
      (Nat.mul_le_mul_left 2048 (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2))
    have h₂ := Nat.mul_le_mul_right ((6 * (encodeInput I).length + 6) ^ 2)
      (Nat.mul_le_mul_left 8192 (Nat.add_le_add_right hn 1))
    nlinarith
  exact hw.trans (Nat.mul_le_mul_right _ hc)

theorem rootCountCost_work_input (I : RawInput) (hs : Shape I) (P : ParentArray n)
    (Hraw H : Vector ℕ n) (hraw : Hraw.toList = I.multiplicities)
    (hH : ∀ i : Fin n, H[i] ≤ Hraw[i]) :
    work (rootCountCost P H) ≤ 512 * (n + 1) * (2 * (encodeInput I).length + 1) := by
  have hn := dimension_bound I hs Hraw hraw
  have hnsize : n.size ≤ (encodeInput I).length :=
    (Nat.size_le.mpr n.lt_two_pow_self).trans hn
  exact rootCountCost_work P H (2 * (encodeInput I).length) (by omega)
    (fun i => ((Nat.size_le_size (hH i)).trans
      (coordinate_width I Hraw hraw i)).trans (by omega))
    (rootTerms_width I hs P Hraw H hraw hH)

theorem normalizeCost_work_input (I : RawInput) (P : ParentArray n) (H : Vector ℕ n)
    (hH : H.toList = I.multiplicities) :
    work (normalizeCost P H) ≤ 128 * (n + 1) * ((encodeInput I).length + 1) := by
  apply copyVector_work _ (encodeInput I).length
  intro i
  have hi := coordinate_width I H hH i
  simp only [Fin.getElem_fin, Vector.getElem_set]
  split_ifs
  · simp
  · exact hi

end UAVProof.TreeBudgetBinaryPipelineBounds

#print axioms UAVProof.TreeBudgetBinaryPipelineBounds.vector_sum
#print axioms UAVProof.TreeBudgetBinaryPipelineBounds.coordinate_width
#print axioms UAVProof.TreeBudgetBinaryPipelineBounds.dimension_bound
#print axioms UAVProof.TreeBudgetBinaryPipelineBounds.rootTerms_sum_le
#print axioms UAVProof.TreeBudgetBinaryPipelineBounds.rootTerms_width
#print axioms UAVProof.TreeBudgetBinaryPipelineBounds.costTerms_abs_width
#print axioms UAVProof.TreeBudgetBinaryPipelineBounds.rowCheck_work_input
#print axioms UAVProof.TreeBudgetBinaryPipelineBounds.candidateCost_work_input
#print axioms UAVProof.TreeBudgetBinaryPipelineBounds.bounded_length_stateBound
#print axioms UAVProof.TreeBudgetBinaryPipelineBounds.candidateCost_work_input_poly
#print axioms UAVProof.TreeBudgetBinaryPipelineBounds.rootCountCost_work_input
#print axioms UAVProof.TreeBudgetBinaryPipelineBounds.normalizeCost_work_input
