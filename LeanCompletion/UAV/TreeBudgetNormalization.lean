import LeanCompletion.UAV.TreeBudgetMatrix

/-! Splitting rows with arbitrary depot degree preserves budgets for
nonnegative non-depot service fees. No sign assumption on T is needed. -/
namespace UAVProof.TreeBudgetNormalization
open TreeFlowExistence TreeBudgetRow TreeBudgetMatrix TreeFlowSymmetry
open SupportExactFeasibility ResourceCuts
variable {V : Type*} [Fintype V] [DecidableEq V]

def RelaxedMatrixFeasible (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) : Prop :=
  ∃ n : Fin m → V → ℕ,
    (∀ v, v ≠ R.root → ∑ r, n r v = h v) ∧
    (∀ r, AncestorClosed R (n r)) ∧ (∀ r, rowCost R (n r) s ≤ T)

theorem service_nonneg {o : V} (s : V → ℚ)
    (hs : ∀ v, v ≠ o → 0 ≤ s v) (r : LegalRoute o) :
    0 ≤ routeServiceIn r Finset.univ s := by
  apply Finset.sum_nonneg
  intro v _
  by_cases hv : v = o
  · subst v; simp [List.count_eq_zero.mpr r.depot_not_mem]
  · exact mul_nonneg (hs v hv) (Nat.cast_nonneg _)

theorem relaxed_implies_exact (R : RootedTree V) (h d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hd : HasDegrees R.root d m (edgeFlow R h))
    (hs : ∀ v, v ≠ R.root → 0 ≤ s v)
    (hm : RelaxedMatrixFeasible R h m s T) :
    ExactFeasible R.root (edgeFlow R h) d m s T := by
  classical
  obtain ⟨n, hn, ha, hb⟩ := hm
  choose rs hc hf using fun r => row_decomposable R (n r) (ha r)
  let I := (r : Fin m) × Fin (rootDegree R (n r))
  let fleet : I → LegalRoute R.root := fun i => rs i.1 i.2
  have hcard : Fintype.card I = m := by
    simp only [I, Fintype.card_sigma, Fintype.card_fin]
    change (∑ r, ∑ w ∈ R.children R.root, n r w) = m
    rw [Finset.sum_comm]
    have hmroot := hd.1 R.root
    rw [edgeFlow_out] at hmroot
    simp [prescribedDegree] at hmroot
    calc
      _ = ∑ w ∈ R.children R.root, h w := Finset.sum_congr rfl
        (fun w hw => hn w ((R.mem_children R.root w).mp hw).1)
      _ = m := hmroot
  have hflow : ∀ u v, totalRouteFlow Finset.univ fleet u v = edgeFlow R h u v := by
    intro u v
    change (∑ i : I, routeFlow (rs i.1 i.2).vertices u v) = _
    rw [Fintype.sum_sigma]
    change (∑ r, totalRouteFlow Finset.univ (rs r) u v) = _
    simp only [hf]
    exact sum_edgeFlow R n h hn u v
  have hbudget : ∀ i : I, routeServiceIn (fleet i) Finset.univ s ≤ T := by
    intro i
    calc
      _ ≤ ∑ j, routeServiceIn (rs i.1 j) Finset.univ s :=
        Finset.single_le_sum (fun j _ => service_nonneg s hs (rs i.1 j)) (Finset.mem_univ i.2)
      _ = rowCost R (n i.1) s := sum_service_of_exact R (n i.1) (rs i.1) (hc i.1) s
      _ ≤ T := hb i.1
  let e : Fin m ≃ I := Fintype.equivOfCardEq (by simpa using hcard.symm)
  have he : ∀ u v, totalRouteFlow Finset.univ (fun r => fleet (e r)) u v = edgeFlow R h u v := by
    intro u v
    calc
      _ = totalRouteFlow Finset.univ fleet u v := by
        simpa only [totalRouteFlow] using Equiv.sum_comp e (fun i => routeFlow (fleet i).vertices u v)
      _ = _ := hflow u v
  exact ⟨fun r => fleet (e r), exactFlow_implies_coverage _ _ d hd he,
    fun r => hbudget (e r), he⟩

theorem matrix_iff_relaxed (R : RootedTree V) (h d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hd : HasDegrees R.root d m (edgeFlow R h))
    (hs : ∀ v, v ≠ R.root → 0 ≤ s v) :
    MatrixFeasible R h m s T ↔ RelaxedMatrixFeasible R h m s T := by
  constructor
  · rintro ⟨n, hc, _, ha, hb⟩; exact ⟨n, hc, ha, hb⟩
  · intro hrel
    exact exact_implies_matrix R h d m s T (relaxed_implies_exact R h d m s T hd hs hrel)

theorem canonical_exact_iff_relaxed (R : RootedTree V) (d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hc : FlowCompatible R d m)
    (hs : ∀ v, v ≠ R.root → 0 ≤ s v) :
    ExactFeasible R.root (canonicalFlow R d) d m s T ↔
      RelaxedMatrixFeasible R (fun v => (requirement R d v).toNat) m s T :=
  (canonical_exact_iff_matrix R d m s T hc).trans
    (matrix_iff_relaxed R _ d m s T (canonicalFlow_has_degrees R d m hc) hs)

end UAVProof.TreeBudgetNormalization

#print axioms UAVProof.TreeBudgetNormalization.matrix_iff_relaxed
#print axioms UAVProof.TreeBudgetNormalization.canonical_exact_iff_relaxed
