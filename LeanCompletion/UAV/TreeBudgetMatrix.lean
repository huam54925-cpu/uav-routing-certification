import LeanCompletion.UAV.TreeBudgetRow

/-! Exact service-budget feasibility via per-route tree edge multiplicities.
The root coordinate of every row is ignored. Costs may be signed. -/
namespace UAVProof.TreeBudgetMatrix
open TreeFlowExistence TreeBudgetRow TreeFlowSymmetry SupportExactFeasibility ResourceCuts
variable {V : Type*} [Fintype V] [DecidableEq V]

def MatrixFeasible (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) : Prop :=
  ∃ n : Fin m → V → ℕ,
    (∀ v, v ≠ R.root → ∑ r, n r v = h v) ∧
    (∀ r, rootDegree R (n r) = 1) ∧
    (∀ r, AncestorClosed R (n r)) ∧ (∀ r, rowCost R (n r) s ≤ T)

theorem sum_edgeFlow {I : Type*} [Fintype I] (R : RootedTree V)
    (n : I → V → ℕ) (h : V → ℕ)
    (hc : ∀ v, v ≠ R.root → ∑ r, n r v = h v) (u v : V) :
    (∑ r, edgeFlow R (n r) u v) = edgeFlow R h u v := by
  simp only [edgeFlow, Finset.sum_add_distrib]
  congr 1
  · by_cases hv : v ≠ R.root ∧ R.parent v = u
    · simp [hv, hc v hv.1]
    · simp [hv]
  · by_cases hu : u ≠ R.root ∧ R.parent u = v
    · simp [hu, hc u hu.1]
    · simp [hu]

theorem exact_implies_matrix (R : RootedTree V) (h d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ)
    (he : ExactFeasible R.root (edgeFlow R h) d m s T) : MatrixFeasible R h m s T := by
  obtain ⟨rs, _, hb, hf⟩ := he
  have hs (r : Fin m) : ∀ u v, ¬ R.graph.Adj u v → routeFlow (rs r).vertices u v = 0 :=
    fun u v hn => route_supported_of_exact _ rs hf r u v (edgeFlow_supported R h u v hn)
  refine ⟨fun r => routeRow R (rs r), ?_, ?_, ?_, ?_⟩
  · intro v hv
    simpa [totalRouteFlow, routeRow, edgeFlow_parent R h hv] using hf (R.parent v) v
  · intro r; exact routeRow_root R (rs r) (hs r)
  · intro r; exact routeRow_ancestor R (rs r) (hs r)
  · intro r
    rw [← service_of_counts R _ (rs r) (routeRow_counts R (rs r) (hs r)) s]
    exact hb r

theorem matrix_implies_exact (R : RootedTree V) (h d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hd : HasDegrees R.root d m (edgeFlow R h))
    (hm : MatrixFeasible R h m s T) : ExactFeasible R.root (edgeFlow R h) d m s T := by
  classical
  obtain ⟨n, hc, hk, ha, hb⟩ := hm
  choose rs hf hv using fun r => single_row_realization R (n r) (ha r) (hk r)
  have ht : ∀ u v, totalRouteFlow Finset.univ rs u v = edgeFlow R h u v := by
    intro u v
    simp only [totalRouteFlow, hf]
    exact sum_edgeFlow R n h hc u v
  exact ⟨rs, exactFlow_implies_coverage rs _ d hd ht,
    fun r => (service_of_counts R _ (rs r) (hv r) s).le.trans (hb r), ht⟩

theorem exact_iff_matrix (R : RootedTree V) (h d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hd : HasDegrees R.root d m (edgeFlow R h)) :
    ExactFeasible R.root (edgeFlow R h) d m s T ↔ MatrixFeasible R h m s T :=
  ⟨exact_implies_matrix R h d m s T, matrix_implies_exact R h d m s T hd⟩

theorem canonical_exact_iff_matrix (R : RootedTree V) (d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hc : FlowCompatible R d m) :
    ExactFeasible R.root (canonicalFlow R d) d m s T ↔
      MatrixFeasible R (fun v => (requirement R d v).toNat) m s T :=
  exact_iff_matrix R _ d m s T (canonicalFlow_has_degrees R d m hc)

end UAVProof.TreeBudgetMatrix

#print axioms UAVProof.TreeBudgetMatrix.exact_iff_matrix
#print axioms UAVProof.TreeBudgetMatrix.canonical_exact_iff_matrix
