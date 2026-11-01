import LeanCompletion.UAV.TreeSupportExact

/-! Symmetry of conserved tree flows and budget-free exact decomposition.
Coverage is derived from exact aggregate flow, without assuming coverage. -/

namespace UAVProof.TreeFlowSymmetry
open SupportExactFeasibility TreeSupportExact

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem tree_flow_symmetric (G : SimpleGraph V) (hG : G.IsTree)
    (x : V → V → ℕ)
    (hshape : ∀ i j, ¬ G.Adj i j → x i j = 0)
    (hbalance : ∀ v, outFlow Finset.univ x v = inFlow Finset.univ x v) :
    ∀ i j, x i j = x j i := by
  have heq : x = fun i j => x j i := tree_flow_unique G hG x (fun i j => x j i)
    hshape (fun i j h => hshape j i (fun hji => h hji.symm))
    (fun i => hbalance i) (fun j => (hbalance j).symm)
  intro i j
  exact congrFun (congrFun heq i) j

/-- No service costs or budgets occur in this predicate. -/
def ExactDecomposable (depot : V) (x : V → V → ℕ) (d : V → ℕ) (m : ℕ) : Prop :=
  ∃ routes : Fin m → LegalRoute depot,
    (∀ v, v ≠ depot → totalVisitCount Finset.univ routes v = d v) ∧
    ∀ u v, totalRouteFlow Finset.univ routes u v = x u v

theorem exactFlow_implies_coverage {depot : V} {m : ℕ}
    (routes : Fin m → LegalRoute depot) (x : V → V → ℕ) (d : V → ℕ)
    (hdegrees : HasDegrees depot d m x)
    (hexact : ∀ u v, totalRouteFlow Finset.univ routes u v = x u v) :
    ∀ v, v ≠ depot → totalVisitCount Finset.univ routes v = d v := by
  have heq : totalRouteFlow Finset.univ routes = x := funext fun u => funext (hexact u)
  intro v hv
  rw [← total_outFlow_eq_visit_count Finset.univ routes v hv, heq]
  simpa [prescribedDegree, hv] using hdegrees.1 v

theorem exactDecomposable_iff_exactFlow (depot : V) (x : V → V → ℕ)
    (d : V → ℕ) (m : ℕ) (hdegrees : HasDegrees depot d m x) :
    ExactDecomposable depot x d m ↔
      ∃ routes : Fin m → LegalRoute depot,
        ∀ u v, totalRouteFlow Finset.univ routes u v = x u v := by
  constructor
  · rintro ⟨routes, _, hf⟩
    exact ⟨routes, hf⟩
  · rintro ⟨routes, hf⟩
    exact ⟨routes, exactFlow_implies_coverage routes x d hdegrees hf, hf⟩

/-- An active depot-free set must have a positive exit. Isolated zero-demand
vertices do not create a spurious connectivity requirement. -/
theorem exactDecomposable_positive_cut {depot : V} {x : V → V → ℕ}
    {d : V → ℕ} {m : ℕ} (h : ExactDecomposable depot x d m)
    (S : Finset V) (ho : depot ∉ S)
    (hactive : ∃ v ∈ S, 0 < outFlow Finset.univ x v) :
    1 ≤ outCutFlow S x := by
  obtain ⟨routes, _, hf⟩ := h
  have heq : totalRouteFlow Finset.univ routes = x := funext fun u => funext (hf u)
  rw [← heq]
  apply total_outCutFlow_ge_one_of_positive_visit Finset.univ routes S ho
  obtain ⟨v, hv, hp⟩ := hactive
  have hvo : v ≠ depot := fun h => ho (h ▸ hv)
  refine ⟨v, hv, ?_⟩
  rw [← total_outFlow_eq_visit_count Finset.univ routes v hvo, heq]
  exact hp

theorem exactDecomposable_zero_iff (depot : V) (x : V → V → ℕ) (d : V → ℕ) :
    ExactDecomposable depot x d 0 ↔ x = 0 ∧ ∀ v, v ≠ depot → d v = 0 := by
  constructor
  · rintro ⟨routes, hc, hf⟩
    constructor
    · funext u v
      simpa [totalRouteFlow] using (hf u v).symm
    · intro v hv
      simpa [totalVisitCount] using (hc v hv).symm
  · rintro ⟨rfl, hd⟩
    exact ⟨fun r => Fin.elim0 r, by intro v hv; simp [totalVisitCount, hd v hv],
      by simp [totalRouteFlow]⟩

end UAVProof.TreeFlowSymmetry

#print axioms UAVProof.TreeFlowSymmetry.tree_flow_symmetric
#print axioms UAVProof.TreeFlowSymmetry.exactDecomposable_iff_exactFlow
