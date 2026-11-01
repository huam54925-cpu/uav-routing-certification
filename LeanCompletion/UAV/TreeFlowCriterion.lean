import LeanCompletion.UAV.TreeFlowConnectivity
import LeanCompletion.UAV.TreeRouteDecomposition
import LeanCompletion.UAV.RootedTreeAdapter
import LeanCompletion.UAV.TreeFlowAlternating

/-! Budget-free existence criterion for finite rooted trees. -/

namespace UAVProof.TreeFlowCriterion
open TreeFlowExistence TreeFlowConnectivity TreeRouteDecomposition
open TreeFlowSymmetry TreeSupportExact SupportExactFeasibility PositiveFlowConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V]

def RouteCompatible (R : RootedTree V) (d : V → ℕ) (m : ℕ) : Prop :=
  FlowCompatible R d m ∧ ∀ v, v ≠ R.root → 0 < d v → 0 < requirement R d v

/-- Formula (5): nonnegative integer recursion, the root degree equation,
and positive parent edges for every positive-demand task are exactly sufficient. -/
theorem exists_decomposition_iff (R : RootedTree V) (d : V → ℕ) (m : ℕ) :
    (∃ x : V → V → ℕ,
      (∀ u v, ¬ R.graph.Adj u v → x u v = 0) ∧
      HasDegrees R.root d m x ∧ ExactDecomposable R.root x d m) ↔
      RouteCompatible R d m := by
  constructor
  · rintro ⟨x, hs, hd, hr⟩
    have hc := compatible_of_flow R d m x hs hd
    have hcd := canonicalFlow_has_degrees R d m hc
    have heq : x = canonicalFlow R d := tree_flow_unique R.graph R.isTree x
      (canonicalFlow R d) hs (edgeFlow_supported R _)
      (fun v => (hd.1 v).trans (hcd.1 v).symm)
      (fun v => (hd.2 v).trans (hcd.2 v).symm)
    refine ⟨hc, (canonicalFlow_connected_iff R d m hc).mp ?_⟩
    rw [← heq]
    exact exactDecomposable_connected hr
  · rintro ⟨hc, hp⟩
    have hd := canonicalFlow_has_degrees R d m hc
    refine ⟨canonicalFlow R d, edgeFlow_supported R _, hd, ?_⟩
    apply (tree_exactDecomposable_iff R.graph R.isTree R.root
      (canonicalFlow R d) d m hd (edgeFlow_supported R _)).mpr
    exact (canonicalFlow_connected_iff R d m hc).mpr hp

/-- Direct formulation with routes only: no preselected flow and no budgets. -/
theorem exists_routes_iff (R : RootedTree V) (d : V → ℕ) (m : ℕ) :
    (∃ routes : Fin m → LegalRoute R.root,
      (∀ v, v ≠ R.root → totalVisitCount Finset.univ routes v = d v) ∧
      ∀ u v, ¬ R.graph.Adj u v → totalRouteFlow Finset.univ routes u v = 0) ↔
      RouteCompatible R d m := by
  rw [← exists_decomposition_iff]
  constructor
  · rintro ⟨routes, hc, hs⟩
    exact ⟨totalRouteFlow Finset.univ routes, hs, aggregate_has_degrees d routes hc,
      routes, hc, fun _ _ => rfl⟩
  · rintro ⟨x, hs, _, routes, hc, hf⟩
    exact ⟨routes, hc, fun u v hn => (hf u v).trans (hs u v hn)⟩

/-- Public entry point taking only a finite tree and its chosen depot.
The rooted representation and decreasing rank are constructed internally. -/
theorem exists_tree_routes_iff (G : SimpleGraph V) (hG : G.IsTree)
    (depot : V) (d : V → ℕ) (m : ℕ) :
    (∃ routes : Fin m → LegalRoute depot,
      (∀ v, v ≠ depot → totalVisitCount Finset.univ routes v = d v) ∧
      ∀ u v, ¬ G.Adj u v → totalRouteFlow Finset.univ routes u v = 0) ↔
      RouteCompatible (RootedTree.ofIsTree G hG depot) d m := by
  exact exists_routes_iff (RootedTree.ofIsTree G hG depot) d m

end UAVProof.TreeFlowCriterion

#print axioms UAVProof.TreeFlowCriterion.exists_decomposition_iff
#print axioms UAVProof.TreeFlowCriterion.exists_routes_iff
#print axioms UAVProof.TreeFlowCriterion.exists_tree_routes_iff
