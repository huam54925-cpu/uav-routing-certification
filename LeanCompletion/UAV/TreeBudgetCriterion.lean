import LeanCompletion.UAV.TreeBudgetNormalization
import LeanCompletion.UAV.TreeFlowCriterion

/-! Public budget criterion: the tree, depot, demands and fleet size are inputs;
flow compatibility is derived in the forward direction, not assumed. -/
namespace UAVProof.TreeBudgetCriterion
open TreeFlowExistence TreeBudgetMatrix TreeBudgetNormalization
open SupportExactFeasibility TreeSupportExact ResourceCuts
variable {V : Type*} [Fintype V] [DecidableEq V]

def BudgetRoutes (R : RootedTree V) (d : V → ℕ) (m : ℕ) (s : V → ℚ) (T : ℚ) : Prop :=
  ∃ rs : Fin m → LegalRoute R.root,
    (∀ v, v ≠ R.root → totalVisitCount Finset.univ rs v = d v) ∧
    (∀ r, routeServiceIn (rs r) Finset.univ s ≤ T) ∧
    ∀ u v, ¬ R.graph.Adj u v → totalRouteFlow Finset.univ rs u v = 0

theorem budget_routes_iff (R : RootedTree V) (d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) : BudgetRoutes R d m s T ↔
      FlowCompatible R d m ∧ MatrixFeasible R (fun v => (requirement R d v).toNat) m s T := by
  constructor
  · rintro ⟨rs, hc, hb, hshape⟩
    have hd := aggregate_has_degrees d rs hc
    have hcomp := compatible_of_flow R d m _ hshape hd
    have hcd := canonicalFlow_has_degrees R d m hcomp
    have he := tree_flow_unique R.graph R.isTree _ (canonicalFlow R d)
      hshape (edgeFlow_supported R _) (fun v => (hd.1 v).trans (hcd.1 v).symm)
      (fun v => (hd.2 v).trans (hcd.2 v).symm)
    exact ⟨hcomp, exact_implies_matrix R _ d m s T
      ⟨rs, hc, hb, fun u v => congrFun (congrFun he u) v⟩⟩
  · rintro ⟨hcomp, hm⟩
    obtain ⟨rs, hc, hb, hf⟩ := (canonical_exact_iff_matrix R d m s T hcomp).mpr hm
    exact ⟨rs, hc, hb, fun u v hn => (hf u v).trans (edgeFlow_supported R _ u v hn)⟩

theorem budget_routes_iff_relaxed (R : RootedTree V) (d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hs : ∀ v, v ≠ R.root → 0 ≤ s v) : BudgetRoutes R d m s T ↔
      FlowCompatible R d m ∧ RelaxedMatrixFeasible R (fun v => (requirement R d v).toNat) m s T := by
  rw [budget_routes_iff]
  constructor
  · rintro ⟨hc, hm⟩
    exact ⟨hc, (matrix_iff_relaxed R _ d m s T (canonicalFlow_has_degrees R d m hc) hs).mp hm⟩
  · rintro ⟨hc, hm⟩
    exact ⟨hc, (matrix_iff_relaxed R _ d m s T (canonicalFlow_has_degrees R d m hc) hs).mpr hm⟩

theorem exists_tree_budget_routes_iff (G : SimpleGraph V) (hG : G.IsTree)
    (o : V) (d : V → ℕ) (m : ℕ) (s : V → ℚ) (T : ℚ) :
    (∃ rs : Fin m → LegalRoute o,
      (∀ v, v ≠ o → totalVisitCount Finset.univ rs v = d v) ∧
      (∀ r, routeServiceIn (rs r) Finset.univ s ≤ T) ∧
      ∀ u v, ¬ G.Adj u v → totalRouteFlow Finset.univ rs u v = 0) ↔
    let R := RootedTree.ofIsTree G hG o
    FlowCompatible R d m ∧ MatrixFeasible R (fun v => (requirement R d v).toNat) m s T := by
  exact budget_routes_iff (RootedTree.ofIsTree G hG o) d m s T

end UAVProof.TreeBudgetCriterion

#print axioms UAVProof.TreeBudgetCriterion.exists_tree_budget_routes_iff
#print axioms UAVProof.TreeBudgetCriterion.budget_routes_iff_relaxed
