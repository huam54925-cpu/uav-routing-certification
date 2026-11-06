import LeanCompletion.UAV.TreeBudgetRepresentationBridge
import LeanCompletion.UAV.TreeBudgetExamples

/-! Kernel-checked information-loss and boundary regressions for the bridge.
The good/bad families have the same input and different witness validity;
the input itself is feasible, as the good family explicitly proves. -/
namespace UAVProof.TreeBudgetRepresentationBridgeExamples

open TreeFlowExistence TreeBudgetRow TreeBudgetMatrix TreeBudgetPatterns
open TreeBudgetCertificate TreeBudgetRepresentationBridge SupportExactFeasibility
open ResourceCuts LocalVisitPairingNextCertificate

/-- Vertex 0 is the depot, 1 the hub, and 2--5 the leaves. -/
def hubGraph : SimpleGraph (Fin 6) where
  Adj u v := (u = 1 ∧ v ≠ 1) ∨ (u ≠ 1 ∧ v = 1)
  symm := by intro u v h; rcases h with h | h <;> simp_all
  loopless := ⟨fun v => by simp⟩

instance : DecidableRel hubGraph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def hubTree : RootedTree (Fin 6) where
  graph := hubGraph
  isTree := by
    classical
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨?_, ?_⟩
    · apply (SimpleGraph.connected_iff_exists_forall_reachable hubGraph).mpr
      refine ⟨1, fun w => ?_⟩
      by_cases hw : w = 1
      · subst w; exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable (show hubGraph.Adj 1 w from Or.inl ⟨rfl, hw⟩)
    · simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      have he : hubGraph.edgeFinset =
          {s((0 : Fin 6), 1), s((1 : Fin 6), 2), s((1 : Fin 6), 3),
           s((1 : Fin 6), 4), s((1 : Fin 6), 5)} := by
        ext e
        induction e using Sym2.inductionOn with
        | hf u v =>
          fin_cases u <;> fin_cases v <;>
            simp [SimpleGraph.mem_edgeFinset, hubGraph, Sym2.eq]
      rw [he]
      decide +kernel
  root := 0
  parent := ![0, 0, 1, 1, 1, 1]
  parent_root := rfl
  rank := ![2, 1, 0, 0, 0, 0]
  parent_rank := by decide +kernel
  adj_iff := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide +kernel

def orderAB : LegalRoute hubTree.root where
  visits := [1, 2, 1, 3, 1]
  visits_nonempty := by decide +kernel
  depot_not_mem := by decide +kernel
  adjacent_ne := by decide +kernel

def orderBA : LegalRoute hubTree.root where
  visits := [1, 3, 1, 2, 1]
  visits_nonempty := by decide +kernel
  depot_not_mem := by decide +kernel
  adjacent_ne := by decide +kernel

/-- The four-vertex order example is embedded in the common six-vertex tree;
the two unused leaf coordinates are zero. -/
theorem order_information_loss :
    orderAB ≠ orderBA ∧
    projectRow hubTree orderAB = ![0, 1, 1, 1, 0, 0] ∧
    projectRow hubTree orderBA = ![0, 1, 1, 1, 0, 0] ∧
    (∀ v, orderAB.visits.count v = (![0, 3, 1, 1, 0, 0] : Fin 6 → ℕ) v) ∧
    (∀ v, orderBA.visits.count v = (![0, 3, 1, 1, 0, 0] : Fin 6 → ℕ) v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hv := congrArg LegalRoute.visits h
    have hn : orderAB.visits ≠ orderBA.visits := by decide +kernel
    exact hn hv
  all_goals decide +kernel

theorem order_routes_supported :
    (∀ u v, ¬ hubTree.graph.Adj u v → routeFlow orderAB.vertices u v = 0) ∧
    (∀ u v, ¬ hubTree.graph.Adj u v → routeFlow orderBA.vertices u v = 0) := by
  change (∀ u v, ¬ hubGraph.Adj u v → routeFlow orderAB.vertices u v = 0) ∧
    (∀ u v, ¬ hubGraph.Adj u v → routeFlow orderBA.vertices u v = 0)
  decide +kernel

/-- Fees may be signed; equality follows from equal visit counts. -/
theorem order_cost_equal (s : Fin 6 → ℚ) :
    routeServiceIn orderAB Finset.univ s = routeServiceIn orderBA Finset.univ s := by
  unfold routeServiceIn
  apply Finset.sum_congr rfl
  intro v _
  rw [order_information_loss.2.2.2.1 v, order_information_loss.2.2.2.2 v]

def goodFirst : LegalRoute hubTree.root where
  visits := [1, 2, 1, 4, 1]
  visits_nonempty := by decide +kernel
  depot_not_mem := by decide +kernel
  adjacent_ne := by decide +kernel

def goodSecond : LegalRoute hubTree.root where
  visits := [1, 3, 1, 5, 1]
  visits_nonempty := by decide +kernel
  depot_not_mem := by decide +kernel
  adjacent_ne := by decide +kernel

def badSecond : LegalRoute hubTree.root where
  visits := [1, 4, 1, 5, 1]
  visits_nonempty := by decide +kernel
  depot_not_mem := by decide +kernel
  adjacent_ne := by decide +kernel

def goodFamily : Fin 2 → LegalRoute hubTree.root := ![goodFirst, goodSecond]
def badFamily : Fin 2 → LegalRoute hubTree.root := ![orderAB, badSecond]
def fees : Fin 6 → ℚ := ![0, 0, 2, 2, 1, 1]
def aggregateRow : Fin 6 → ℕ := ![0, 2, 1, 1, 1, 1]
def demands : Fin 6 → ℕ := ![0, 6, 1, 1, 1, 1]

theorem allocation_common_flow :
    (∀ u v, totalRouteFlow Finset.univ goodFamily u v = edgeFlow hubTree aggregateRow u v) ∧
    (∀ u v, totalRouteFlow Finset.univ badFamily u v = edgeFlow hubTree aggregateRow u v) := by
  decide +kernel

/-- Six visits to the hub: two initial visits plus four returns from leaves. -/
theorem allocation_common_visits :
    (∀ v, totalVisitCount Finset.univ goodFamily v = demands v) ∧
    (∀ v, totalVisitCount Finset.univ badFamily v = demands v) := by
  decide +kernel

theorem allocation_common_support :
    (∀ i u v, ¬ hubTree.graph.Adj u v → routeFlow (goodFamily i).vertices u v = 0) ∧
    (∀ i u v, ¬ hubTree.graph.Adj u v → routeFlow (badFamily i).vertices u v = 0) := by
  change (∀ i u v, ¬ hubGraph.Adj u v → routeFlow (goodFamily i).vertices u v = 0) ∧
    (∀ i u v, ¬ hubGraph.Adj u v → routeFlow (badFamily i).vertices u v = 0)
  decide +kernel

theorem allocation_costs_and_budgets :
    (∀ i, routeServiceIn (goodFamily i) Finset.univ fees = (![3, 3] : Fin 2 → ℚ) i) ∧
    (∀ i, routeServiceIn (badFamily i) Finset.univ fees = (![4, 2] : Fin 2 → ℚ) i) ∧
    (∑ i, routeServiceIn (goodFamily i) Finset.univ fees) = 6 ∧
    (∑ i, routeServiceIn (badFamily i) Finset.univ fees) = 6 ∧
    (∀ i, routeServiceIn (goodFamily i) Finset.univ fees ≤ 3) ∧
    ¬ (∀ i, routeServiceIn (badFamily i) Finset.univ fees ≤ 3) := by
  decide +kernel

/-- Even restricted to exact decompositions of this same input, no predicate of
total flow recovers every given family's budget validity. This says nothing
against deciding whether some budget-feasible decomposition exists. -/
theorem aggregate_does_not_determine_witness_budget :
    ¬ ∃ test : (Fin 6 → Fin 6 → ℕ) → Prop,
      ∀ rs : Fin 2 → LegalRoute hubTree.root,
        (∀ u v, totalRouteFlow Finset.univ rs u v = edgeFlow hubTree aggregateRow u v) →
        (∀ v, totalVisitCount Finset.univ rs v = demands v) →
        ((∀ i, routeServiceIn (rs i) Finset.univ fees ≤ 3) ↔
          test (totalRouteFlow Finset.univ rs)) := by
  rintro ⟨test, ht⟩
  have hf : totalRouteFlow Finset.univ goodFamily = totalRouteFlow Finset.univ badFamily := by
    funext u v
    exact (allocation_common_flow.1 u v).trans (allocation_common_flow.2 u v).symm
  have hg := (ht goodFamily allocation_common_flow.1 allocation_common_visits.1).mp
    allocation_costs_and_budgets.2.2.2.2.1
  rw [hf] at hg
  exact allocation_costs_and_budgets.2.2.2.2.2
    ((ht badFamily allocation_common_flow.2 allocation_common_visits.2).mpr hg)

/-- The shared instance is feasible: rejecting the bad witness does not reject
the instance, because the good family supplies a valid witness. -/
theorem good_instance_feasible :
    ExactFeasible hubTree.root (edgeFlow hubTree aggregateRow) demands 2 fees 3 := by
  exact ⟨goodFamily, fun v _ => allocation_common_visits.1 v,
    allocation_costs_and_budgets.2.2.2.2.1, allocation_common_flow.1⟩

theorem nonzero_root_reconstruction :
    ∃ r : LegalRoute hubTree.root,
      projectRow hubTree r = ![0, 1, 1, 1, 0, 0] ∧
      ∀ s, routeServiceIn r Finset.univ s = cost hubTree ![7, 1, 1, 1, 0, 0] s := by
  have ha : AncestorClosed hubTree ![7, 1, 1, 1, 0, 0] := by
    unfold AncestorClosed
    decide +kernel
  have hk : rootDegree hubTree ![7, 1, 1, 1, 0, 0] = 1 := by
    rw [← rootCount_eq]
    decide +kernel
  obtain ⟨r, _, hp, _, hc⟩ := exists_route_project_normalize hubTree _ ha hk
  refine ⟨r, hp.trans ?_, hc⟩
  decide +kernel

theorem signed_negative_budget_reconstruction :
    ∃ r : LegalRoute hubTree.root,
      projectRow hubTree r = ![0, 1, 1, 0, 0, 0] ∧
      routeServiceIn r Finset.univ ![999, -2, 1, 0, 0, 0] = -3 ∧
      routeServiceIn r Finset.univ ![999, -2, 1, 0, 0, 0] ≤ -3 := by
  have hv : RowValid hubTree ![37, 1, 1, 0, 0, 0]
      ![999, -2, 1, 0, 0, 0] (-3) ![0, 1, 1, 0, 0, 0] := by decide +kernel
  obtain ⟨r, _, hp, _, hc, hb⟩ := rowValid_exists_route hubTree _ _ _ _ hv
  refine ⟨r, hp, (hc _).trans ?_, hb⟩
  decide +kernel

/-- The route family is empty; this does not construct an empty LegalRoute.
Signed budgets are allowed in both the tree and the forward next interface. -/
theorem empty_fleet_signed_bridges (s : Fin 6 → ℚ) (T : ℚ) :
    ExactFeasible hubTree.root (edgeFlow hubTree (fun _ => 0)) (fun _ => 0) 0 s T ∧
    HasNextCertificate hubTree.root (fun _ => 0) (edgeFlow hubTree (fun _ => 0)) s T ∧
    ∃ C, checkCertificate hubTree (fun _ => 0) 0 s T C = true := by
  have he := TreeBudgetExamples.empty_fleet hubTree s T
  have hd : HasDegrees hubTree.root (fun _ => 0) 0 (edgeFlow hubTree (fun _ => 0)) := by
    constructor <;> intro v <;> simp [outFlow, inFlow, edgeFlow, prescribedDegree]
  exact ⟨he, exact_implies_next hubTree _ _ _ _ _ he,
    (exact_iff_checked_certificate hubTree _ _ _ _ _ hd).mp he⟩

end UAVProof.TreeBudgetRepresentationBridgeExamples

#print axioms UAVProof.TreeBudgetRepresentationBridgeExamples.order_information_loss
#print axioms UAVProof.TreeBudgetRepresentationBridgeExamples.order_routes_supported
#print axioms UAVProof.TreeBudgetRepresentationBridgeExamples.order_cost_equal
#print axioms UAVProof.TreeBudgetRepresentationBridgeExamples.allocation_common_flow
#print axioms UAVProof.TreeBudgetRepresentationBridgeExamples.allocation_common_visits
#print axioms UAVProof.TreeBudgetRepresentationBridgeExamples.allocation_common_support
#print axioms UAVProof.TreeBudgetRepresentationBridgeExamples.allocation_costs_and_budgets
#print axioms
  UAVProof.TreeBudgetRepresentationBridgeExamples.aggregate_does_not_determine_witness_budget
#print axioms UAVProof.TreeBudgetRepresentationBridgeExamples.good_instance_feasible
#print axioms UAVProof.TreeBudgetRepresentationBridgeExamples.nonzero_root_reconstruction
#print axioms UAVProof.TreeBudgetRepresentationBridgeExamples.signed_negative_budget_reconstruction
#print axioms UAVProof.TreeBudgetRepresentationBridgeExamples.empty_fleet_signed_bridges
