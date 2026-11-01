import LeanCompletion.UAV.RootedTreeAdapter
import LeanCompletion.UAV.PositiveFlowConnectivity
import LeanCompletion.UAV.RouteSplice
import LeanCompletion.UAV.TreeFlowCriterion

/-! Kernel-checked guards for the distinction between compatible tree flows
and depot-route decompositions. -/

namespace UAVProof.TreeFlowExamples
open TreeFlowExistence TreeFlowSymmetry PositiveFlowConnectivity

def pathFour : RootedTree (Fin 4) where
  graph := SimpleGraph.pathGraph 4
  isTree := by
    classical
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨SimpleGraph.pathGraph_connected 3, ?_⟩
    simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    have he : (SimpleGraph.pathGraph 4).edgeFinset =
        {s((0 : Fin 4), 1), s((1 : Fin 4), 2), s((2 : Fin 4), 3)} := by
      ext e
      induction e using Sym2.inductionOn with
      | hf u v =>
        fin_cases u <;> fin_cases v <;>
          simp [SimpleGraph.mem_edgeFinset, SimpleGraph.pathGraph_adj, Sym2.eq]
    rw [he]
    decide +kernel
  root := 0
  parent := ![0, 0, 1, 2]
  parent_root := rfl
  rank := fun v => 3 - v.val
  parent_rank := by decide +kernel
  adj_iff := by
    intro u v
    rw [SimpleGraph.pathGraph_adj]
    fin_cases u <;> fin_cases v <;> decide

theorem pathFour_children :
    pathFour.children 0 = {1} ∧ pathFour.children 1 = {2} ∧
    pathFour.children 2 = {3} ∧ pathFour.children 3 = ∅ := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext v <;> fin_cases v <;>
    simp [RootedTree.children, pathFour]

theorem disconnected_requirements :
    requirement pathFour (fun _ => 1) 1 = 1 ∧
    requirement pathFour (fun _ => 1) 2 = 0 ∧
    requirement pathFour (fun _ => 1) 3 = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := pathFour_children
  have r3 : requirement pathFour (fun _ => 1) 3 = 1 := by
    rw [requirement_eq, h3]; simp
  have r2 : requirement pathFour (fun _ => 1) 2 = 0 := by
    rw [requirement_eq, h2]; simp [r3]
  have r1 : requirement pathFour (fun _ => 1) 1 = 1 := by
    rw [requirement_eq, h1]; simp [r2]
  exact ⟨r1, r2, r3⟩

theorem disconnected_compatible : FlowCompatible pathFour (fun _ => 1) 1 := by
  obtain ⟨h1, h2, h3⟩ := disconnected_requirements
  constructor
  · intro v hv
    fin_cases v <;> simp_all [pathFour]
  · change (1 : ℤ) = ∑ w ∈ pathFour.children 0, requirement pathFour (fun _ => 1) w
    rw [pathFour_children.1]
    simpa using h1.symm

theorem disconnected_positive_parent_fails :
    ¬ (∀ v : Fin 4, v ≠ pathFour.root →
      0 < (1 : ℕ) → 0 < requirement pathFour (fun _ => 1) v) := by
  intro h
  have hp := h 2 (by decide) (by decide)
  rw [disconnected_requirements.2.1] at hp
  omega

/-- The recursion uses integers: a negative parent multiplicity is rejected. -/
theorem negative_requirement_is_rejected :
    requirement pathFour ![0, 0, 0, 1] 2 = -1 ∧
      ¬ FlowCompatible pathFour ![0, 0, 0, 1] 1 := by
  have r3 : requirement pathFour ![0, 0, 0, 1] 3 = 1 := by
    rw [requirement_eq, pathFour_children.2.2.2]
    simp
  have r2 : requirement pathFour ![0, 0, 0, 1] 2 = -1 := by
    rw [requirement_eq, pathFour_children.2.2.1]
    simp [r3]
  refine ⟨r2, ?_⟩
  intro h
  have hp := h.1 2 (by decide)
  rw [r2] at hp
  omega

theorem zero_demand_compatible {V : Type*} [Fintype V] [DecidableEq V]
    (R : RootedTree V) : FlowCompatible R (fun _ => 0) 0 := by
  apply compatible_of_flow R (fun _ => 0) 0 (fun _ _ => 0)
  · simp
  · constructor <;> intro v <;>
      simp [SupportExactFeasibility.prescribedDegree, outFlow, inFlow]

/-- No positive service demand is hidden by the empty fleet. -/
theorem zero_flow_decomposable {V : Type*} [Fintype V] [DecidableEq V] (o : V) :
    ExactDecomposable o (fun _ _ => 0) (fun _ => 0) 0 := by
  refine ⟨fun r => Fin.elim0 r, ?_, ?_⟩
  · simp [totalVisitCount]
  · simp [totalRouteFlow]

/-- The depot's own demand is ignored, and a depot-only instance has no routes. -/
theorem singleton_decomposition_iff (d : Fin 1 → ℕ) (m : ℕ) :
    ExactDecomposable (0 : Fin 1) (fun _ _ => 0) d m ↔ m = 0 := by
  constructor
  · rintro ⟨rs, _, hf⟩
    have heq : totalRouteFlow Finset.univ rs = (fun _ _ => 0) :=
      funext fun i => funext (hf i)
    have h := total_outFlow_depot_eq_card Finset.univ rs
    rw [heq] at h
    simpa [outFlow] using h.symm
  · intro h
    subst m
    refine ⟨fun r => Fin.elim0 r, ?_, ?_⟩
    · intro v hv
      fin_cases v
      exact (hv rfl).elim
    · simp [totalRouteFlow]

def repeatedBase : LegalRoute (0 : Fin 3) where
  visits := [1, 2, 1]
  visits_nonempty := by decide
  depot_not_mem := by decide
  adjacent_ne := by decide +kernel

def repeatedInsert : LegalRoute (0 : Fin 3) :=
  RouteSplice.insertExcursion repeatedBase [] [2, 1] 1 2 rfl (by decide) (by decide)

/-- The inserted vertex 2 was already present; depot edges are unchanged. -/
theorem repeated_vertex_insertion :
    repeatedInsert.visits = [1, 2, 1, 2, 1] ∧
    routeFlow repeatedInsert.vertices 0 1 = 1 ∧
    routeFlow repeatedInsert.vertices 1 0 = 1 ∧
    routeFlow repeatedInsert.vertices 1 2 = 2 ∧
    routeFlow repeatedInsert.vertices 2 1 = 2 := by
  decide +kernel

theorem disconnected_no_routes :
    ¬ ∃ rs : Fin 1 → LegalRoute pathFour.root,
      (∀ v, v ≠ pathFour.root → totalVisitCount Finset.univ rs v = 1) ∧
      ∀ u v, ¬ pathFour.graph.Adj u v → totalRouteFlow Finset.univ rs u v = 0 := by
  intro h
  have hc := (TreeFlowCriterion.exists_routes_iff pathFour (fun _ => 1) 1).mp h
  exact disconnected_positive_parent_fails hc.2

theorem connected_requirements :
    requirement pathFour ![0, 2, 2, 1] 1 = 1 ∧
    requirement pathFour ![0, 2, 2, 1] 2 = 1 ∧
    requirement pathFour ![0, 2, 2, 1] 3 = 1 := by
  have r3 : requirement pathFour ![0, 2, 2, 1] 3 = 1 := by
    rw [requirement_eq, pathFour_children.2.2.2]; simp
  have r2 : requirement pathFour ![0, 2, 2, 1] 2 = 1 := by
    rw [requirement_eq, pathFour_children.2.2.1]; simp [r3]
  have r1 : requirement pathFour ![0, 2, 2, 1] 1 = 1 := by
    rw [requirement_eq, pathFour_children.2.1]; simp [r2]
  exact ⟨r1, r2, r3⟩

theorem connected_routes_exist :
    ∃ rs : Fin 1 → LegalRoute pathFour.root,
      (∀ v, v ≠ pathFour.root → totalVisitCount Finset.univ rs v = ![0, 2, 2, 1] v) ∧
      ∀ u v, ¬ pathFour.graph.Adj u v → totalRouteFlow Finset.univ rs u v = 0 := by
  apply (TreeFlowCriterion.exists_routes_iff pathFour ![0, 2, 2, 1] 1).mpr
  obtain ⟨h1, h2, h3⟩ := connected_requirements
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v hv
    fin_cases v <;> simp_all [pathFour]
  · change (1 : ℤ) = ∑ w ∈ pathFour.children 0, requirement pathFour ![0, 2, 2, 1] w
    rw [pathFour_children.1]
    simpa using h1.symm
  · intro v hv hd
    fin_cases v <;> simp_all [pathFour]

end UAVProof.TreeFlowExamples

#print axioms UAVProof.TreeFlowExamples.disconnected_compatible
#print axioms UAVProof.TreeFlowExamples.disconnected_positive_parent_fails
#print axioms UAVProof.TreeFlowExamples.negative_requirement_is_rejected
#print axioms UAVProof.TreeFlowExamples.zero_demand_compatible
#print axioms UAVProof.TreeFlowExamples.zero_flow_decomposable
#print axioms UAVProof.TreeFlowExamples.singleton_decomposition_iff
#print axioms UAVProof.TreeFlowExamples.repeated_vertex_insertion
#print axioms UAVProof.TreeFlowExamples.disconnected_no_routes
#print axioms UAVProof.TreeFlowExamples.connected_routes_exist
