import LeanCompletion.UAV.VisitCopyLift
import LeanCompletion.UAV.FixedFlowObstruction

/-!
# Copy-level obstruction and an explicit violated service cut

Target dependency: uav-routing-certification commit
f7147cf13d043537fc1a2f2d361eee251b3685e6.

Status: proof candidate; not yet compiled in the authoring environment.
Uses the existing service-only model; no travel costs are introduced.
Only closed finite certificates use `decide +kernel`.
-/

namespace UAVProof.CopyLiftObstruction

open ResourceCuts VisitCopyLift

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Structural conditions only: the rounded service cuts are deliberately absent. -/
structure IsStructuralCopyLift
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ) : Prop where
  project_exact : ∀ u v,
    projectFlow (project depot required) y u v = x u v
  out_one : ∀ c : VisitCopy depot required, c ≠ none →
    outFlow Finset.univ y c = 1
  in_one : ∀ c : VisitCopy depot required, c ≠ none →
    inFlow Finset.univ y c = 1
  positive_cuts : ∀ S : Finset (VisitCopy depot required),
    S.Nonempty → none ∉ S → 1 ≤ outCutFlow S y

/-- A reusable contraposition of the established lift/decomposition equivalence. -/
theorem no_serviceCopyLift_of_no_exact_decomposition
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (hloop : ∀ v, x v v = 0)
    (service : V → ℚ) (T : ℚ)
    (hservice : ∀ v, 0 ≤ service v) (hT : 0 < T)
    (hno : ¬ ∃ routes :
        Fin (outFlow Finset.univ x depot) → LegalRoute depot,
      (∀ v, v ≠ depot →
        totalVisitCount Finset.univ routes v = required v) ∧
      (∀ u v, totalRouteFlow Finset.univ routes u v = x u v) ∧
      (∀ r, routeServiceIn (routes r) Finset.univ service ≤ T)) :
    ¬ ∃ y : VisitCopy depot required → VisitCopy depot required → ℕ,
      IsServiceCopyLift depot required x service T y := by
  intro hlift
  exact hno ((serviceCopyLift_iff_exact_decomposition
    depot required x hloop service T hservice hT).mp hlift)

/-- Every structural lift has some violated cut. The subset may depend on y.
This does not assert one universal subset violating every lift. -/
theorem exists_violated_copy_cut_of_no_serviceCopyLift
    (depot : V) (required : V → ℕ) (x : V → V → ℕ)
    (service : V → ℚ) (T : ℚ)
    (hno : ¬ ∃ z : VisitCopy depot required → VisitCopy depot required → ℕ,
      IsServiceCopyLift depot required x service T z)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (hy : IsStructuralCopyLift depot required x y) :
    ∃ S : Finset (VisitCopy depot required),
      S.Nonempty ∧ none ∉ S ∧
      (outCutFlow S y : ℤ) <
        Int.ceil ((∑ c ∈ S, copyService depot required service c) / T) := by
  classical
  by_contra hbad
  apply hno
  refine ⟨y, {
    project_exact := hy.project_exact
    out_one := hy.out_one
    in_one := hy.in_one
    positive_cuts := hy.positive_cuts
    rounded_cuts := ?_
  }⟩
  intro S hS hdepot
  by_contra hcut
  exact hbad ⟨S, hS, hdepot, lt_of_not_ge hcut⟩

end General

namespace FourNode

open FixedFlowObstruction

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem service_nonneg : ∀ v : Node, 0 ≤ service v := by
  decide +kernel

/-- Bridge the old counterexample's task set to the new theorem's univ budget. -/
theorem task_service_le_univ (r : LegalRoute (0 : Node)) :
    routeServiceIn r tasks service ≤ routeServiceIn r Finset.univ service := by
  unfold routeServiceIn
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ tasks)
    (fun i _ _ => mul_nonneg (service_nonneg i) (Nat.cast_nonneg _))

/-- The original counterexample, with exactly the interface of the lift theorem. -/
theorem no_budget_exact_family :
    ¬ ∃ routes :
        Fin (outFlow Finset.univ fixedFlow (0 : Node)) → LegalRoute (0 : Node),
      (∀ v, v ≠ (0 : Node) →
        totalVisitCount Finset.univ routes v = required v) ∧
      (∀ u v, totalRouteFlow Finset.univ routes u v = fixedFlow u v) ∧
      (∀ r, routeServiceIn (routes r) Finset.univ service ≤ capacity) := by
  rintro ⟨routes, _hcounts, hflow, hbudget⟩
  have hexact : totalRouteFlow Finset.univ routes = fixedFlow := by
    funext u v
    exact hflow u v
  exact FixedFlowObstruction.no_exact_decomposition Finset.univ routes hexact
    (fun r _ => (task_service_le_univ (routes r)).trans (hbudget r))

theorem no_service_copy_lift :
    ¬ ∃ y : VisitCopy (0 : Node) required → VisitCopy (0 : Node) required → ℕ,
      IsServiceCopyLift (0 : Node) required fixedFlow service capacity y := by
  exact no_serviceCopyLift_of_no_exact_decomposition
    (0 : Node) required fixedFlow fixed_flow_aggregate_conditions.noDiagonal
    service capacity service_nonneg (by decide +kernel) no_budget_exact_family

/-- Canonical occurrence copies, not an unrelated auxiliary graph. -/
abbrev Copy := VisitCopy (0 : Node) required

theorem every_structural_lift_has_violated_cut
    (y : Copy → Copy → ℕ)
    (hy : IsStructuralCopyLift (0 : Node) required fixedFlow y) :
    ∃ S : Finset Copy, S.Nonempty ∧ none ∉ S ∧
      (outCutFlow S y : ℤ) <
        Int.ceil ((∑ c ∈ S, copyService (0 : Node) required service c) / capacity) := by
  exact exists_violated_copy_cut_of_no_serviceCopyLift
    (0 : Node) required fixedFlow service capacity no_service_copy_lift y hy

/-! Explicit structural lift:
    depot -> aFirst -> bOnly -> aReturn -> depot
    depot -> aOther -> cOnly -> depot.
The first path has service 4, the second service 2, with budget 3.
-/

def aFirst : Copy := some ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
def aReturn : Copy := some ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩
def aOther : Copy := some ⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩
def bOnly : Copy := some ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩
def cOnly : Copy := some ⟨⟨3, by decide⟩, ⟨0, by decide⟩⟩

def witnessEdges : Finset (Copy × Copy) :=
  {(none, aFirst), (aFirst, bOnly), (bOnly, aReturn), (aReturn, none),
   (none, aOther), (aOther, cOnly), (cOnly, none)}

def witnessFlow (u v : Copy) : ℕ :=
  if (u, v) ∈ witnessEdges then 1 else 0

def badSet : Finset Copy := {aFirst, bOnly, aReturn}

theorem witness_project_exact : ∀ u v : Node,
    projectFlow (project (0 : Node) required) witnessFlow u v = fixedFlow u v := by
  decide +kernel

theorem witness_out_one : ∀ c : Copy, c ≠ none →
    outFlow Finset.univ witnessFlow c = 1 := by
  decide +kernel

theorem witness_in_one : ∀ c : Copy, c ≠ none →
    inFlow Finset.univ witnessFlow c = 1 := by
  decide +kernel

theorem witness_positive_cuts : ∀ S : Finset Copy,
    S.Nonempty → none ∉ S → 1 ≤ outCutFlow S witnessFlow := by
  decide +kernel

/-- This also proves the universal obstruction is not vacuous. -/
theorem witness_is_structural :
    IsStructuralCopyLift (0 : Node) required fixedFlow witnessFlow where
  project_exact := witness_project_exact
  out_one := witness_out_one
  in_one := witness_in_one
  positive_cuts := witness_positive_cuts

theorem badSet_nonempty : badSet.Nonempty := by decide +kernel
theorem depot_not_mem_badSet : (none : Copy) ∉ badSet := by decide +kernel

theorem badSet_service_eq_four :
    (∑ c ∈ badSet, copyService (0 : Node) required service c) = (4 : ℚ) := by
  decide +kernel

theorem badSet_outCut_eq_one : outCutFlow badSet witnessFlow = 1 := by
  decide +kernel

theorem badSet_violates_capacity :
    (outCutFlow badSet witnessFlow : ℤ) <
      Int.ceil ((∑ c ∈ badSet, copyService (0 : Node) required service c) / capacity) := by
  rw [badSet_service_eq_four, badSet_outCut_eq_one]
  norm_num [capacity]

/-- The bad subset selects some, but not all, copies of the same physical node. -/
theorem badSet_splits_a_fibre :
    aFirst ∈ badSet ∧ aOther ∉ badSet ∧
      project (0 : Node) required aFirst = project (0 : Node) required aOther := by
  decide +kernel

/-- Physical set {a,b} includes ALL three a occurrences: work 5, out-cut 2. -/
theorem physical_ab_cut_passes :
    requiredServiceIn ({1, 2} : Finset Node) service required = (5 : ℚ) ∧
    outCutFlow ({1, 2} : Finset Node) fixedFlow = 2 ∧
    Int.ceil (requiredServiceIn ({1, 2} : Finset Node) service required / capacity) ≤
      (outCutFlow ({1, 2} : Finset Node) fixedFlow : ℤ) := by
  decide +kernel

/-- All original aggregate conditions hold; structural lifts exist;
none satisfies every rounded copy cut, and a concrete failure is exhibited. -/
theorem physical_cuts_pass_but_copy_cuts_obstruct :
    AggregateConditions fixedFlow ∧
    IsStructuralCopyLift (0 : Node) required fixedFlow witnessFlow ∧
    (¬ ∃ y : Copy → Copy → ℕ,
      IsServiceCopyLift (0 : Node) required fixedFlow service capacity y) ∧
    badSet.Nonempty ∧ (none : Copy) ∉ badSet ∧
    (outCutFlow badSet witnessFlow : ℤ) <
      Int.ceil ((∑ c ∈ badSet, copyService (0 : Node) required service c) / capacity) := by
  exact ⟨fixed_flow_aggregate_conditions, witness_is_structural,
    no_service_copy_lift, badSet_nonempty, depot_not_mem_badSet,
    badSet_violates_capacity⟩

end FourNode
end UAVProof.CopyLiftObstruction

#print axioms UAVProof.CopyLiftObstruction.no_serviceCopyLift_of_no_exact_decomposition
#print axioms UAVProof.CopyLiftObstruction.exists_violated_copy_cut_of_no_serviceCopyLift
#print axioms UAVProof.CopyLiftObstruction.FourNode.no_budget_exact_family
#print axioms UAVProof.CopyLiftObstruction.FourNode.no_service_copy_lift
#print axioms UAVProof.CopyLiftObstruction.FourNode.every_structural_lift_has_violated_cut
#print axioms UAVProof.CopyLiftObstruction.FourNode.witness_is_structural
#print axioms UAVProof.CopyLiftObstruction.FourNode.badSet_violates_capacity
#print axioms UAVProof.CopyLiftObstruction.FourNode.badSet_splits_a_fibre
#print axioms UAVProof.CopyLiftObstruction.FourNode.physical_ab_cut_passes
#print axioms UAVProof.CopyLiftObstruction.FourNode.physical_cuts_pass_but_copy_cuts_obstruct
