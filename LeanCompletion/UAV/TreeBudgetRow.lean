import LeanCompletion.UAV.TreeFlowConnectivity
import LeanCompletion.UAV.TreeRouteDecomposition

/-! Edge-count rows on a rooted tree. The root coordinate is ignored. -/
namespace UAVProof.TreeBudgetRow
open TreeFlowExistence TreeFlowConnectivity TreeFlowSymmetry
open TreeRouteDecomposition PositiveFlowConnectivity SupportExactFeasibility ResourceCuts
variable {V : Type*} [Fintype V] [DecidableEq V]

def AncestorClosed (R : RootedTree V) (n : V → ℕ) : Prop :=
  ∀ v, v ≠ R.root → 0 < n v → R.parent v ≠ R.root → 0 < n (R.parent v)

noncomputable def rootDegree (R : RootedTree V) (n : V → ℕ) : ℕ :=
  ∑ w ∈ R.children R.root, n w

noncomputable def rowVisits (R : RootedTree V) (n : V → ℕ) (v : V) : ℕ :=
  if v = R.root then 0 else n v + ∑ w ∈ R.children v, n w

noncomputable def rowCost (R : RootedTree V) (n : V → ℕ) (s : V → ℚ) : ℚ :=
  ∑ v, s v * (rowVisits R n v : ℚ)

theorem row_has_degrees (R : RootedTree V) (n : V → ℕ) :
    HasDegrees R.root (rowVisits R n) (rootDegree R n) (edgeFlow R n) := by
  constructor <;> intro v
  · rw [edgeFlow_out]; by_cases hv : v = R.root <;>
      simp [prescribedDegree, rowVisits, rootDegree, hv]
  · rw [edgeFlow_in]; by_cases hv : v = R.root <;>
      simp [prescribedDegree, rowVisits, rootDegree, hv]

theorem ancestor_iff_connected (R : RootedTree V) (n : V → ℕ) :
    AncestorClosed R n ↔ DepotConnected R.root (edgeFlow R n) := by
  rw [edgeFlow_connected_iff]
  constructor
  · intro h v hv hp
    rw [edgeFlow_out] at hp
    simp only [hv, if_false] at hp
    by_cases hn : 0 < n v
    · exact hn
    · have hs : 0 < ∑ w ∈ R.children v, n w := by omega
      obtain ⟨w, hw, hpos⟩ := Finset.sum_pos_iff.mp hs
      obtain ⟨hwroot, hparent⟩ := (R.mem_children v w).mp hw
      simpa [hparent] using h w hwroot hpos (by simpa [hparent] using hv)
  · intro h v hv hp hpr
    apply h _ hpr
    have he : 0 < edgeFlow R n (R.parent v) v := by
      rw [edgeFlow_parent R n hv]; exact hp
    exact lt_of_lt_of_le he (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ v))

theorem row_decomposable (R : RootedTree V) (n : V → ℕ)
    (ha : AncestorClosed R n) :
    ExactDecomposable R.root (edgeFlow R n) (rowVisits R n) (rootDegree R n) :=
  symmetric_connected_exactDecomposable R.root _ _ _ (row_has_degrees R n)
    (fun v => edgeFlow_supported R n v v R.graph.irrefl)
    (edgeFlow_symmetric R n) ((ancestor_iff_connected R n).mp ha)

theorem single_row_realization (R : RootedTree V) (n : V → ℕ)
    (ha : AncestorClosed R n) (hk : rootDegree R n = 1) :
    ∃ r : LegalRoute R.root, (∀ u v, routeFlow r.vertices u v = edgeFlow R n u v) ∧
      ∀ v, r.visits.count v = rowVisits R n v := by
  have hd := row_decomposable R n ha
  rw [hk] at hd
  obtain ⟨rs, hc, hf⟩ := hd
  refine ⟨rs 0, ?_, ?_⟩
  · intro u v; simpa [totalRouteFlow] using hf u v
  · intro v
    by_cases hv : v = R.root
    · subst v; simp [rowVisits, List.count_eq_zero.mpr (rs 0).depot_not_mem]
    · simpa [totalVisitCount] using hc v hv

theorem service_of_counts (R : RootedTree V) (n : V → ℕ) (r : LegalRoute R.root)
    (hc : ∀ v, r.visits.count v = rowVisits R n v) (s : V → ℚ) :
    routeServiceIn r Finset.univ s = rowCost R n s := by
  simp only [routeServiceIn, rowCost, hc]

theorem counts_of_flow (R : RootedTree V) (n : V → ℕ) (r : LegalRoute R.root)
    (hf : ∀ u v, routeFlow r.vertices u v = edgeFlow R n u v) (v : V) :
    r.visits.count v = rowVisits R n v := by
  by_cases hv : v = R.root
  · subst v; simp [rowVisits, List.count_eq_zero.mpr r.depot_not_mem]
  · rw [← r.outFlow_eq_visit_count v hv]
    have he : routeFlow r.vertices = edgeFlow R n := funext fun u => funext (hf u)
    rw [he, edgeFlow_out]
    simp [rowVisits, hv]

theorem service_of_flow (R : RootedTree V) (n : V → ℕ) (r : LegalRoute R.root)
    (hf : ∀ u v, routeFlow r.vertices u v = edgeFlow R n u v) (s : V → ℚ) :
    routeServiceIn r Finset.univ s = rowCost R n s :=
  service_of_counts R n r (counts_of_flow R n r hf) s

theorem zero_root_row (R : RootedTree V) (n : V → ℕ)
    (ha : AncestorClosed R n) (hk : rootDegree R n = 0) :
    ∀ v, v ≠ R.root → n v = 0 := by
  have hd := row_decomposable R n ha
  rw [hk] at hd
  have he := ((exactDecomposable_zero_iff R.root _ _).mp hd).1
  intro v hv
  have h := congrFun (congrFun he (R.parent v)) v
  simpa [edgeFlow_parent R n hv] using h

theorem rowCost_linear (R : RootedTree V) (n : V → ℕ) (s : V → ℚ) :
    rowCost R n s = ∑ v, if v = R.root then 0 else
      (s v + if R.parent v = R.root then 0 else s (R.parent v)) * (n v : ℚ) := by
  classical
  let t : V → ℚ := fun v => if v = R.root then 0 else s v
  have hcost : rowCost R n s = ∑ v, t v * (n v : ℚ) +
      ∑ v, ∑ w ∈ R.children v, t v * (n w : ℚ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v = R.root <;>
      simp [rowVisits, t, hv, Nat.cast_add, Nat.cast_sum,
        mul_add, Finset.mul_sum]
  rw [hcost]
  have hchildren : (∑ v, ∑ w ∈ R.children v, t v * (n w : ℚ)) =
      ∑ w, if w = R.root then 0 else t (R.parent w) * (n w : ℚ) := by
    simp only [RootedTree.children, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w = R.root <;> simp [hw]
  rw [hchildren, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = R.root <;> simp [t, hv, add_mul]

theorem sum_service_of_exact {I : Type*} [Fintype I] (R : RootedTree V)
    (n : V → ℕ) (rs : I → LegalRoute R.root)
    (hc : ∀ v, v ≠ R.root → totalVisitCount Finset.univ rs v = rowVisits R n v)
    (s : V → ℚ) : (∑ i, routeServiceIn (rs i) Finset.univ s) = rowCost R n s := by
  unfold routeServiceIn rowCost
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = R.root
  · subst v; simp [rowVisits, List.count_eq_zero.mpr (rs _).depot_not_mem]
  · simpa [totalVisitCount, Finset.mul_sum] using congrArg (fun a : ℕ => s v * (a : ℚ)) (hc v hv)

def routeRow (R : RootedTree V) (r : LegalRoute R.root) (v : V) : ℕ :=
  routeFlow r.vertices (R.parent v) v

theorem routeRow_flow (R : RootedTree V) (r : LegalRoute R.root)
    (hs : ∀ u v, ¬ R.graph.Adj u v → routeFlow r.vertices u v = 0) :
    routeFlow r.vertices = edgeFlow R (routeRow R r) :=
  flow_eq_edgeFlow R _ hs (tree_flow_symmetric R.graph R.isTree _ hs
    (closed_route_flow_balance r.vertices r.closed))

theorem routeRow_counts (R : RootedTree V) (r : LegalRoute R.root)
    (hs : ∀ u v, ¬ R.graph.Adj u v → routeFlow r.vertices u v = 0) (v : V) :
    r.visits.count v = rowVisits R (routeRow R r) v := by
  by_cases hv : v = R.root
  · subst v; simp [rowVisits, List.count_eq_zero.mpr r.depot_not_mem]
  · rw [← r.outFlow_eq_visit_count v hv, routeRow_flow R r hs, edgeFlow_out]
    simp [rowVisits, hv]

theorem routeRow_root (R : RootedTree V) (r : LegalRoute R.root)
    (hs : ∀ u v, ¬ R.graph.Adj u v → routeFlow r.vertices u v = 0) :
    rootDegree R (routeRow R r) = 1 := by
  have h := r.outFlow_depot_eq_one
  rw [routeRow_flow R r hs, edgeFlow_out] at h
  simpa [rootDegree] using h

theorem routeRow_ancestor (R : RootedTree V) (r : LegalRoute R.root)
    (hs : ∀ u v, ¬ R.graph.Adj u v → routeFlow r.vertices u v = 0) :
    AncestorClosed R (routeRow R r) := by
  apply (ancestor_iff_connected R _).mpr
  have hd : ExactDecomposable R.root (routeFlow r.vertices) (fun v => r.visits.count v) 1 :=
    ⟨fun _ => r, by simp [totalVisitCount], by simp [totalRouteFlow]⟩
  rw [← routeRow_flow R r hs]
  exact exactDecomposable_connected hd

end UAVProof.TreeBudgetRow

#print axioms UAVProof.TreeBudgetRow.single_row_realization
#print axioms UAVProof.TreeBudgetRow.rowCost_linear
#print axioms UAVProof.TreeBudgetRow.service_of_flow
#print axioms UAVProof.TreeBudgetRow.zero_root_row
