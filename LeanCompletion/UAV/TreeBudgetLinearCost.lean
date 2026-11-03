import LeanCompletion.UAV.TreeBudgetMatrix
import LeanCompletion.UAV.TreeBudgetCertificate

/-! Arbitrary rational parent-edge weights encoded by executable signed service
fees. No route validity or nonnegativity is needed for the row identity. -/
namespace UAVProof.TreeBudgetLinearCost
open TreeFlowExistence TreeBudgetRow TreeBudgetMatrix TreeBudgetPatterns
open SupportExactFeasibility ResourceCuts
variable {V : Type*} [Fintype V] [DecidableEq V]

def linearCost (R : RootedTree V) (p : V → ℕ) (w : V → ℚ) : ℚ :=
  ∑ v, if v = R.root then 0 else w v * (p v : ℚ)

def virtualService {V : Type*} [Fintype V] [DecidableEq V]
    (R : RootedTree V) (w : V → ℚ) (v : V) : ℚ :=
  if hv : v = R.root then 0 else
    have _ := hv
    w v - virtualService R w (R.parent v)
termination_by (∑ u, R.rank u) - R.rank v
decreasing_by
  have h := R.parent_rank v hv
  have hb : R.rank (R.parent v) ≤ ∑ u, R.rank u :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  omega

@[simp] theorem virtualService_root (R : RootedTree V) (w : V → ℚ) :
    virtualService R w R.root = 0 := by rw [virtualService]; simp

theorem virtualService_edge (R : RootedTree V) (w : V → ℚ) (v : V)
    (hv : v ≠ R.root) :
    virtualService R w v + virtualService R w (R.parent v) = w v := by
  rw [virtualService]
  simp [hv]

theorem rowCost_virtualService (R : RootedTree V) (p : V → ℕ) (w : V → ℚ) :
    rowCost R p (virtualService R w) = linearCost R p w := by
  rw [rowCost_linear]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = R.root
  · simp [hv]
  · have hp : (if R.parent v = R.root then 0 else virtualService R w (R.parent v)) =
        virtualService R w (R.parent v) := by split_ifs with h <;> simp [h]
    simp only [hv, if_false, hp, virtualService_edge R w v hv]

theorem exists_virtualService (R : RootedTree V) (w : V → ℚ) :
    ∃ s : V → ℚ, s R.root = 0 ∧ ∀ p, rowCost R p s = linearCost R p w :=
  ⟨virtualService R w, virtualService_root R w, fun p => rowCost_virtualService R p w⟩

def LinearMatrixFeasible (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (w : V → ℚ) (T : ℚ) : Prop :=
  ∃ p : Fin m → V → ℕ,
    (∀ v, v ≠ R.root → ∑ i, p i v = h v) ∧
    (∀ i, rootDegree R (p i) = 1) ∧ (∀ i, AncestorClosed R (p i)) ∧
    (∀ i, linearCost R (p i) w ≤ T)

theorem linearMatrix_iff (R : RootedTree V) (h : V → ℕ) (m : ℕ)
    (w : V → ℚ) (T : ℚ) :
    LinearMatrixFeasible R h m w T ↔ MatrixFeasible R h m (virtualService R w) T := by
  simp only [LinearMatrixFeasible, MatrixFeasible, rowCost_virtualService]

/-- Directional costs are charged per traversal, including both depot edges. -/
def flowTravel (x : V → V → ℕ) (c : V → V → ℚ) : ℚ :=
  ∑ u, ∑ v, c u v * (x u v : ℚ)

def combinedWeight (R : RootedTree V) (s : V → ℚ) (c : V → V → ℚ) (v : V) : ℚ :=
  s v + (if R.parent v = R.root then 0 else s (R.parent v)) +
    c (R.parent v) v + c v (R.parent v)

theorem flowTravel_edgeFlow (R : RootedTree V) (p : V → ℕ) (c : V → V → ℚ) :
    flowTravel (edgeFlow R p) c =
      linearCost R p (fun v => c (R.parent v) v + c v (R.parent v)) := by
  unfold flowTravel edgeFlow
  simp only [Nat.cast_add, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun u v => c u v *
    ((if v ≠ R.root ∧ R.parent v = u then p v else 0 : ℕ) : ℚ))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = R.root
  · simp [hv]
  · simp [hv, add_mul]

theorem combined_rowCost (R : RootedTree V) (p : V → ℕ)
    (s : V → ℚ) (c : V → V → ℚ) :
    rowCost R p s + flowTravel (edgeFlow R p) c =
      rowCost R p (virtualService R (combinedWeight R s c)) := by
  rw [rowCost_virtualService, rowCost_linear, flowTravel_edgeFlow]
  unfold linearCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = R.root
  · simp [hv]
  · simp only [hv, if_false, combinedWeight]; ring

noncomputable def routeCost {o : V} (r : LegalRoute o)
    (s : V → ℚ) (c : V → V → ℚ) : ℚ :=
  routeServiceIn r Finset.univ s + flowTravel (routeFlow r.vertices) c

theorem routeCost_eq_virtual (R : RootedTree V) (r : LegalRoute R.root)
    (s : V → ℚ) (c : V → V → ℚ)
    (hs : ∀ u v, ¬ R.graph.Adj u v → routeFlow r.vertices u v = 0) :
    routeCost r s c = routeServiceIn r Finset.univ
      (virtualService R (combinedWeight R s c)) := by
  unfold routeCost
  rw [service_of_counts R _ r (routeRow_counts R r hs) s, routeRow_flow R r hs,
    combined_rowCost, service_of_counts R _ r (routeRow_counts R r hs)]

def TravelExactFeasible (R : RootedTree V) (h d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (c : V → V → ℚ) (T : ℚ) : Prop :=
  ∃ rs : Fin m → LegalRoute R.root,
    (∀ v, v ≠ R.root → totalVisitCount Finset.univ rs v = d v) ∧
    (∀ i, routeCost (rs i) s c ≤ T) ∧
    (∀ u v, totalRouteFlow Finset.univ rs u v = edgeFlow R h u v)

theorem travelExact_iff_virtual (R : RootedTree V) (h d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (c : V → V → ℚ) (T : ℚ) :
    TravelExactFeasible R h d m s c T ↔
      ExactFeasible R.root (edgeFlow R h) d m (virtualService R (combinedWeight R s c)) T := by
  constructor <;> rintro ⟨rs, hc, hb, hf⟩ <;> refine ⟨rs, hc, ?_, hf⟩
  · intro i
    rw [← routeCost_eq_virtual R (rs i) s c (fun u v hn =>
      route_supported_of_exact _ rs hf i u v (edgeFlow_supported R h u v hn))]
    exact hb i
  · intro i
    rw [routeCost_eq_virtual R (rs i) s c (fun u v hn =>
      route_supported_of_exact _ rs hf i u v (edgeFlow_supported R h u v hn))]
    exact hb i

theorem travelExact_iff_matrix (R : RootedTree V) (h d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (c : V → V → ℚ) (T : ℚ)
    (hd : HasDegrees R.root d m (edgeFlow R h)) :
    TravelExactFeasible R h d m s c T ↔
      MatrixFeasible R h m (virtualService R (combinedWeight R s c)) T := by
  rw [travelExact_iff_virtual, exact_iff_matrix R h d m _ T hd]

/-- Reuse the existing executable checker, with no change to certificate format. -/
theorem travelExact_iff_certificate (R : RootedTree V) (h d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (c : V → V → ℚ) (T : ℚ)
    (hd : HasDegrees R.root d m (edgeFlow R h)) :
    TravelExactFeasible R h d m s c T ↔
      ∃ C : TreeBudgetCertificate.Certificate V,
        TreeBudgetCertificate.checkCertificate R h m
          (virtualService R (combinedWeight R s c)) T C = true := by
  rw [travelExact_iff_matrix R h d m s c T hd,
    TreeBudgetCertificate.matrix_iff_exists_certificate]

/-- This accounting identity holds on any finite graph, not only a tree. -/
theorem total_cost_fixed {o : V} {I : Type*} [Fintype I]
    (rs : I → LegalRoute o) (d : V → ℕ) (x : V → V → ℕ)
    (s : V → ℚ) (c : V → V → ℚ)
    (hc : ∀ v, v ≠ o → totalVisitCount Finset.univ rs v = d v)
    (hf : ∀ u v, totalRouteFlow Finset.univ rs u v = x u v) :
    (∑ i, routeCost (rs i) s c) =
      (∑ v, if v = o then 0 else s v * (d v : ℚ)) + flowTravel x c := by
  simp only [routeCost, Finset.sum_add_distrib]
  congr 1
  · unfold routeServiceIn
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v = o
    · subst v
      simp [List.count_eq_zero.mpr (rs _).depot_not_mem]
    · simp only [hv, if_false, ← Finset.mul_sum]
      congr 1
      exact_mod_cast hc v hv
  · unfold flowTravel
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.mul_sum]
    congr 1
    exact_mod_cast hf u v

end UAVProof.TreeBudgetLinearCost

#print axioms UAVProof.TreeBudgetLinearCost.exists_virtualService
#print axioms UAVProof.TreeBudgetLinearCost.rowCost_virtualService
#print axioms UAVProof.TreeBudgetLinearCost.linearMatrix_iff
#print axioms UAVProof.TreeBudgetLinearCost.flowTravel_edgeFlow
#print axioms UAVProof.TreeBudgetLinearCost.routeCost_eq_virtual
#print axioms UAVProof.TreeBudgetLinearCost.travelExact_iff_matrix
#print axioms UAVProof.TreeBudgetLinearCost.travelExact_iff_certificate
#print axioms UAVProof.TreeBudgetLinearCost.total_cost_fixed
