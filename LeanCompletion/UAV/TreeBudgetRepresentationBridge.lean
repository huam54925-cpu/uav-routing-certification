import LeanCompletion.UAV.TreeBudgetCertificate
import LeanCompletion.UAV.LocalVisitPairingNextCertificate

/-! Interfaces between explicit routes, tree rows, checked pattern certificates,
and unbounded next certificates. Tree-side costs may be signed. Only the reverse
next-to-routes interface inherits nonnegative fees and positive budget.
Reconstruction is existential, not an executable choice of route ordering. -/
namespace UAVProof.TreeBudgetRepresentationBridge

open TreeFlowExistence TreeBudgetRow TreeBudgetMatrix TreeBudgetPatterns
open TreeBudgetCertificate SupportExactFeasibility ResourceCuts
open LocalVisitPairingCompleteness LocalVisitPairingNextCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Forget visit order and normalize the ignored root coordinate. Tree support
is a separate hypothesis in soundness statements, not part of `LegalRoute`. -/
def projectRow (R : RootedTree V) (r : LegalRoute R.root) : V → ℕ :=
  normalize R (routeRow R r)

@[simp] theorem projectRow_root (R : RootedTree V) (r : LegalRoute R.root) :
    projectRow R r R.root = 0 := by simp [projectRow]

theorem edgeFlow_normalize (R : RootedTree V) (p : V → ℕ) :
    edgeFlow R (normalize R p) = edgeFlow R p := by
  funext u v
  by_cases hu : u = R.root <;> by_cases hv : v = R.root <;>
    simp [edgeFlow, TreeBudgetPatterns.normalize, hu, hv]

/-- Exact row flow determines the normalized row, without any sign assumptions. -/
theorem projectRow_of_flow (R : RootedTree V) (p : V → ℕ) (r : LegalRoute R.root)
    (hf : ∀ u v, routeFlow r.vertices u v = edgeFlow R p u v) :
    projectRow R r = normalize R p := by
  funext v
  by_cases hv : v = R.root
  · simp [projectRow, TreeBudgetPatterns.normalize, hv]
  · simp only [projectRow, TreeBudgetPatterns.normalize, if_neg hv, routeRow, hf]
    exact edgeFlow_parent R p hv

theorem projectRow_flow (R : RootedTree V) (r : LegalRoute R.root)
    (hs : ∀ u v, ¬ R.graph.Adj u v → routeFlow r.vertices u v = 0) :
    routeFlow r.vertices = edgeFlow R (projectRow R r) := by
  rw [projectRow, edgeFlow_normalize]
  exact routeRow_flow R r hs

/-- Projection preserves the structural row conditions, counts and arbitrary
signed additive costs. No upper bound H or budget is needed at this layer. -/
theorem projectRow_sound (R : RootedTree V) (r : LegalRoute R.root)
    (hs : ∀ u v, ¬ R.graph.Adj u v → routeFlow r.vertices u v = 0) :
    rootCount R (projectRow R r) = 1 ∧ AncestorClosed R (projectRow R r) ∧
      (∀ v, r.visits.count v = rowVisits R (projectRow R r) v) ∧
      ∀ s : V → ℚ, routeServiceIn r Finset.univ s = cost R (projectRow R r) s := by
  have hf : ∀ u v, routeFlow r.vertices u v = edgeFlow R (projectRow R r) u v :=
    fun u v => congrFun (congrFun (projectRow_flow R r hs) u) v
  refine ⟨?_, ?_, counts_of_flow R _ r hf, ?_⟩
  · rw [projectRow, normalize_rootCount, rootCount_eq]
    exact routeRow_root R r hs
  · rw [projectRow, normalize_ancestor]
    exact routeRow_ancestor R r hs
  · intro s
    rw [cost_eq]
    exact service_of_flow R _ r hf s

/-- A root coordinate supplied by the caller is ignored, then normalized by
projection. The same realized route satisfies the cost identity for every s. -/
theorem exists_route_project_normalize (R : RootedTree V) (p : V → ℕ)
    (ha : AncestorClosed R p) (hk : rootDegree R p = 1) :
    ∃ r : LegalRoute R.root,
      (∀ u v, routeFlow r.vertices u v = edgeFlow R p u v) ∧
      projectRow R r = normalize R p ∧
      (∀ v, r.visits.count v = rowVisits R p v) ∧
      ∀ s : V → ℚ, routeServiceIn r Finset.univ s = cost R p s := by
  obtain ⟨r, hf, hc⟩ := single_row_realization R p ha hk
  refine ⟨r, hf, projectRow_of_flow R p r hf, hc, ?_⟩
  intro s
  rw [cost_eq]
  exact service_of_counts R p r hc s

/-- On normalized rows, realization followed by projection is a right-inverse
contract. It does not recover the original route's ordering or identity. -/
theorem exists_route_project (R : RootedTree V) (p : V → ℕ)
    (hp0 : p R.root = 0) (ha : AncestorClosed R p) (hk : rootDegree R p = 1) :
    ∃ r : LegalRoute R.root,
      (∀ u v, routeFlow r.vertices u v = edgeFlow R p u v) ∧
      projectRow R r = p ∧ (∀ v, r.visits.count v = rowVisits R p v) ∧
      ∀ s : V → ℚ, routeServiceIn r Finset.univ s = cost R p s := by
  have hn : normalize R p = p := by
    funext v
    by_cases hv : v = R.root <;> simp [TreeBudgetPatterns.normalize, hv, hp0]
  simpa only [hn] using exists_route_project_normalize R p ha hk

/-- Row validity gives a budget-feasible realization, even for negative fees
and negative budget. The nonroot H bounds remain a property of the same row. -/
theorem rowValid_exists_route (R : RootedTree V) (H : V → ℕ) (s : V → ℚ)
    (T : ℚ) (p : V → ℕ) (hp : RowValid R H s T p) :
    ∃ r : LegalRoute R.root,
      (∀ u v, routeFlow r.vertices u v = edgeFlow R p u v) ∧
      projectRow R r = p ∧ (∀ v, r.visits.count v = rowVisits R p v) ∧
      (∀ fees : V → ℚ, routeServiceIn r Finset.univ fees = cost R p fees) ∧
      routeServiceIn r Finset.univ s ≤ T := by
  obtain ⟨r, hf, hproject, hc, hs⟩ := exists_route_project R p hp.1 hp.2.2.2.1
    (by simpa only [rootCount_eq] using hp.2.2.1)
  exact ⟨r, hf, hproject, hc, hs, (hs s).le.trans hp.2.2.2.2⟩

/-- Signed tree-side existence bridge; no positive fleet size is required. -/
theorem exact_iff_checked_certificate (R : RootedTree V) (H d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hd : HasDegrees R.root d m (edgeFlow R H)) :
    ExactFeasible R.root (edgeFlow R H) d m s T ↔
      ∃ c : Certificate V, checkCertificate R H m s T c = true :=
  (exact_iff_matrix R H d m s T hd).trans (matrix_iff_exists_certificate R H m s T)

/-- The forward next-certificate construction needs no fee or budget signs. -/
theorem exact_implies_next (R : RootedTree V) (H d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (he : ExactFeasible R.root (edgeFlow R H) d m s T) :
    HasNextCertificate R.root d (edgeFlow R H) s T :=
  (hasNextCertificate_iff_hasLocalCertificate R.root d (edgeFlow R H) s T).mpr
    (hasLocalCertificate_of_exactFeasible R.root d (edgeFlow R H) m s T he)

theorem matrix_implies_next (R : RootedTree V) (H d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hd : HasDegrees R.root d m (edgeFlow R H))
    (hm : MatrixFeasible R H m s T) : HasNextCertificate R.root d (edgeFlow R H) s T :=
  exact_implies_next R H d m s T ((exact_iff_matrix R H d m s T hd).mpr hm)

theorem checked_certificate_implies_next (R : RootedTree V) (H d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hd : HasDegrees R.root d m (edgeFlow R H))
    (c : Certificate V) (hc : checkCertificate R H m s T c = true) :
    HasNextCertificate R.root d (edgeFlow R H) s T :=
  exact_implies_next R H d m s T ((exact_iff_checked_certificate R H d m s T hd).mpr ⟨c, hc⟩)

/-- The existing inverse next interface retains its sign hypotheses. Tree
irreflexivity supplies no-loops, and HasDegrees supplies the fleet equality. -/
theorem next_iff_exact (R : RootedTree V) (H d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hd : HasDegrees R.root d m (edgeFlow R H))
    (hs : ∀ v, 0 ≤ s v) (hT : 0 < T) :
    HasNextCertificate R.root d (edgeFlow R H) s T ↔
      ExactFeasible R.root (edgeFlow R H) d m s T := by
  have hcount : m = outFlow Finset.univ (edgeFlow R H) R.root := by
    simpa only [prescribedDegree, if_pos rfl] using (hd.1 R.root).symm
  have hiff := exactFeasible_iff_count_and_hasNextCertificate R.root d (edgeFlow R H)
    m s T (fun v => edgeFlow_supported R H v v R.graph.irrefl) hs hT
  simpa only [hcount, true_and] using hiff.symm

theorem next_iff_matrix (R : RootedTree V) (H d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hd : HasDegrees R.root d m (edgeFlow R H))
    (hs : ∀ v, 0 ≤ s v) (hT : 0 < T) :
    HasNextCertificate R.root d (edgeFlow R H) s T ↔ MatrixFeasible R H m s T :=
  (next_iff_exact R H d m s T hd hs hT).trans (exact_iff_matrix R H d m s T hd)

theorem next_iff_checked_certificate (R : RootedTree V) (H d : V → ℕ) (m : ℕ)
    (s : V → ℚ) (T : ℚ) (hd : HasDegrees R.root d m (edgeFlow R H))
    (hs : ∀ v, 0 ≤ s v) (hT : 0 < T) :
    HasNextCertificate R.root d (edgeFlow R H) s T ↔
      ∃ c : Certificate V, checkCertificate R H m s T c = true :=
  (next_iff_exact R H d m s T hd hs hT).trans (exact_iff_checked_certificate R H d m s T hd)

end UAVProof.TreeBudgetRepresentationBridge

#print axioms UAVProof.TreeBudgetRepresentationBridge.projectRow_root
#print axioms UAVProof.TreeBudgetRepresentationBridge.edgeFlow_normalize
#print axioms UAVProof.TreeBudgetRepresentationBridge.projectRow_of_flow
#print axioms UAVProof.TreeBudgetRepresentationBridge.projectRow_flow
#print axioms UAVProof.TreeBudgetRepresentationBridge.projectRow_sound
#print axioms UAVProof.TreeBudgetRepresentationBridge.exists_route_project_normalize
#print axioms UAVProof.TreeBudgetRepresentationBridge.exists_route_project
#print axioms UAVProof.TreeBudgetRepresentationBridge.rowValid_exists_route
#print axioms UAVProof.TreeBudgetRepresentationBridge.exact_iff_checked_certificate
#print axioms UAVProof.TreeBudgetRepresentationBridge.exact_implies_next
#print axioms UAVProof.TreeBudgetRepresentationBridge.matrix_implies_next
#print axioms UAVProof.TreeBudgetRepresentationBridge.checked_certificate_implies_next
#print axioms UAVProof.TreeBudgetRepresentationBridge.next_iff_exact
#print axioms UAVProof.TreeBudgetRepresentationBridge.next_iff_matrix
#print axioms UAVProof.TreeBudgetRepresentationBridge.next_iff_checked_certificate
