import LeanCompletion.UAV.TreeFlowSymmetry
import LeanCompletion.UAV.RouteSplice
import LeanCompletion.UAV.PositiveFlowConnectivity

/-! Budget-free decomposition of symmetric integer flows by insertion.
The intermediate family is bounded by the target flow and has maximal size. -/

namespace UAVProof.TreeRouteDecomposition
open TreeFlowSymmetry

variable {V : Type*} [Fintype V] [DecidableEq V]

def depotStar (o v : V) (hv : v ≠ o) : LegalRoute o where
  visits := [v]
  visits_nonempty := by simp
  depot_not_mem := by simpa [eq_comm] using hv
  adjacent_ne := by simp [depotRoute, List.isChain_cons_cons, hv, Ne.symm hv]

theorem depotStar_flow (o v : V) (hv : v ≠ o) (i j : V) :
    routeFlow (depotStar o v hv).vertices i j =
      (if o = i ∧ v = j then 1 else 0) + (if v = i ∧ o = j then 1 else 0) := by
  simp [routeFlow, depotStar, LegalRoute.vertices, depotRoute, List.count_cons]
  omega

abbrev Starts (o : V) (x : V → V → ℕ) := Σ v : V, Fin (x o v)

def initialRoutes (o : V) (x : V → V → ℕ) (hloop : x o o = 0) :
    Starts o x → LegalRoute o := fun k => depotStar o k.1 (by
      intro h; have hk : 0 < x o k.1 := Nat.zero_lt_of_lt k.2.isLt; rw [h, hloop] at hk; omega)

theorem initial_flow (o : V) (x : V → V → ℕ) (hloop : x o o = 0) (i j : V) :
    totalRouteFlow Finset.univ (initialRoutes o x hloop) i j =
      (if o = i then x o j else 0) + (if o = j then x o i else 0) := by
  simp only [totalRouteFlow, Fintype.sum_sigma, initialRoutes, depotStar_flow]
  simp only [Finset.sum_add_distrib]
  by_cases hi : o = i
  · subst i
    by_cases hj : o = j
    · subst j; simp
    · simp [hj, Ne.symm hj]
  · by_cases hj : o = j
    · subst j; simp [hi, Ne.symm hi]
    · simp [hi, hj]

theorem initial_card (o : V) (x : V → V → ℕ) :
    Fintype.card (Starts o x) = outFlow Finset.univ x o := by
  simp [Starts, Fintype.card_sigma, outFlow]

def mass (x : V → V → ℕ) : ℕ := ∑ u, ∑ v, x u v

theorem mass_mono {x y : V → V → ℕ} (h : ∀ u v, x u v ≤ y u v) : mass x ≤ mass y :=
  Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => h u v

def Good {I : Type*} [Fintype I] {o : V} (x : V → V → ℕ)
    (rs : I → LegalRoute o) : Prop :=
  (∀ u v, totalRouteFlow Finset.univ rs u v ≤ x u v) ∧
  (∀ u v, totalRouteFlow Finset.univ rs u v = totalRouteFlow Finset.univ rs v u) ∧
  ∀ v, totalRouteFlow Finset.univ rs o v = x o v

theorem maximal_family {I : Type*} [Fintype I] {o : V} (x : V → V → ℕ)
    (seed : I → LegalRoute o) (hseed : Good x seed) :
    ∃ rs : I → LegalRoute o, Good x rs ∧
      ∀ rs' : I → LegalRoute o, Good x rs' →
        mass (totalRouteFlow Finset.univ rs') ≤ mass (totalRouteFlow Finset.univ rs) := by
  classical
  let P : ℕ → Prop := fun n => ∃ rs : I → LegalRoute o,
    Good x rs ∧ mass (totalRouteFlow Finset.univ rs) = n
  have hp : P (mass (totalRouteFlow Finset.univ seed)) := ⟨seed, hseed, rfl⟩
  have hm := Nat.findGreatest_spec (P := P) (mass_mono hseed.1) hp
  obtain ⟨rs, hg, he⟩ := hm
  refine ⟨rs, hg, fun rs' hg' => ?_⟩
  rw [he]
  exact Nat.le_findGreatest (mass_mono hg'.1) ⟨rs', hg', rfl⟩

theorem maximal_visited_saturated {I : Type*} [Fintype I] [DecidableEq I] {o : V}
    (x : V → V → ℕ) (hloop : ∀ v, x v v = 0) (hsym : ∀ u v, x u v = x v u)
    (rs : I → LegalRoute o) (hg : Good x rs)
    (hmax : ∀ rs' : I → LegalRoute o, Good x rs' →
      mass (totalRouteFlow Finset.univ rs') ≤ mass (totalRouteFlow Finset.univ rs))
    (r : I) (p : V) (hp : p ∈ (rs r).visits) :
    ∀ v, totalRouteFlow Finset.univ rs p v = x p v := by
  classical
  intro v
  by_contra heq
  have hlt : totalRouteFlow Finset.univ rs p v < x p v := lt_of_le_of_ne (hg.1 p v) heq
  have hpo : p ≠ o := fun h => (rs r).depot_not_mem (h ▸ hp)
  have hvo : v ≠ o := by
    intro h; subst v
    rw [hg.2.1 p o, hg.2.2 p, hsym o p] at hlt
    omega
  have hvp : v ≠ p := by
    intro h; subst v
    rw [hloop] at hlt; omega
  have hlt' : totalRouteFlow Finset.univ rs v p < x v p := by
    rw [hg.2.1 v p, hsym v p]; exact hlt
  obtain ⟨rs', hf⟩ := RouteSplice.exists_family_insertExcursion rs r p v hp hvo hvp
  have hg' : Good x rs' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      rw [hf]
      by_cases h : p = i ∧ v = j
      · obtain ⟨rfl, rfl⟩ := h
        simp only [true_and, and_self, if_true, hvp, false_and, if_false, add_zero]
        omega
      · by_cases h' : v = i ∧ p = j
        · obtain ⟨rfl, rfl⟩ := h'
          simp only [h, if_false, zero_add, and_self, if_true]
          omega
        · simp only [h, h', if_false, add_zero]
          exact hg.1 i j
    · intro i j
      rw [hf, hf, hg.2.1 i j]
      simp only [and_comm]
      omega
    · intro j
      rw [hf]
      simp [hpo, hvo, hg.2.2]
  have hmono : ∀ i j, totalRouteFlow Finset.univ rs i j ≤ totalRouteFlow Finset.univ rs' i j := by
    intro i j; rw [hf]; omega
  have hstrict : mass (totalRouteFlow Finset.univ rs) < mass (totalRouteFlow Finset.univ rs') := by
    apply Finset.sum_lt_sum (fun i _ => Finset.sum_le_sum (fun j _ => hmono i j))
    refine ⟨p, Finset.mem_univ _, ?_⟩
    apply Finset.sum_lt_sum (fun j _ => hmono p j)
    refine ⟨v, Finset.mem_univ _, ?_⟩
    rw [hf]
    simp only [and_self, if_true]
    omega
  have := hmax rs' hg'
  omega

theorem initial_good (o : V) (x : V → V → ℕ) (hloop : ∀ v, x v v = 0)
    (hsym : ∀ u v, x u v = x v u) : Good x (initialRoutes o x (hloop o)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [initial_flow]
    by_cases hi : o = i
    · subst i; simp [hloop]
    · by_cases hj : o = j
      · subst j; simp [hi, hsym o i]
      · simp [hi, hj]
  · intro i j
    rw [initial_flow, initial_flow]
    omega
  · intro v
    simp [initial_flow, hloop]

/-- A symmetric loop-free flow connected to the depot admits an exact family.
The construction maximizes a bounded partial family and inserts missing excursions. -/
theorem symmetric_connected_family (o : V) (x : V → V → ℕ)
    (hloop : ∀ v, x v v = 0) (hsym : ∀ u v, x u v = x v u)
    (hconn : PositiveFlowConnectivity.DepotConnected o x) :
    ∃ rs : Starts o x → LegalRoute o,
      ∀ u v, totalRouteFlow Finset.univ rs u v = x u v := by
  classical
  obtain ⟨rs, hg, hmax⟩ := maximal_family x (initialRoutes o x (hloop o))
    (initial_good o x hloop hsym)
  have hstep : ∀ u v,
      (∀ w, totalRouteFlow Finset.univ rs u w = x u w) → 0 < x u v →
      ∀ w, totalRouteFlow Finset.univ rs v w = x v w := by
    intro u v hu hp
    by_cases hv : v = o
    · subst v; exact hg.2.2
    have hpos : 0 < totalRouteFlow Finset.univ rs v u := by
      rw [hg.2.1 v u, hu v]; exact hp
    have hout : 0 < outFlow Finset.univ (totalRouteFlow Finset.univ rs) v :=
      lt_of_lt_of_le hpos (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ u))
    rw [total_outFlow_eq_visit_count Finset.univ rs v hv] at hout
    obtain ⟨r, _, hr⟩ := Finset.sum_pos_iff.mp hout
    exact maximal_visited_saturated x hloop hsym rs hg hmax r v (List.count_pos_iff.mp hr)
  refine ⟨rs, ?_⟩
  intro u v
  by_cases hp : 0 < x u v
  · exact PositiveFlowConnectivity.reachable_closed hsym
      (fun u => ∀ v, totalRouteFlow Finset.univ rs u v = x u v)
      hg.2.2 hstep (hconn u v hp) v
  · have := hg.1 u v
    omega

theorem symmetric_connected_exactDecomposable (o : V) (x : V → V → ℕ)
    (d : V → ℕ) (m : ℕ) (hdegrees : SupportExactFeasibility.HasDegrees o d m x)
    (hloop : ∀ v, x v v = 0) (hsym : ∀ u v, x u v = x v u)
    (hconn : PositiveFlowConnectivity.DepotConnected o x) :
    ExactDecomposable o x d m := by
  classical
  obtain ⟨rs, hf⟩ := symmetric_connected_family o x hloop hsym hconn
  have hc : Fintype.card (Starts o x) = m := by
    rw [initial_card]
    simpa [SupportExactFeasibility.prescribedDegree] using hdegrees.1 o
  let e : Fin m ≃ Starts o x := Fintype.equivOfCardEq (by simpa using hc.symm)
  apply (exactDecomposable_iff_exactFlow o x d m hdegrees).mpr
  refine ⟨fun r => rs (e r), ?_⟩
  intro u v
  calc
    totalRouteFlow Finset.univ (fun r => rs (e r)) u v =
        totalRouteFlow Finset.univ rs u v := by
      simpa only [totalRouteFlow] using
        Equiv.sum_comp e (fun r => routeFlow (rs r).vertices u v)
    _ = x u v := hf u v

theorem symmetric_exactDecomposable_iff (o : V) (x : V → V → ℕ)
    (d : V → ℕ) (m : ℕ) (hdegrees : SupportExactFeasibility.HasDegrees o d m x)
    (hloop : ∀ v, x v v = 0) (hsym : ∀ u v, x u v = x v u) :
    ExactDecomposable o x d m ↔ PositiveFlowConnectivity.DepotConnected o x :=
  ⟨PositiveFlowConnectivity.exactDecomposable_connected,
    symmetric_connected_exactDecomposable o x d m hdegrees hloop hsym⟩

/-- The budget-free exact decomposition criterion for a prescribed tree flow. -/
theorem tree_exactDecomposable_iff (G : SimpleGraph V) (hG : G.IsTree)
    (o : V) (x : V → V → ℕ) (d : V → ℕ) (m : ℕ)
    (hdegrees : SupportExactFeasibility.HasDegrees o d m x)
    (hshape : ∀ u v, ¬ G.Adj u v → x u v = 0) :
    ExactDecomposable o x d m ↔ PositiveFlowConnectivity.DepotConnected o x :=
  symmetric_exactDecomposable_iff o x d m hdegrees
    (fun v => hshape v v G.irrefl)
    (tree_flow_symmetric G hG x hshape
      (fun v => (hdegrees.1 v).trans (hdegrees.2 v).symm))

end UAVProof.TreeRouteDecomposition

#print axioms UAVProof.TreeRouteDecomposition.symmetric_exactDecomposable_iff
#print axioms UAVProof.TreeRouteDecomposition.tree_exactDecomposable_iff
