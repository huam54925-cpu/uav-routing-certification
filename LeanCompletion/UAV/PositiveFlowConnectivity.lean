import LeanCompletion.UAV.TreeFlowSymmetry

namespace UAVProof.PositiveFlowConnectivity
open TreeFlowSymmetry SupportExactFeasibility
variable {V : Type*} [Fintype V] [DecidableEq V]

def supportGraph (x : V → V → ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (0 < x u v ∨ 0 < x v u)
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def DepotConnected (depot : V) (x : V → V → ℕ) : Prop :=
  ∀ u v, 0 < x u v → (supportGraph x).Reachable depot u

theorem reachable_closed {depot : V} {x : V → V → ℕ}
    (hsym : ∀ u v, x u v = x v u) (P : V → Prop) (ho : P depot)
    (hstep : ∀ u v, P u → 0 < x u v → P v) {v : V}
    (hr : (supportGraph x).Reachable depot v) : P v := by
  obtain ⟨p⟩ := hr
  have walk_closed : ∀ {a b}, (supportGraph x).Walk a b → P a → P b := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a b c hab p ih =>
      intro ha
      apply ih
      apply hstep a b ha
      rcases hab.2 with hp | hp
      · exact hp
      · simpa [hsym a b] using hp
  exact walk_closed p ho

theorem list_reachable (G : SimpleGraph V) (a : V) (l : List V)
    (he : ∀ u v, (u, v) ∈ (a :: l).zip (a :: l).tail → G.Adj u v) :
    ∀ v ∈ a :: l, G.Reachable a v := by
  induction l generalizing a with
  | nil => simpa using SimpleGraph.Reachable.refl a
  | cons b l ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact SimpleGraph.Reachable.refl _
    · have hab : G.Adj a b := he a b (by simp)
      apply hab.reachable.trans
      apply ih b (fun u w hw => he u w (by simpa using Or.inr hw)) v hv

theorem supported_route_reachable {depot : V} (r : LegalRoute depot)
    (x : V → V → ℕ) (hs : RouteUsesSupport x r) {v : V}
    (hv : v ∈ r.visits) : (supportGraph x).Reachable depot v := by
  apply list_reachable (supportGraph x) depot (r.visits ++ [depot])
  · intro u w he
    have he' : (u,w) ∈ r.vertices.zip r.vertices.tail := he
    refine ⟨route_edge_ne_of_isChain r.adjacent_ne he', Or.inl ?_⟩
    have hp : 0 < routeFlow r.vertices u w := List.count_pos_iff.mpr he'
    by_contra hn
    have hz : x u w = 0 := by omega
    have := hs u w hz
    omega
  · simp [hv]

theorem exactDecomposable_connected {depot : V} {x : V → V → ℕ}
    {d : V → ℕ} {m : ℕ} (h : ExactDecomposable depot x d m) :
    DepotConnected depot x := by
  obtain ⟨routes, _, hf⟩ := h
  have heq : totalRouteFlow Finset.univ routes = x := funext fun u => funext (hf u)
  intro u v hp
  by_cases hu : u = depot
  · subst u; exact SimpleGraph.Reachable.refl _
  have hout : 0 < outFlow Finset.univ x u := lt_of_lt_of_le hp
    (Finset.single_le_sum (fun j _ => Nat.zero_le (x u j)) (Finset.mem_univ v))
  rw [← heq, total_outFlow_eq_visit_count Finset.univ routes u hu] at hout
  obtain ⟨r, _, hr⟩ := Finset.sum_pos_iff.mp hout
  exact supported_route_reachable (routes r) x
    (route_supported_of_exact x routes hf r) (List.count_pos_iff.mp hr)

end UAVProof.PositiveFlowConnectivity

#print axioms UAVProof.PositiveFlowConnectivity.exactDecomposable_connected
