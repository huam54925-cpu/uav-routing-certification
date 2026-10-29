import LeanCompletion.UAV.ResourceCuts

/-!
# Support feasibility versus exact edge multiplicities

Source baseline: uav-routing-certification, 3594b596ccbfb500483c0d1f84d69ebc0ac84e4c.
New proof candidate: local Lean compilation and axiom reports are pending.

Both predicates use the same Fin m family, exact visit demands, legal-route
semantics and per-route service budget. Support means containment, not equality
of positive edge sets. Travel costs are not included.

No nonnegativity or positive-budget assumption is needed for these implications:
the SAME routes and service costs are preserved, without using capacity cuts.
-/

namespace UAVProof.SupportExactFeasibility

open ResourceCuts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every edge absent from x is absent from z. No upper bound on positive edges. -/
def SupportedBy (z x : V → V → ℕ) : Prop :=
  ∀ u v, x u v = 0 → z u v = 0

def RouteUsesSupport (x : V → V → ℕ) {depot : V}
    (r : LegalRoute depot) : Prop :=
  SupportedBy (routeFlow r.vertices) x

/-- The depot requirement d depot is intentionally ignored. -/
def prescribedDegree (depot : V) (d : V → ℕ) (m : ℕ) (v : V) : ℕ :=
  if v = depot then m else d v

def HasDegrees (depot : V) (d : V → ℕ) (m : ℕ)
    (z : V → V → ℕ) : Prop :=
  (∀ v, outFlow Finset.univ z v = prescribedDegree depot d m v) ∧
  (∀ v, inFlow Finset.univ z v = prescribedDegree depot d m v)

def SupportFeasible (depot : V) (x : V → V → ℕ)
    (d : V → ℕ) (m : ℕ) (service : V → ℚ) (T : ℚ) : Prop :=
  ∃ routes : Fin m → LegalRoute depot,
    (∀ v, v ≠ depot → totalVisitCount Finset.univ routes v = d v) ∧
    (∀ r, routeServiceIn (routes r) Finset.univ service ≤ T) ∧
    (∀ r, RouteUsesSupport x (routes r))

def ExactFeasible (depot : V) (x : V → V → ℕ)
    (d : V → ℕ) (m : ℕ) (service : V → ℚ) (T : ℚ) : Prop :=
  ∃ routes : Fin m → LegalRoute depot,
    (∀ v, v ≠ depot → totalVisitCount Finset.univ routes v = d v) ∧
    (∀ r, routeServiceIn (routes r) Finset.univ service ≤ T) ∧
    (∀ u v, totalRouteFlow Finset.univ routes u v = x u v)

/-- A sufficient condition on the support/degree system, not a feasibility claim. -/
def SupportDeterminesFlow (depot : V) (d : V → ℕ) (m : ℕ)
    (x : V → V → ℕ) : Prop :=
  ∀ z : V → V → ℕ,
    SupportedBy z x → HasDegrees depot d m z → z = x

theorem aggregate_supported {depot : V} {m : ℕ}
    (x : V → V → ℕ) (routes : Fin m → LegalRoute depot)
    (hsupport : ∀ r, RouteUsesSupport x (routes r)) :
    SupportedBy (totalRouteFlow Finset.univ routes) x := by
  intro u v hzero
  unfold totalRouteFlow
  apply Finset.sum_eq_zero
  intro r _
  exact hsupport r u v hzero

theorem route_supported_of_exact {depot : V} {m : ℕ}
    (x : V → V → ℕ) (routes : Fin m → LegalRoute depot)
    (hexact : ∀ u v, totalRouteFlow Finset.univ routes u v = x u v)
    (r : Fin m) : RouteUsesSupport x (routes r) := by
  intro u v hzero
  have hle : routeFlow (routes r).vertices u v ≤
      totalRouteFlow Finset.univ routes u v :=
    Finset.single_le_sum
      (fun k _ => Nat.zero_le (routeFlow (routes k).vertices u v))
      (Finset.mem_univ r)
  rw [hexact u v, hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- Coverage and the common family size derive BOTH degrees. -/
theorem aggregate_has_degrees {depot : V} {m : ℕ}
    (d : V → ℕ) (routes : Fin m → LegalRoute depot)
    (hcover : ∀ v, v ≠ depot → totalVisitCount Finset.univ routes v = d v) :
    HasDegrees depot d m (totalRouteFlow Finset.univ routes) := by
  constructor
  · intro v
    simpa [fleetDegree, prescribedDegree] using
      total_outFlow_eq_fleetDegree Finset.univ routes d hcover v
  · intro v
    simpa [fleetDegree, prescribedDegree] using
      total_inFlow_eq_fleetDegree Finset.univ routes d hcover v

theorem exact_implies_support
    (depot : V) (x : V → V → ℕ) (d : V → ℕ) (m : ℕ)
    (service : V → ℚ) (T : ℚ)
    (h : ExactFeasible depot x d m service T) :
    SupportFeasible depot x d m service T := by
  obtain ⟨routes, hcover, hbudget, hexact⟩ := h
  exact ⟨routes, hcover, hbudget, route_supported_of_exact x routes hexact⟩

/-- Exact feasibility itself implies the prescribed degrees of x. -/
theorem exact_has_degrees
    (depot : V) (x : V → V → ℕ) (d : V → ℕ) (m : ℕ)
    (service : V → ℚ) (T : ℚ)
    (h : ExactFeasible depot x d m service T) :
    HasDegrees depot d m x := by
  obtain ⟨routes, hcover, _, hexact⟩ := h
  have heq : totalRouteFlow Finset.univ routes = x := by
    funext u v
    exact hexact u v
  rw [← heq]
  exact aggregate_has_degrees d routes hcover

theorem support_implies_exact_of_unique
    (depot : V) (x : V → V → ℕ) (d : V → ℕ) (m : ℕ)
    (service : V → ℚ) (T : ℚ)
    (hunique : SupportDeterminesFlow depot d m x)
    (h : SupportFeasible depot x d m service T) :
    ExactFeasible depot x d m service T := by
  obtain ⟨routes, hcover, hbudget, hsupport⟩ := h
  have heq : totalRouteFlow Finset.univ routes = x :=
    hunique (totalRouteFlow Finset.univ routes)
      (aggregate_supported x routes hsupport)
      (aggregate_has_degrees d routes hcover)
  refine ⟨routes, hcover, hbudget, ?_⟩
  intro u v
  exact congrFun (congrFun heq u) v

theorem support_iff_exact_of_unique
    (depot : V) (x : V → V → ℕ) (d : V → ℕ) (m : ℕ)
    (service : V → ℚ) (T : ℚ)
    (hunique : SupportDeterminesFlow depot d m x) :
    SupportFeasible depot x d m service T ↔
      ExactFeasible depot x d m service T := by
  exact ⟨support_implies_exact_of_unique depot x d m service T hunique,
    exact_implies_support depot x d m service T⟩

end UAVProof.SupportExactFeasibility

#print axioms UAVProof.SupportExactFeasibility.aggregate_supported
#print axioms UAVProof.SupportExactFeasibility.route_supported_of_exact
#print axioms UAVProof.SupportExactFeasibility.aggregate_has_degrees
#print axioms UAVProof.SupportExactFeasibility.exact_implies_support
#print axioms UAVProof.SupportExactFeasibility.exact_has_degrees
#print axioms UAVProof.SupportExactFeasibility.support_implies_exact_of_unique
#print axioms UAVProof.SupportExactFeasibility.support_iff_exact_of_unique
