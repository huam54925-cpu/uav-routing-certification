import LeanCompletion.UAV.SingleVisitDecomposition

namespace UAVProof.VisitCopyLift

variable {V : Type*}

/-- One distinguished depot, plus exactly required v copies
of each non-depot physical vertex. -/
abbrev VisitCopy (depot : V) (required : V → ℕ) :=
  Option (Σ v : {v : V // v ≠ depot}, Fin (required v.val))

/-- Project an occurrence copy to its physical vertex. -/
def project (depot : V) (required : V → ℕ) :
    VisitCopy depot required → V
  | none => depot
  | some a => a.1.val

/-- The only copy projecting to the physical depot is
the distinguished copy depot. -/
theorem project_eq_depot_iff
    (depot : V) (required : V → ℕ)
    (c : VisitCopy depot required) :
    project depot required c = depot ↔ c = none := by
  cases c with
  | none =>
      simp [project]
  | some a =>
      constructor
      · intro h
        exact (a.1.property h).elim
      · intro h
        cases h

/-- Every task occurrence inherits its physical service fee.
The distinguished depot has zero service fee. -/
def copyService
    (depot : V) (required : V → ℕ)
    (service : V → ℚ) :
    VisitCopy depot required → ℚ
  | none => 0
  | some a => service a.1.val

theorem copyService_nonneg
    (depot : V) (required : V → ℕ)
    (service : V → ℚ)
    (hservice : ∀ v, 0 ≤ service v) :
    ∀ c : VisitCopy depot required,
      0 ≤ copyService depot required service c := by
  intro c
  cases c with
  | none =>
      simp [copyService]
  | some a =>
      exact hservice a.1.val

section FlowProjection

variable {W : Type*}
variable [DecidableEq V] [Fintype W]

/-- Aggregate copy-level arc multiplicities over the two
projection fibers. This also handles depot arcs. -/
def projectFlow
    (π : W → V)
    (y : W → W → ℕ)
    (u v : V) : ℕ :=
  ∑ a ∈ Finset.univ.filter (fun a => π a = u),
    ∑ b ∈ Finset.univ.filter (fun b => π b = v),
      y a b

/-- Every copy arc is bounded by its corresponding
aggregated physical arc. -/
theorem entry_le_projectFlow
    (π : W → V) (y : W → W → ℕ)
    (source target : W) :
    y source target ≤
      projectFlow π y (π source) (π target) := by
  classical
  have hinner :
      y source target ≤
        ∑ q ∈ Finset.univ.filter
          (fun q => π q = π target), y source q := by
    exact Finset.single_le_sum
      (s := Finset.univ.filter
        (fun q => π q = π target))
      (f := fun q => y source q)
      (a := target)
      (fun q _ => Nat.zero_le (y source q))
      (by simp)

  have houter :
      (∑ q ∈ Finset.univ.filter
        (fun q => π q = π target), y source q) ≤
      projectFlow π y (π source) (π target) := by
    unfold projectFlow
    exact Finset.single_le_sum
      (s := Finset.univ.filter
        (fun p => π p = π source))
      (f := fun p =>
        ∑ q ∈ Finset.univ.filter
          (fun q => π q = π target), y p q)
      (a := source)
      (fun p _ => Nat.zero_le _)
      (by simp)

  exact hinner.trans houter

/-- Exact projection to a loop-free physical flow forbids
positive arcs between copies of the same physical vertex. -/
theorem zero_of_same_projection
    (π : W → V)
    (y : W → W → ℕ)
    (x : V → V → ℕ)
    (hExact : ∀ u v, projectFlow π y u v = x u v)
    (hloop : ∀ v, x v v = 0)
    (a b : W)
    (hsame : π a = π b) :
    y a b = 0 := by
  have hbound := entry_le_projectFlow π y a b

  have hzero :
      projectFlow π y (π a) (π b) = 0 := by
    rw [hExact, ← hsame, hloop]

  rw [hzero] at hbound
  omega

/-- In particular, every exact lift of a loop-free physical
flow is itself loop-free. -/
theorem lift_no_self_loops
    (π : W → V)
    (y : W → W → ℕ)
    (x : V → V → ℕ)
    (hExact : ∀ u v, projectFlow π y u v = x u v)
    (hloop : ∀ v, x v v = 0) :
    ∀ a, y a a = 0 := by
  intro a
  exact zero_of_same_projection
    π y x hExact hloop a a rfl

end FlowProjection
section RouteProjection

variable {W : Type*}

/-- Map a legal route through a projection whose depot fiber
is a singleton, provided projected adjacent vertices differ. -/
def mapLegalRoute
    (π : W → V)
    (copyDepot : W) (depot : V)
    (hdepot : π copyDepot = depot)
    (honlyDepot : ∀ w, π w = depot → w = copyDepot)
    (r : LegalRoute copyDepot)
    (hseparate :
      r.vertices.IsChain (fun a b => π a ≠ π b)) :
    LegalRoute depot where
  visits := r.visits.map π

  visits_nonempty := by
    intro hempty
    have hnil : r.visits = [] := by
      simpa using hempty
    exact r.visits_nonempty hnil

  depot_not_mem := by
    intro hmem
    obtain ⟨w, hw, heq⟩ := List.mem_map.mp hmem
    have hwdepot : w = copyDepot :=
      honlyDepot w heq
    subst w
    exact r.depot_not_mem hw

  adjacent_ne := by
    have hm :
        (r.vertices.map π).IsChain (· ≠ ·) :=
      (List.isChain_map π).mpr hseparate
    simpa [
      LegalRoute.vertices,
      depotRoute,
      hdepot
    ] using hm

/-- The complete projected vertex sequence is exactly the
map of the original sequence, including both depot endpoints. -/
theorem mapLegalRoute_vertices
    (π : W → V)
    (copyDepot : W) (depot : V)
    (hdepot : π copyDepot = depot)
    (honlyDepot : ∀ w, π w = depot → w = copyDepot)
    (r : LegalRoute copyDepot)
    (hseparate :
      r.vertices.IsChain (fun a b => π a ≠ π b)) :
    (mapLegalRoute
      π copyDepot depot hdepot honlyDepot r hseparate).vertices =
      r.vertices.map π := by
  simp [
    mapLegalRoute,
    LegalRoute.vertices,
    depotRoute,
    hdepot
  ]

/-- A route supported by an exact lift of a loop-free physical
flow has distinct projected endpoints on every consecutive edge. -/
theorem projection_separates_supported_route
    [DecidableEq V] [Fintype W]
    (π : W → V)
    (y : W → W → ℕ)
    (x : V → V → ℕ)
    (hExact : ∀ u v, projectFlow π y u v = x u v)
    (hloop : ∀ v, x v v = 0)
    (copyDepot : W)
    (r : LegalRoute copyDepot)
    (hsupport :
      r.vertices.IsChain (fun a b => 0 < y a b)) :
    r.vertices.IsChain (fun a b => π a ≠ π b) := by
  apply hsupport.imp
  intro a b hab hsame
  have hzero : y a b = 0 :=
    zero_of_same_projection
      π y x hExact hloop a b hsame
  omega

end RouteProjection

/-- Project a supported occurrence-copy route to a legal
physical route. Nonconsecutive repeated physical visits remain allowed. -/
def projectSupportedCopyRoute
    [Fintype V] [DecidableEq V]
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required →
      VisitCopy depot required → ℕ)
    (x : V → V → ℕ)
    (hExact : ∀ u v,
      projectFlow (project depot required) y u v = x u v)
    (hloop : ∀ v, x v v = 0)
    (r : LegalRoute (none : VisitCopy depot required))
    (hsupport :
      r.vertices.IsChain (fun a b => 0 < y a b)) :
    LegalRoute depot :=
  mapLegalRoute
    (project depot required)
    (none : VisitCopy depot required)
    depot
    rfl
    (fun c hc =>
      (project_eq_depot_iff depot required c).mp hc)
    r
    (projection_separates_supported_route
      (project depot required)
      y x hExact hloop
      (none : VisitCopy depot required)
      r hsupport)























end UAVProof.VisitCopyLift

#print axioms UAVProof.VisitCopyLift.project_eq_depot_iff
#print axioms UAVProof.VisitCopyLift.copyService_nonneg
#print axioms UAVProof.VisitCopyLift.entry_le_projectFlow
#print axioms UAVProof.VisitCopyLift.zero_of_same_projection
#print axioms UAVProof.VisitCopyLift.lift_no_self_loops
#print axioms UAVProof.VisitCopyLift.mapLegalRoute
#print axioms UAVProof.VisitCopyLift.mapLegalRoute_vertices
#print axioms UAVProof.VisitCopyLift.projection_separates_supported_route
#print axioms UAVProof.VisitCopyLift.projectSupportedCopyRoute
