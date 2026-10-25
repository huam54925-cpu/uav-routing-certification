import LeanCompletion.UAV.SingleVisitDecomposition
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin


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


















section VisitCounting

variable {W : Type*}
variable [DecidableEq V] [DecidableEq W] [Fintype W]


/-- Counting a physical vertex after projection equals the
sum of occurrence counts over its projection fiber. -/
theorem count_map_eq_fiber_sum
    [BEq V] [LawfulBEq V]
    [BEq W] [LawfulBEq W]
    (π : W → V) (visits : List W) (v : V) :
    (visits.map π).count v =
      ∑ w ∈ Finset.univ.filter (fun w => π w = v),
        visits.count w := by
  classical
  induction visits with
  | nil =>
      simp
  | cons a visits ih =>
      have hdelta :
          (∑ w ∈ Finset.univ.filter (fun w => π w = v),
            if a = w then (1 : ℕ) else 0) =
          (if π a = v then 1 else 0) := by
        by_cases ha : π a = v
        · rw [if_pos ha]
          calc
            (∑ w ∈ Finset.univ.filter (fun w => π w = v),
              if a = w then (1 : ℕ) else 0) =
                (if a = a then 1 else 0) := by
              apply Finset.sum_eq_single a
              · intro w hw hwa
                exact if_neg (Ne.symm hwa)
              · intro hnot
                exact
                  (hnot (Finset.mem_filter.mpr
                    ⟨Finset.mem_univ a, ha⟩)).elim
            _ = 1 := if_pos rfl

        · rw [if_neg ha]
          apply Finset.sum_eq_zero
          intro w hw
          have hne : a ≠ w := by
            intro heq
            have hwproj : π w = v :=
              (Finset.mem_filter.mp hw).2
            apply ha
            exact (congrArg π heq).trans hwproj
          exact if_neg hne

      calc
        ((a :: visits).map π).count v =
            (visits.map π).count v +
              (if π a = v then 1 else 0) := by
          simp only [
            List.map_cons,
            List.count_cons,
            beq_iff_eq
          ]

        _ =
            (∑ w ∈ Finset.univ.filter (fun w => π w = v),
              visits.count w) +
            (∑ w ∈ Finset.univ.filter (fun w => π w = v),
              if a = w then (1 : ℕ) else 0) := by
          rw [ih, hdelta]

        _ =
            ∑ w ∈ Finset.univ.filter (fun w => π w = v),
              (a :: visits).count w := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro w hw
          simp only [List.count_cons, beq_iff_eq]

/-- Aggregate visit counts commute with route projection. -/
theorem totalVisitCount_mapLegalRoute
    {ι : Type*} [Fintype ι]
    (π : W → V)
    (copyDepot : W) (depot : V)
    (hdepot : π copyDepot = depot)
    (honlyDepot : ∀ w, π w = depot → w = copyDepot)
    (routes : ι → LegalRoute copyDepot)
    (hseparate : ∀ d,
      (routes d).vertices.IsChain
        (fun a b => π a ≠ π b))
    (v : V) :
    totalVisitCount Finset.univ
      (fun d =>
        mapLegalRoute π copyDepot depot
          hdepot honlyDepot (routes d) (hseparate d)) v =
      ∑ w ∈ Finset.univ.filter (fun w => π w = v),
        totalVisitCount Finset.univ routes w := by
  classical
  unfold totalVisitCount
  change
    (∑ d, ((routes d).visits.map π).count v) =
      ∑ w ∈ Finset.univ.filter (fun w => π w = v),
        ∑ d, (routes d).visits.count w
  simp_rw [count_map_eq_fiber_sum]
  exact Finset.sum_comm

/-- If each non-depot copy is visited exactly once, the
projected number of visits to a task is its fiber cardinality. -/
theorem mapped_count_eq_fiber_card
    {ι : Type*} [Fintype ι]
    (π : W → V)
    (copyDepot : W) (depot : V)
    (hdepot : π copyDepot = depot)
    (honlyDepot : ∀ w, π w = depot → w = copyDepot)
    (routes : ι → LegalRoute copyDepot)
    (hseparate : ∀ d,
      (routes d).vertices.IsChain
        (fun a b => π a ≠ π b))
    (hcopies : ∀ w, w ≠ copyDepot →
      totalVisitCount Finset.univ routes w = 1)
    (v : V)
    (hv : v ≠ depot) :
    totalVisitCount Finset.univ
      (fun d =>
        mapLegalRoute π copyDepot depot
          hdepot honlyDepot (routes d) (hseparate d)) v =
      (Finset.univ.filter (fun w : W => π w = v)).card := by
  classical

  rw [totalVisitCount_mapLegalRoute
    π copyDepot depot hdepot honlyDepot routes hseparate v]

  calc
    (∑ w ∈ Finset.univ.filter (fun w => π w = v),
      totalVisitCount Finset.univ routes w) =
        ∑ w ∈ Finset.univ.filter (fun w => π w = v),
          (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro w hw

      have hwproj : π w = v :=
        (Finset.mem_filter.mp hw).2

      have hwne : w ≠ copyDepot := by
        intro heq
        subst w
        exact hv (hwproj.symm.trans hdepot)

      exact hcopies w hwne

    _ = (Finset.univ.filter
        (fun w : W => π w = v)).card := by
      simp

end VisitCounting

/-- The copies over a non-depot task are equivalent to
the prescribed finite set of occurrence indices. -/
def taskFiberEquivFin
    (depot : V) (required : V → ℕ)
    (v : V) (hv : v ≠ depot) :
    {c : VisitCopy depot required //
      project depot required c = v} ≃
      Fin (required v) where
  toFun := fun c => by
    rcases c with ⟨c, hc⟩
    cases c with
    | none =>
        exact (hv hc.symm).elim
    | some a =>
        rcases a with ⟨⟨u, hu⟩, k⟩
        change u = v at hc
        subst u
        exact k

  invFun := fun k =>
    ⟨some ⟨⟨v, hv⟩, k⟩, rfl⟩

  left_inv := by
    intro c
    rcases c with ⟨c, hc⟩
    cases c with
    | none =>
        exact (hv hc.symm).elim
    | some a =>
        rcases a with ⟨⟨u, hu⟩, k⟩
        change u = v at hc
        subst u
        rfl

  right_inv := by
    intro k
    rfl

/-- The physical task fiber has exactly its required number
of occurrence copies. -/
theorem taskFiber_card
    [Fintype V] [DecidableEq V]
    (depot : V) (required : V → ℕ)
    (v : V) (hv : v ≠ depot) :
    (Finset.univ.filter
      (fun c : VisitCopy depot required =>
        project depot required c = v)).card =
      required v := by
  classical
  have hcard :=
    Fintype.card_congr
      (taskFiberEquivFin depot required v hv)
  simpa only [
    Fintype.card_subtype,
    Fintype.card_fin
  ] using hcard

/-- Exact single-visit coverage of all occurrence copies
projects to the prescribed physical visit counts. -/
theorem projected_copy_routes_cover
    [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required →
      VisitCopy depot required → ℕ)
    (x : V → V → ℕ)
    (hExact : ∀ u v,
      projectFlow (project depot required) y u v = x u v)
    (hloop : ∀ v, x v v = 0)
    (routes :
      ι → LegalRoute (none : VisitCopy depot required))
    (hsupport : ∀ d,
      (routes d).vertices.IsChain
        (fun a b => 0 < y a b))
    (hcopies : ∀ c : VisitCopy depot required,
      c ≠ none →
      totalVisitCount Finset.univ routes c = 1) :
    ∀ v, v ≠ depot →
      totalVisitCount Finset.univ
        (fun d =>
          projectSupportedCopyRoute
            depot required y x hExact hloop
            (routes d) (hsupport d)) v =
        required v := by
  classical
  intro v hv

  have hcount :=
    mapped_count_eq_fiber_card
      (project depot required)
      (none : VisitCopy depot required)
      depot
      rfl
      (fun c hc =>
        (project_eq_depot_iff depot required c).mp hc)
      routes
      (fun d =>
        projection_separates_supported_route
          (project depot required)
          y x hExact hloop
          (none : VisitCopy depot required)
          (routes d) (hsupport d))
      hcopies
      v hv

  calc
    totalVisitCount Finset.univ
        (fun d =>
          projectSupportedCopyRoute
            depot required y x hExact hloop
            (routes d) (hsupport d)) v =
        (Finset.univ.filter
          (fun c : VisitCopy depot required =>
            project depot required c = v)).card := by
      simpa only [projectSupportedCopyRoute] using hcount

    _ = required v :=
      taskFiber_card depot required v hv


section EdgeProjection

variable {W : Type*}
variable [DecidableEq V] [DecidableEq W] [Fintype W]

/-- Projecting a vertex sequence aggregates its edge counts
over the corresponding pairs of projection fibers. -/
theorem routeFlow_map
    (π : W → V) (route : List W)
    (u v : V) :
    routeFlow (route.map π) u v =
      projectFlow π (routeFlow route) u v := by
  classical

  have htail :
      (route.map π).tail = route.tail.map π := by
    cases route <;> rfl

  have hcount :
      ((route.zip route.tail).map (Prod.map π π)).count (u, v) =
        ∑ p ∈ Finset.univ.filter
          (fun p : W × W => (π p.1, π p.2) = (u, v)),
          (route.zip route.tail).count p :=
    count_map_eq_fiber_sum
      (V := V × V)
      (W := W × W)
      (Prod.map π π)
      (route.zip route.tail)
      (u, v)

  calc
    routeFlow (route.map π) u v =
        ((route.zip route.tail).map
          (Prod.map π π)).count (u, v) := by
      unfold routeFlow
      rw [htail, List.zip_map]

    _ =
        (∑ p ∈ Finset.univ.filter
          (fun p : W × W => (π p.1, π p.2) = (u, v)),
          (route.zip route.tail).count p) :=
      hcount

    _ = projectFlow π (routeFlow route) u v := by
      unfold projectFlow routeFlow
      simp only [
        Finset.sum_filter,
        Fintype.sum_prod_type,
        Prod.mk.injEq
      ]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hsource : π a = u
      · simp [hsource]
      · simp [hsource]

omit [DecidableEq W] in
/-- Flow projection commutes with finite summation. -/
theorem projectFlow_sum
    {ι : Type*} [Fintype ι]
    (π : W → V)
    (flows : ι → W → W → ℕ)
    (u v : V) :
    projectFlow π (fun a b => ∑ d, flows d a b) u v =
      ∑ d, projectFlow π (flows d) u v := by
  classical
  unfold projectFlow

  calc
    (∑ a ∈ Finset.univ.filter (fun a => π a = u),
      ∑ b ∈ Finset.univ.filter (fun b => π b = v),
        ∑ d, flows d a b) =
      ∑ a ∈ Finset.univ.filter (fun a => π a = u),
        ∑ d,
          ∑ b ∈ Finset.univ.filter (fun b => π b = v),
            flows d a b := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm

    _ =
      ∑ d,
        ∑ a ∈ Finset.univ.filter (fun a => π a = u),
          ∑ b ∈ Finset.univ.filter (fun b => π b = v),
            flows d a b := by
      exact Finset.sum_comm

/-- Aggregate route flow commutes with legal-route projection. -/
theorem totalRouteFlow_mapLegalRoute
    {ι : Type*} [Fintype ι]
    (π : W → V)
    (copyDepot : W) (depot : V)
    (hdepot : π copyDepot = depot)
    (honlyDepot : ∀ w, π w = depot → w = copyDepot)
    (routes : ι → LegalRoute copyDepot)
    (hseparate : ∀ d,
      (routes d).vertices.IsChain
        (fun a b => π a ≠ π b))
    (u v : V) :
    totalRouteFlow Finset.univ
      (fun d =>
        mapLegalRoute π copyDepot depot
          hdepot honlyDepot (routes d) (hseparate d)) u v =
      projectFlow π
        (totalRouteFlow Finset.univ routes) u v := by
  classical

  change
    (∑ d,
      routeFlow
        (mapLegalRoute π copyDepot depot
          hdepot honlyDepot
          (routes d) (hseparate d)).vertices u v) =
      projectFlow π
        (fun a b => ∑ d, routeFlow (routes d).vertices a b) u v

  simp_rw [mapLegalRoute_vertices, routeFlow_map]

  exact
    (projectFlow_sum π
      (fun d => routeFlow (routes d).vertices) u v).symm

end EdgeProjection

/-- Exact decomposition of the copy flow and exact projection
of that flow imply exact recovery of the physical flow. -/
theorem projected_copy_routes_exact
    [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required →
      VisitCopy depot required → ℕ)
    (x : V → V → ℕ)
    (hExact : ∀ u v,
      projectFlow (project depot required) y u v = x u v)
    (hloop : ∀ v, x v v = 0)
    (routes :
      ι → LegalRoute (none : VisitCopy depot required))
    (hsupport : ∀ d,
      (routes d).vertices.IsChain
        (fun a b => 0 < y a b))
    (hrouteExact : ∀ a b,
      totalRouteFlow Finset.univ routes a b = y a b) :
    ∀ u v,
      totalRouteFlow Finset.univ
        (fun d =>
          projectSupportedCopyRoute
            depot required y x hExact hloop
            (routes d) (hsupport d)) u v =
        x u v := by
  classical
  intro u v

  have hflowEq :
      totalRouteFlow Finset.univ routes = y :=
    funext (fun a => funext (hrouteExact a))

  have hmap :=
    totalRouteFlow_mapLegalRoute
      (project depot required)
      (none : VisitCopy depot required)
      depot
      rfl
      (fun c hc =>
        (project_eq_depot_iff depot required c).mp hc)
      routes
      (fun d =>
        projection_separates_supported_route
          (project depot required)
          y x hExact hloop
          (none : VisitCopy depot required)
          (routes d) (hsupport d))
      u v

  calc
    totalRouteFlow Finset.univ
        (fun d =>
          projectSupportedCopyRoute
            depot required y x hExact hloop
            (routes d) (hsupport d)) u v =
      projectFlow (project depot required)
        (totalRouteFlow Finset.univ routes) u v := by
      simpa only [projectSupportedCopyRoute] using hmap

    _ = projectFlow (project depot required) y u v := by
      rw [hflowEq]

    _ = x u v := hExact u v

section ServiceProjection

variable {W : Type*}
variable [Fintype V] [DecidableEq V]
variable [Fintype W] [DecidableEq W]

/-- Service on a projected route equals service on the
original route with fees pulled back along the projection. -/
theorem routeServiceIn_mapLegalRoute
    (π : W → V)
    (copyDepot : W) (depot : V)
    (hdepot : π copyDepot = depot)
    (honlyDepot : ∀ w, π w = depot → w = copyDepot)
    (r : LegalRoute copyDepot)
    (hseparate :
      r.vertices.IsChain (fun a b => π a ≠ π b))
    (service : V → ℚ) :
    ResourceCuts.routeServiceIn
      (mapLegalRoute π copyDepot depot
        hdepot honlyDepot r hseparate)
      Finset.univ service =
    ResourceCuts.routeServiceIn
      r Finset.univ (fun w => service (π w)) := by
  classical
  unfold ResourceCuts.routeServiceIn

  change
    (∑ v, service v *
      (((r.visits.map π).count v : ℕ) : ℚ)) =
    ∑ w, service (π w) * (r.visits.count w : ℚ)

  simp_rw [count_map_eq_fiber_sum]
  simp only [Nat.cast_sum, Finset.mul_sum]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  simp

end ServiceProjection

/-- Occurrence-copy fees and physical per-visit fees give
exactly the same service cost on a projected route. -/
theorem projected_copy_route_service
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
      r.vertices.IsChain (fun a b => 0 < y a b))
    (service : V → ℚ) :
    ResourceCuts.routeServiceIn
      (projectSupportedCopyRoute
        depot required y x hExact hloop r hsupport)
      Finset.univ service =
    ResourceCuts.routeServiceIn
      r Finset.univ (copyService depot required service) := by
  classical

  have hmap :=
    routeServiceIn_mapLegalRoute
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
      service

  calc
    ResourceCuts.routeServiceIn
        (projectSupportedCopyRoute
          depot required y x hExact hloop r hsupport)
        Finset.univ service =
      ResourceCuts.routeServiceIn r Finset.univ
        (fun c => service (project depot required c)) := by
      simpa only [projectSupportedCopyRoute] using hmap

    _ =
      ResourceCuts.routeServiceIn r Finset.univ
        (copyService depot required service) := by
      unfold ResourceCuts.routeServiceIn
      apply Finset.sum_congr rfl
      intro c hc
      cases c with
      | none =>
          letI : BEq (VisitCopy depot required) :=
            instBEqOfDecidableEq

          have hzero :
              r.visits.count
                (none : VisitCopy depot required) = 0 :=
            List.count_eq_zero.mpr r.depot_not_mem

          simp only [hzero, Nat.cast_zero, mul_zero]
      | some a =>
          rfl

/-- A supported copy route satisfying its service budget
projects to a physical route satisfying the same budget. -/
theorem projected_copy_route_budget
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
      r.vertices.IsChain (fun a b => 0 < y a b))
    (service : V → ℚ) (T : ℚ)
    (hbudget :
      ResourceCuts.routeServiceIn r Finset.univ
        (copyService depot required service) ≤ T) :
    ResourceCuts.routeServiceIn
      (projectSupportedCopyRoute
        depot required y x hExact hloop r hsupport)
      Finset.univ service ≤ T := by
  rw [projected_copy_route_service
    depot required y x hExact hloop r hsupport service]
  exact hbudget

/-- If every consecutive edge satisfies a relation, the list
is a chain for that relation. -/
theorem isChain_of_zip_edges
    {W : Type*}
    (R : W → W → Prop)
    (route : List W)
    (hedges : ∀ a b,
      (a, b) ∈ route.zip route.tail → R a b) :
    route.IsChain R := by
  induction route with
  | nil =>
      simp
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp
      | cons b tail =>
          apply List.isChain_cons_cons.mpr
          constructor
          · apply hedges a b
            simp
          · apply ih
            intro u v huv
            apply hedges u v
            simp only [
              List.tail_cons,
              List.zip_cons_cons,
              List.mem_cons
            ]
            exact Or.inr huv

/-- An exact nonnegative route-flow decomposition automatically
supports every edge of each constituent route. -/
theorem exact_family_supported
    {W : Type*} [DecidableEq W]
    {ι : Type*} [Fintype ι]
    (depot : W)
    (routes : ι → LegalRoute depot)
    (y : W → W → ℕ)
    (hExact : ∀ a b,
      totalRouteFlow Finset.univ routes a b = y a b) :
    ∀ d, (routes d).vertices.IsChain
      (fun a b => 0 < y a b) := by
  classical
  intro d
  apply isChain_of_zip_edges
  intro a b hedge

  have hpositive :
      0 < routeFlow (routes d).vertices a b := by
    have hne :
        routeFlow (routes d).vertices a b ≠ 0 := by
      intro hzero
      unfold routeFlow at hzero
      exact (List.count_eq_zero.mp hzero) hedge
    omega

  have hle :
      routeFlow (routes d).vertices a b ≤
        totalRouteFlow Finset.univ routes a b := by
    unfold totalRouteFlow
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun e =>
        routeFlow (routes e).vertices a b)
      (a := d)
      (fun e _ => Nat.zero_le _)
      (Finset.mem_univ d)

  rw [hExact a b] at hle
  exact lt_of_lt_of_le hpositive hle

/-- A copy flow with unit task degrees, positive depot-free
cuts and rounded service-capacity cuts yields a budget-feasible
exact physical route decomposition.

The copy route family is constructed, not assumed.
The number of physical routes equals the physical depot outflow. -/
theorem exists_exact_decomposition_of_copy_lift
    [Fintype V] [DecidableEq V]
    (depot : V)
    (required : V → ℕ)
    (x : V → V → ℕ)
    (y : VisitCopy depot required →
      VisitCopy depot required → ℕ)
    (hExact : ∀ u v,
      projectFlow (project depot required) y u v = x u v)
    (hloop : ∀ v, x v v = 0)
    (hout : ∀ c : VisitCopy depot required,
      c ≠ none → outFlow Finset.univ y c = 1)
    (hin : ∀ c : VisitCopy depot required,
      c ≠ none → inFlow Finset.univ y c = 1)
    (hconn : ∀ S : Finset (VisitCopy depot required),
      S.Nonempty → none ∉ S → 1 ≤ outCutFlow S y)
    (service : V → ℚ)
    (T : ℚ)
    (hT : 0 < T)
    (hcuts : ∀ S : Finset (VisitCopy depot required),
      S.Nonempty → none ∉ S →
      Int.ceil
        ((∑ c ∈ S, copyService depot required service c) / T) ≤
          (outCutFlow S y : ℤ)) :
    ∃ routes :
        {c : VisitCopy depot required // 0 < y none c} →
          LegalRoute depot,
      (∀ v, v ≠ depot →
        totalVisitCount Finset.univ routes v = required v) ∧
      (∀ u v,
        totalRouteFlow Finset.univ routes u v = x u v) ∧
      (Fintype.card
          {c : VisitCopy depot required // 0 < y none c} =
        outFlow Finset.univ x depot) ∧
      (∀ d,
        ResourceCuts.routeServiceIn
          (routes d) Finset.univ service ≤ T) := by
  classical

  have hyloop :
      ∀ c : VisitCopy depot required, y c c = 0 :=
    lift_no_self_loops
      (project depot required) y x hExact hloop

  obtain ⟨copyRoutes, _hnodup, hcopyCounts,
      hcopyExact, _hcopyCard, hcopyBudget⟩ :=
    SingleVisitDecomposition.exists_budget_feasible_singleVisit_decomposition
      y
      (none : VisitCopy depot required)
      hout hin hconn hyloop
      (copyService depot required service)
      T hT hcuts

  have hsupport :
      ∀ d, (copyRoutes d).vertices.IsChain
        (fun a b => 0 < y a b) :=
    exact_family_supported
      (none : VisitCopy depot required)
      copyRoutes y hcopyExact

  let routes :
      {c : VisitCopy depot required // 0 < y none c} →
        LegalRoute depot :=
    fun d =>
      projectSupportedCopyRoute
        depot required y x hExact hloop
        (copyRoutes d) (hsupport d)

  have hcounts :
      ∀ v, v ≠ depot →
        totalVisitCount Finset.univ routes v = required v := by
    simpa only [routes] using
      (projected_copy_routes_cover
        depot required y x hExact hloop
        copyRoutes hsupport hcopyCounts)

  have hphysicalExact :
      ∀ u v,
        totalRouteFlow Finset.univ routes u v = x u v := by
    simpa only [routes] using
      (projected_copy_routes_exact
        depot required y x hExact hloop
        copyRoutes hsupport hcopyExact)

  have hflowEq :
      totalRouteFlow Finset.univ routes = x :=
    funext (fun u => funext (hphysicalExact u))

  have hcard :
      Fintype.card
          {c : VisitCopy depot required // 0 < y none c} =
        outFlow Finset.univ x depot := by
    have h :=
      total_outFlow_depot_eq_card Finset.univ routes
    rw [hflowEq] at h
    simpa only [Finset.card_univ] using h.symm

  refine ⟨routes, hcounts, hphysicalExact, hcard, ?_⟩
  intro d
  change ResourceCuts.routeServiceIn
    (projectSupportedCopyRoute
      depot required y x hExact hloop
      (copyRoutes d) (hsupport d))
    Finset.univ service ≤ T
  exact projected_copy_route_budget
    depot required y x hExact hloop
    (copyRoutes d) (hsupport d)
    service T (hcopyBudget d)

/-- A visit position consists of a route identifier and
a valid index in that route's inspection list. -/
abbrev VisitPosition
    {ι : Type*} {depot : V}
    (routes : ι → LegalRoute depot) :=
  Σ d : ι, Fin (routes d).visits.length

/-- The physical vertex inspected at a visit position. -/
def positionVertex
    {ι : Type*} {depot : V}
    (routes : ι → LegalRoute depot)
    (p : VisitPosition routes) : V :=
  (routes p.1).visits.get p.2

/-- Inspection positions never represent the depot. -/
theorem positionVertex_ne_depot
    {ι : Type*} {depot : V}
    (routes : ι → LegalRoute depot)
    (p : VisitPosition routes) :
    positionVertex routes p ≠ depot := by
  intro h
  have hmem :
      positionVertex routes p ∈ (routes p.1).visits := by
    exact List.get_mem _ _
  rw [h] at hmem
  exact (routes p.1).depot_not_mem hmem

/-- The number of list positions carrying a vertex equals
its list count. Repeated entries are counted separately. -/
theorem card_get_fiber_eq_count
    [DecidableEq V]
    (visits : List V)
    (v : V) :
    Fintype.card
      {k : Fin visits.length // visits.get k = v} =
        visits.count v := by
  classical

  have hmap :=
    count_map_eq_fiber_sum
      (V := V)
      (W := Fin visits.length)
      visits.get
      (List.finRange visits.length)
      v

  have hlist :
      (List.finRange visits.length).map visits.get =
        visits := by
    rw [← List.ofFn_eq_map, List.ofFn_get]

  rw [hlist] at hmap
  rw [Fintype.card_subtype]
  simpa using hmap.symm

/-- Counting all route positions over a physical vertex gives
the aggregate inspection count at that vertex. -/
theorem visitPosition_fiber_card
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    {depot : V}
    (routes : ι → LegalRoute depot)
    (v : V) :
    Fintype.card
      {p : VisitPosition routes //
        positionVertex routes p = v} =
      totalVisitCount Finset.univ routes v := by
  classical

  change
    Fintype.card
      {p : (Σ d : ι, Fin (routes d).visits.length) //
        (routes p.1).visits.get p.2 = v} =
      totalVisitCount Finset.univ routes v

  rw [
    Fintype.card_subtype,
    Finset.card_eq_sum_ones,
    Finset.sum_filter,
    Fintype.sum_sigma
  ]
  unfold totalVisitCount
  apply Finset.sum_congr rfl
  intro d hd

  have h :=
    card_get_fiber_eq_count (routes d).visits v

  rw [
    Fintype.card_subtype,
    Finset.card_eq_sum_ones,
    Finset.sum_filter
  ] at h

  exact h

/-- Exact physical coverage fixes the cardinality of
each non-depot visit-position fiber. -/
theorem visitPosition_fiber_card_eq_required
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (v : V)
    (hv : v ≠ depot) :
    Fintype.card
      {p : VisitPosition routes //
        positionVertex routes p = v} =
      required v := by
  exact
    (visitPosition_fiber_card routes v).trans
      (hcounts v hv)

/-- Assign distinct occurrence indices to all actual visits
of a task. This is an existence-level numbering choice. -/
noncomputable def visitPositionFiberEquivFin
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (v : V)
    (hv : v ≠ depot) :
    {p : VisitPosition routes //
      positionVertex routes p = v} ≃
      Fin (required v) := by
  classical
  exact Fintype.equivFinOfCardEq
    (visitPosition_fiber_card_eq_required
      depot required routes hcounts v hv)

/-- Partition all visit positions by their physical task.
The inverse simply forgets the task label. -/
def visitPositionTaskFiberEquiv
    {ι : Type*}
    (depot : V)
    (routes : ι → LegalRoute depot) :
    VisitPosition routes ≃
      (Σ v : {v : V // v ≠ depot},
        {p : VisitPosition routes //
          positionVertex routes p = v.val}) where
  toFun := fun p =>
    ⟨⟨positionVertex routes p,
        positionVertex_ne_depot routes p⟩,
      ⟨p, rfl⟩⟩

  invFun := fun q => q.2.val

  left_inv := by
    intro p
    rfl

  right_inv := by
    rintro ⟨⟨v, hv⟩, ⟨p, hp⟩⟩
    change positionVertex routes p = v at hp
    subst v
    rfl

/-- All actual visit positions are in bijection with the
canonical task copies. The distinguished depot is excluded. -/
noncomputable def visitPositionCopiesEquiv
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v) :
    VisitPosition routes ≃
      (Σ v : {v : V // v ≠ depot}, Fin (required v.val)) :=
  (visitPositionTaskFiberEquiv depot routes).trans
    (Equiv.sigmaCongrRight
      (fun v : {v : V // v ≠ depot} =>
        visitPositionFiberEquivFin
          depot required routes hcounts v.val v.property))

/-- Assign a canonical non-depot copy to an actual visit position. -/
noncomputable def positionCopy
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (p : VisitPosition routes) :
    VisitCopy depot required :=
  some (visitPositionCopiesEquiv
    depot required routes hcounts p)

/-- The assigned copy projects to the task at the original position. -/
theorem positionCopy_project
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (p : VisitPosition routes) :
    project depot required
      (positionCopy depot required routes hcounts p) =
      positionVertex routes p := by
  rfl

/-- No inspection position is assigned the distinguished depot copy. -/
theorem positionCopy_ne_none
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (p : VisitPosition routes) :
    positionCopy depot required routes hcounts p ≠ none := by
  intro h
  change
    some (visitPositionCopiesEquiv
      depot required routes hcounts p) = none at h
  cases h

/-- Different visit positions receive different copies,
including positions on different routes. -/
theorem positionCopy_injective
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v) :
    Function.Injective
      (positionCopy depot required routes hcounts) := by
  intro p q hpq
  apply
    (visitPositionCopiesEquiv
      depot required routes hcounts).injective
  exact Option.some.inj hpq

/-- Replace each physical visit by its assigned occurrence copy,
preserving the original order of positions. -/
noncomputable def liftedVisits
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (d : ι) :
    List (VisitCopy depot required) :=
  List.ofFn
    (fun k : Fin (routes d).visits.length =>
      positionCopy depot required routes hcounts
        (⟨d, k⟩ : VisitPosition routes))

/-- Projecting the lifted inspection list exactly recovers
the original list, including its order and repeated vertices. -/
theorem liftedVisits_map_project
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (d : ι) :
    (liftedVisits depot required routes hcounts d).map
        (project depot required) =
      (routes d).visits := by
  unfold liftedVisits
  rw [List.map_ofFn]
  change
    List.ofFn
      (fun k : Fin (routes d).visits.length =>
        (routes d).visits.get k) =
      (routes d).visits
  exact List.ofFn_get (routes d).visits
/-- Projection recovers the complete original route,
including both depot endpoints. -/
theorem liftedVisits_vertices_map
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (d : ι) :
    (depotRoute
      (none : VisitCopy depot required)
      (liftedVisits depot required routes hcounts d)).map
        (project depot required) =
      (routes d).vertices := by
  change
    (((none : VisitCopy depot required) ::
      liftedVisits depot required routes hcounts d) ++
        [none]).map (project depot required) =
      (depot :: (routes d).visits) ++ [depot]
  rw [List.map_append]
  change
    (depot ::
      (liftedVisits depot required routes hcounts d).map
        (project depot required)) ++ [depot] =
      (depot :: (routes d).visits) ++ [depot]
  rw [liftedVisits_map_project]

/-- Lift a physical legal route by replacing each inspection
position with its assigned canonical copy. -/
noncomputable def liftedLegalRoute
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (d : ι) :
    LegalRoute (none : VisitCopy depot required) where
  visits :=
    liftedVisits depot required routes hcounts d

  visits_nonempty := by
    intro hempty
    have hmap :=
      liftedVisits_map_project
        depot required routes hcounts d
    rw [hempty, List.map_nil] at hmap
    exact (routes d).visits_nonempty hmap.symm

  depot_not_mem := by
    intro hmem
    change
      (none : VisitCopy depot required) ∈
        List.ofFn
          (fun k : Fin (routes d).visits.length =>
            positionCopy depot required routes hcounts
              (⟨d, k⟩ : VisitPosition routes)) at hmem
    obtain ⟨k, hk⟩ := List.mem_ofFn.mp hmem
    exact
      positionCopy_ne_none
        depot required routes hcounts
        (⟨d, k⟩ : VisitPosition routes) hk

  adjacent_ne := by
    have hmap :
        ((depotRoute
          (none : VisitCopy depot required)
          (liftedVisits depot required routes hcounts d)).map
            (project depot required)).IsChain (· ≠ ·) := by
      rw [liftedVisits_vertices_map
        depot required routes hcounts d]
      exact (routes d).adjacent_ne

    have hchain :
        (depotRoute
          (none : VisitCopy depot required)
          (liftedVisits depot required routes hcounts d)).IsChain
            (fun a b =>
              project depot required a ≠
                project depot required b) :=
      (List.isChain_map (project depot required)).mp hmap

    apply hchain.imp
    intro a b hab heq
    exact hab (congrArg (project depot required) heq)

/-- The lifted legal route retains the chosen copy list. -/
theorem liftedLegalRoute_visits
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (d : ι) :
    (liftedLegalRoute
      depot required routes hcounts d).visits =
      liftedVisits depot required routes hcounts d := by
  rfl

/-- The entire lifted legal route projects to the original
vertex sequence, preserving every edge position. -/
theorem liftedLegalRoute_vertices_map
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (d : ι) :
    (liftedLegalRoute
      depot required routes hcounts d).vertices.map
        (project depot required) =
      (routes d).vertices := by
  exact liftedVisits_vertices_map
    depot required routes hcounts d

/-- Counting a value in an indexed list equals the number
of indices that produce that value. -/
theorem count_ofFn_eq_fiber_card
    {W : Type*}
    [DecidableEq W] [BEq W] [LawfulBEq W]
    {n : ℕ}
    (f : Fin n → W)
    (w : W) :
    (List.ofFn f).count w =
      Fintype.card {k : Fin n // f k = w} := by
  classical
  have hmap :=
    count_map_eq_fiber_sum
      (V := W)
      (W := Fin n)
      f
      (List.finRange n)
      w
  rw [← List.ofFn_eq_map] at hmap
  rw [Fintype.card_subtype]
  simpa using hmap

/-- Every canonical task copy has exactly one actual
visit position assigned to it. -/
theorem positionCopy_fiber_card_eq_one
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (c : VisitCopy depot required)
    (hc : c ≠ none) :
    Fintype.card
      {p : VisitPosition routes //
        positionCopy depot required routes hcounts p = c} = 1 := by
  classical
  cases c with
  | none =>
      exact (hc rfl).elim
  | some a =>
      let e := visitPositionCopiesEquiv
        depot required routes hcounts

      have hp :
          positionCopy depot required routes hcounts
            (e.symm a) = some a := by
        change some (e (e.symm a)) = some a
        exact congrArg some (e.apply_symm_apply a)

      letI : Unique
          {p : VisitPosition routes //
            positionCopy depot required routes hcounts p =
              some a} :=
        { default := ⟨e.symm a, hp⟩
          uniq := by
            intro q
            apply Subtype.ext
            exact
              positionCopy_injective
                depot required routes hcounts
                (q.property.trans hp.symm) }

      exact Fintype.card_unique

/-- The constructed legal copy routes visit each non-depot
copy exactly once across the entire route family. -/
theorem liftedLegalRoute_totalVisitCount_eq_one
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v) :
    ∀ c : VisitCopy depot required, c ≠ none →
      totalVisitCount Finset.univ
        (liftedLegalRoute depot required routes hcounts) c = 1 := by
  classical

  -- Match the equality test used inside totalVisitCount.
  letI : BEq (VisitCopy depot required) :=
    instBEqOfDecidableEq

  intro c hc
  change
    (∑ d : ι,
      (List.ofFn
        (fun k : Fin (routes d).visits.length =>
          positionCopy depot required routes hcounts
            (⟨d, k⟩ : VisitPosition routes))).count c) = 1

  calc
    (∑ d : ι,
      (List.ofFn
        (fun k : Fin (routes d).visits.length =>
          positionCopy depot required routes hcounts
            (⟨d, k⟩ : VisitPosition routes))).count c) =
      ∑ d : ι,
        Fintype.card
          {k : Fin (routes d).visits.length //
            positionCopy depot required routes hcounts
              (⟨d, k⟩ : VisitPosition routes) = c} := by
        apply Finset.sum_congr rfl
        intro d hd
        exact count_ofFn_eq_fiber_card
          (fun k : Fin (routes d).visits.length =>
            positionCopy depot required routes hcounts
              (⟨d, k⟩ : VisitPosition routes))
          c

    _ = Fintype.card
        {p : VisitPosition routes //
          positionCopy depot required routes hcounts p = c} := by
      simp only [
        Fintype.card_subtype,
        Finset.card_eq_sum_ones,
        Finset.sum_filter
      ]
      exact
        (Fintype.sum_sigma
          (fun p : VisitPosition routes =>
            if positionCopy depot required routes hcounts p = c
            then (1 : ℕ)
            else 0)).symm

    _ = 1 :=
      positionCopy_fiber_card_eq_one
        depot required routes hcounts c hc

/-- The copy flow obtained by summing the constructed
legal copy routes. -/
noncomputable def liftedFlow
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v) :
    VisitCopy depot required →
      VisitCopy depot required → ℕ :=
  totalRouteFlow Finset.univ
    (liftedLegalRoute depot required routes hcounts)

/-- Every task copy has exactly one incoming and
one outgoing unit of lifted flow. -/
theorem liftedFlow_unit_degrees
    [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v) :
    ∀ c : VisitCopy depot required, c ≠ none →
      outFlow Finset.univ
        (liftedFlow depot required routes hcounts) c = 1 ∧
      inFlow Finset.univ
        (liftedFlow depot required routes hcounts) c = 1 := by
  classical
  intro c hc

  have hvisit :=
    liftedLegalRoute_totalVisitCount_eq_one
      depot required routes hcounts c hc

  constructor
  · exact
      (total_outFlow_eq_visit_count
        Finset.univ
        (liftedLegalRoute depot required routes hcounts)
        c hc).trans hvisit
  · exact
      (total_inFlow_eq_visit_count
        Finset.univ
        (liftedLegalRoute depot required routes hcounts)
        c hc).trans hvisit

/-- The constructed copy flow has no self-loops. -/
theorem liftedFlow_no_self_loops
    [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v) :
    ∀ c : VisitCopy depot required,
      liftedFlow depot required routes hcounts c c = 0 := by
  intro c
  exact total_no_diagonal
    Finset.univ
    (liftedLegalRoute depot required routes hcounts)
    c

/-- Projecting the constructed copy flow recovers the
aggregate flow of the original physical routes. -/
theorem liftedFlow_project
    [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (u v : V) :
    projectFlow (project depot required)
      (liftedFlow depot required routes hcounts) u v =
      totalRouteFlow Finset.univ routes u v := by
  classical

  change
    projectFlow (project depot required)
      (fun a b =>
        ∑ d : ι,
          routeFlow
            (liftedLegalRoute
              depot required routes hcounts d).vertices a b)
      u v =
    ∑ d : ι, routeFlow (routes d).vertices u v

  rw [projectFlow_sum]
  apply Finset.sum_congr rfl
  intro d hd

  calc
    projectFlow (project depot required)
        (routeFlow
          (liftedLegalRoute
            depot required routes hcounts d).vertices)
        u v =
      routeFlow
        ((liftedLegalRoute
          depot required routes hcounts d).vertices.map
            (project depot required))
        u v :=
      (routeFlow_map
        (project depot required)
        (liftedLegalRoute
          depot required routes hcounts d).vertices
        u v).symm

    _ = routeFlow (routes d).vertices u v := by
      rw [liftedLegalRoute_vertices_map
        depot required routes hcounts d]

/-- If the physical routes exactly decompose x, the
constructed copy flow is an exact lift of that same x. -/
theorem liftedFlow_projects_exact
    [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (x : V → V → ℕ)
    (hrouteExact : ∀ u v,
      totalRouteFlow Finset.univ routes u v = x u v) :
    ∀ u v,
      projectFlow (project depot required)
        (liftedFlow depot required routes hcounts) u v =
          x u v := by
  intro u v
  exact
    (liftedFlow_project
      depot required routes hcounts u v).trans
        (hrouteExact u v)

/-- Every nonempty depot-free set of copies has positive
outgoing lifted flow. This follows from legal-route coverage;
connectivity is not assumed. -/
theorem liftedFlow_positive_cuts
    [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v) :
    ∀ S : Finset (VisitCopy depot required),
      S.Nonempty → none ∉ S →
        1 ≤ outCutFlow S
          (liftedFlow depot required routes hcounts) := by
  classical
  intro S hnonempty hdepot

  change
    1 ≤ outCutFlow S
      (totalRouteFlow Finset.univ
        (liftedLegalRoute depot required routes hcounts))

  exact total_outCutFlow_ge_one
    Finset.univ
    (liftedLegalRoute depot required routes hcounts)
    (fun _ : VisitCopy depot required => 1)
    (liftedLegalRoute_totalVisitCount_eq_one
      depot required routes hcounts)
    S
    hnonempty
    hdepot
    (by
      intro c hc
      exact Nat.zero_lt_one)

/-- The constructed copy route has exactly the service cost
of its original physical route. No sign assumption is needed. -/
theorem liftedLegalRoute_service
    [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (service : V → ℚ)
    (d : ι) :
    ResourceCuts.routeServiceIn
      (liftedLegalRoute depot required routes hcounts d)
      Finset.univ (copyService depot required service) =
    ResourceCuts.routeServiceIn
      (routes d) Finset.univ service := by
  classical

  let copyRoutes :=
    liftedLegalRoute depot required routes hcounts
  let y := liftedFlow depot required routes hcounts
  let x := totalRouteFlow Finset.univ routes

  have hExact :
      ∀ u v,
        projectFlow (project depot required) y u v = x u v :=
    liftedFlow_project depot required routes hcounts

  have hloop : ∀ v, x v v = 0 :=
    total_no_diagonal Finset.univ routes

  have hsupport :
      ∀ e, (copyRoutes e).vertices.IsChain
        (fun a b => 0 < y a b) :=
    exact_family_supported
      (none : VisitCopy depot required)
      copyRoutes y
      (by
        intro a b
        rfl)

  let projectedRoute : LegalRoute depot :=
    projectSupportedCopyRoute
      depot required y x hExact hloop
      (copyRoutes d) (hsupport d)

  have hvisits :
      projectedRoute.visits = (routes d).visits := by
    change
      (liftedVisits depot required routes hcounts d).map
        (project depot required) =
      (routes d).visits
    exact liftedVisits_map_project
      depot required routes hcounts d

  have hfee :=
    projected_copy_route_service
      depot required y x hExact hloop
      (copyRoutes d) (hsupport d) service

  change
    ResourceCuts.routeServiceIn
      projectedRoute Finset.univ service =
    ResourceCuts.routeServiceIn
      (copyRoutes d) Finset.univ
      (copyService depot required service) at hfee

  calc
    ResourceCuts.routeServiceIn
        (liftedLegalRoute depot required routes hcounts d)
        Finset.univ (copyService depot required service) =
      ResourceCuts.routeServiceIn
        projectedRoute Finset.univ service :=
      hfee.symm

    _ = ResourceCuts.routeServiceIn
        (routes d) Finset.univ service := by
      unfold ResourceCuts.routeServiceIn
      rw [hvisits]

/-- Every physical route budget is preserved by the
constructed occurrence-copy route. -/
theorem liftedLegalRoute_budget
    [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (service : V → ℚ)
    (T : ℚ)
    (hbudget : ∀ d,
      ResourceCuts.routeServiceIn
        (routes d) Finset.univ service ≤ T) :
    ∀ d,
      ResourceCuts.routeServiceIn
        (liftedLegalRoute depot required routes hcounts d)
        Finset.univ (copyService depot required service) ≤ T := by
  intro d
  rw [liftedLegalRoute_service
    depot required routes hcounts service d]
  exact hbudget d

/-- Nonnegative physical service fees and feasible route
budgets imply all rounded service cuts for the constructed
copy flow, including the empty-set cut. -/
theorem liftedFlow_rounded_service_cuts
    [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (service : V → ℚ)
    (T : ℚ)
    (hservice : ∀ v, 0 ≤ service v)
    (hT : 0 < T)
    (hbudget : ∀ d,
      ResourceCuts.routeServiceIn
        (routes d) Finset.univ service ≤ T) :
    ∀ S : Finset (VisitCopy depot required),
      none ∉ S →
      Int.ceil
        ((∑ c ∈ S, copyService depot required service c) / T) ≤
          (outCutFlow S
            (liftedFlow depot required routes hcounts) : ℤ) := by
  classical
  exact
    SingleVisitDecomposition.rounded_service_cuts_of_exact_family
      (liftedFlow depot required routes hcounts)
      (none : VisitCopy depot required)
      (liftedLegalRoute depot required routes hcounts)
      (copyService depot required service)
      T
      (copyService_nonneg depot required service hservice)
      hT
      (liftedLegalRoute_totalVisitCount_eq_one
        depot required routes hcounts)
      (by
        intro a b
        rfl)
      (liftedLegalRoute_budget
        depot required routes hcounts service T hbudget)


/-- A service-feasible occurrence-copy lift of a fixed
physical flow.

Copy self-loops and edges between copies of the same
physical node need not be forbidden separately: when the
physical flow is loop-free, exact projection forces them
to have zero flow. -/
structure IsServiceCopyLift
    [Fintype V] [DecidableEq V]
    (depot : V)
    (required : V → ℕ)
    (x : V → V → ℕ)
    (service : V → ℚ)
    (T : ℚ)
    (y : VisitCopy depot required →
      VisitCopy depot required → ℕ) : Prop where

  project_exact :
    ∀ u v,
      projectFlow (project depot required) y u v = x u v

  out_one :
    ∀ c : VisitCopy depot required, c ≠ none →
      outFlow Finset.univ y c = 1

  in_one :
    ∀ c : VisitCopy depot required, c ≠ none →
      inFlow Finset.univ y c = 1

  positive_cuts :
    ∀ S : Finset (VisitCopy depot required),
      S.Nonempty → none ∉ S →
        1 ≤ outCutFlow S y

  rounded_cuts :
    ∀ S : Finset (VisitCopy depot required),
      S.Nonempty → none ∉ S →
      Int.ceil
        ((∑ c ∈ S, copyService depot required service c) / T) ≤
          (outCutFlow S y : ℤ)

/-- A budget-feasible exact physical route decomposition
constructs an occurrence-copy lift satisfying every required
structural and rounded service-capacity condition. -/
theorem exists_serviceCopyLift_of_exact_family
    [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (depot : V)
    (required : V → ℕ)
    (x : V → V → ℕ)
    (routes : ι → LegalRoute depot)
    (hcounts : ∀ v, v ≠ depot →
      totalVisitCount Finset.univ routes v = required v)
    (hrouteExact : ∀ u v,
      totalRouteFlow Finset.univ routes u v = x u v)
    (service : V → ℚ)
    (T : ℚ)
    (hservice : ∀ v, 0 ≤ service v)
    (hT : 0 < T)
    (hbudget : ∀ d,
      ResourceCuts.routeServiceIn
        (routes d) Finset.univ service ≤ T) :
    ∃ y : VisitCopy depot required →
        VisitCopy depot required → ℕ,
      IsServiceCopyLift depot required x service T y := by
  classical

  refine ⟨liftedFlow depot required routes hcounts, ?_⟩

  refine {
    project_exact := ?_
    out_one := ?_
    in_one := ?_
    positive_cuts := ?_
    rounded_cuts := ?_
  }

  · exact liftedFlow_projects_exact
      depot required routes hcounts x hrouteExact

  · intro c hc
    exact
      (liftedFlow_unit_degrees
        depot required routes hcounts c hc).1

  · intro c hc
    exact
      (liftedFlow_unit_degrees
        depot required routes hcounts c hc).2

  · exact liftedFlow_positive_cuts
      depot required routes hcounts

  · intro S hnonempty hdepot
    exact liftedFlow_rounded_service_cuts
      depot required routes hcounts
      service T hservice hT hbudget
      S hdepot

/-- Renaming route identifiers by an equivalence preserves
every aggregate visit count. -/
theorem totalVisitCount_reindex
    [DecidableEq V]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (depot : V)
    (routes : ι → LegalRoute depot)
    (e : κ ≃ ι)
    (v : V) :
    totalVisitCount Finset.univ
      (fun d => routes (e d)) v =
    totalVisitCount Finset.univ routes v := by
  unfold totalVisitCount
  exact e.sum_comp (fun d => (routes d).visits.count v)

/-- Renaming route identifiers by an equivalence preserves
every aggregate edge multiplicity. -/
theorem totalRouteFlow_reindex
    [DecidableEq V]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (depot : V)
    (routes : ι → LegalRoute depot)
    (e : κ ≃ ι)
    (u v : V) :
    totalRouteFlow Finset.univ
      (fun d => routes (e d)) u v =
    totalRouteFlow Finset.univ routes u v := by
  unfold totalRouteFlow
  exact e.sum_comp
    (fun d => routeFlow (routes d).vertices u v)

/-- For a loop-free physical flow, nonnegative service fees
and a positive budget, existence of a service-feasible copy
lift is equivalent to a budget-feasible exact physical route
decomposition with the prescribed visit counts.

The route count is fixed to the physical depot outflow.
Only service costs are included. -/
theorem serviceCopyLift_iff_exact_decomposition
    [Fintype V] [DecidableEq V]
    (depot : V)
    (required : V → ℕ)
    (x : V → V → ℕ)
    (hloop : ∀ v, x v v = 0)
    (service : V → ℚ)
    (T : ℚ)
    (hservice : ∀ v, 0 ≤ service v)
    (hT : 0 < T) :
    (∃ y : VisitCopy depot required →
        VisitCopy depot required → ℕ,
      IsServiceCopyLift depot required x service T y) ↔
    (∃ routes :
        Fin (outFlow Finset.univ x depot) → LegalRoute depot,
      (∀ v, v ≠ depot →
        totalVisitCount Finset.univ routes v = required v) ∧
      (∀ u v,
        totalRouteFlow Finset.univ routes u v = x u v) ∧
      (∀ d,
        ResourceCuts.routeServiceIn
          (routes d) Finset.univ service ≤ T)) := by
  classical
  constructor

  · rintro ⟨y, hlift⟩

    obtain ⟨routes, hcounts, hExact, hcard, hbudget⟩ :=
      exists_exact_decomposition_of_copy_lift
        depot required x y
        hlift.project_exact
        hloop
        hlift.out_one
        hlift.in_one
        hlift.positive_cuts
        service T hT
        hlift.rounded_cuts

    let e :
        Fin (outFlow Finset.univ x depot) ≃
          {c : VisitCopy depot required // 0 < y none c} :=
      (Fintype.equivFinOfCardEq hcard).symm

    refine ⟨fun d => routes (e d), ?_, ?_, ?_⟩

    · intro v hv
      exact
        (totalVisitCount_reindex depot routes e v).trans
          (hcounts v hv)

    · intro u v
      exact
        (totalRouteFlow_reindex depot routes e u v).trans
          (hExact u v)

    · intro d
      exact hbudget (e d)

  · rintro ⟨routes, hcounts, hExact, hbudget⟩
    exact exists_serviceCopyLift_of_exact_family
      depot required x routes
      hcounts hExact
      service T hservice hT hbudget



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
#print axioms UAVProof.VisitCopyLift.count_map_eq_fiber_sum
#print axioms UAVProof.VisitCopyLift.totalVisitCount_mapLegalRoute
#print axioms UAVProof.VisitCopyLift.mapped_count_eq_fiber_card
#print axioms UAVProof.VisitCopyLift.taskFiberEquivFin
#print axioms UAVProof.VisitCopyLift.taskFiber_card
#print axioms UAVProof.VisitCopyLift.projected_copy_routes_cover

#print axioms UAVProof.VisitCopyLift.routeFlow_map
#print axioms UAVProof.VisitCopyLift.projectFlow_sum
#print axioms UAVProof.VisitCopyLift.totalRouteFlow_mapLegalRoute
#print axioms UAVProof.VisitCopyLift.projected_copy_routes_exact
#print axioms UAVProof.VisitCopyLift.routeServiceIn_mapLegalRoute
#print axioms UAVProof.VisitCopyLift.projected_copy_route_service
#print axioms UAVProof.VisitCopyLift.projected_copy_route_budget
#print axioms UAVProof.VisitCopyLift.isChain_of_zip_edges
#print axioms UAVProof.VisitCopyLift.exact_family_supported
#print axioms UAVProof.VisitCopyLift.exists_exact_decomposition_of_copy_lift
#print axioms UAVProof.VisitCopyLift.positionVertex_ne_depot
#print axioms UAVProof.VisitCopyLift.card_get_fiber_eq_count
#print axioms UAVProof.VisitCopyLift.visitPosition_fiber_card
#print axioms UAVProof.VisitCopyLift.visitPosition_fiber_card_eq_required
#print axioms UAVProof.VisitCopyLift.visitPositionFiberEquivFin
#print axioms UAVProof.VisitCopyLift.visitPositionTaskFiberEquiv
#print axioms UAVProof.VisitCopyLift.visitPositionCopiesEquiv
#print axioms UAVProof.VisitCopyLift.positionCopy_project
#print axioms UAVProof.VisitCopyLift.positionCopy_ne_none
#print axioms UAVProof.VisitCopyLift.positionCopy_injective
#print axioms UAVProof.VisitCopyLift.liftedVisits_map_project
#print axioms UAVProof.VisitCopyLift.liftedVisits_vertices_map
#print axioms UAVProof.VisitCopyLift.liftedLegalRoute
#print axioms UAVProof.VisitCopyLift.liftedLegalRoute_visits
#print axioms UAVProof.VisitCopyLift.liftedLegalRoute_vertices_map
#print axioms UAVProof.VisitCopyLift.count_ofFn_eq_fiber_card
#print axioms UAVProof.VisitCopyLift.positionCopy_fiber_card_eq_one
#print axioms UAVProof.VisitCopyLift.liftedLegalRoute_totalVisitCount_eq_one
#print axioms UAVProof.VisitCopyLift.liftedFlow_unit_degrees
#print axioms UAVProof.VisitCopyLift.liftedFlow_no_self_loops
#print axioms UAVProof.VisitCopyLift.liftedFlow_project
#print axioms UAVProof.VisitCopyLift.liftedFlow_projects_exact
#print axioms UAVProof.VisitCopyLift.liftedFlow_positive_cuts
#print axioms UAVProof.VisitCopyLift.liftedLegalRoute_service
#print axioms UAVProof.VisitCopyLift.liftedLegalRoute_budget
#print axioms UAVProof.VisitCopyLift.liftedFlow_rounded_service_cuts
#print axioms UAVProof.VisitCopyLift.exists_serviceCopyLift_of_exact_family
#print axioms UAVProof.VisitCopyLift.totalVisitCount_reindex
#print axioms UAVProof.VisitCopyLift.totalRouteFlow_reindex
#print axioms UAVProof.VisitCopyLift.serviceCopyLift_iff_exact_decomposition
