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
