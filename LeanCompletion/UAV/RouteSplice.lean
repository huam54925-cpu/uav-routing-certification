import LeanCompletion.UAV.TotalFlow

/-! Inserting an out-and-back excursion in a legal route. The inserted
vertex need not be new: nonadjacent repeated visits are allowed. -/

namespace UAVProof.RouteSplice

variable {V : Type*}

theorem chain_insert (L R : List V) (p v : V)
    (h : (L ++ p :: R).IsChain (· ≠ ·)) (hvp : v ≠ p) :
    (L ++ p :: v :: p :: R).IsChain (· ≠ ·) := by
  induction L with
  | nil => simpa [List.isChain_cons_cons, hvp, Ne.symm hvp] using h
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.isChain_cons_cons] at h ⊢
      exact ⟨h.1, Ne.symm hvp, hvp, h.2⟩
    | cons b L =>
      simp only [List.cons_append, List.isChain_cons_cons] at h ⊢
      exact ⟨h.1, ih h.2⟩

def insertExcursion {depot : V} (r : LegalRoute depot)
    (L R : List V) (p v : V) (hvis : r.visits = L ++ p :: R)
    (hv : v ≠ depot) (hvp : v ≠ p) : LegalRoute depot where
  visits := L ++ p :: v :: p :: R
  visits_nonempty := by simp
  depot_not_mem := by
    have h := r.depot_not_mem
    rw [hvis] at h
    simpa [List.mem_append, hv, Ne.symm hv] using h
  adjacent_ne := by
    have h := r.adjacent_ne
    rw [hvis] at h
    have h' : ((depot :: L) ++ p :: (R ++ [depot])).IsChain (· ≠ ·) := by
      simpa [depotRoute, List.append_assoc] using h
    simpa [depotRoute, List.append_assoc] using
      chain_insert (depot :: L) (R ++ [depot]) p v h' hvp

variable [DecidableEq V]

theorem flow_cons_cons (a b : V) (l : List V) (i j : V) :
    routeFlow (a :: b :: l) i j = routeFlow (b :: l) i j +
      (if a = i ∧ b = j then 1 else 0) := by
  simp [routeFlow, List.count_cons, beq_iff_eq]

theorem flow_insert (L R : List V) (p v i j : V) :
    routeFlow (L ++ p :: v :: p :: R) i j =
      routeFlow (L ++ p :: R) i j +
        (if p = i ∧ v = j then 1 else 0) +
        (if v = i ∧ p = j then 1 else 0) := by
  induction L with
  | nil => simp only [List.nil_append, flow_cons_cons]; omega
  | cons a L ih =>
    cases L with
    | nil => simp only [List.cons_append, List.nil_append, flow_cons_cons] at ih ⊢; omega
    | cons b L => simp only [List.cons_append, flow_cons_cons] at ih ⊢; omega

theorem insertExcursion_flow {depot : V} (r : LegalRoute depot)
    (L R : List V) (p v : V) (hvis : r.visits = L ++ p :: R)
    (hv : v ≠ depot) (hvp : v ≠ p) (i j : V) :
    routeFlow (insertExcursion r L R p v hvis hv hvp).vertices i j =
      routeFlow r.vertices i j +
        (if p = i ∧ v = j then 1 else 0) +
        (if v = i ∧ p = j then 1 else 0) := by
  simpa [insertExcursion, LegalRoute.vertices, depotRoute, hvis, List.append_assoc] using
    flow_insert (depot :: L) (R ++ [depot]) p v i j

theorem exists_insertExcursion {depot : V} (r : LegalRoute depot)
    (p v : V) (hp : p ∈ r.visits) (hv : v ≠ depot) (hvp : v ≠ p) :
    ∃ r' : LegalRoute depot,
      (∀ u, u ∈ r.visits → u ∈ r'.visits) ∧ v ∈ r'.visits ∧
      ∀ i j, routeFlow r'.vertices i j = routeFlow r.vertices i j +
        (if p = i ∧ v = j then 1 else 0) +
        (if v = i ∧ p = j then 1 else 0) := by
  obtain ⟨L, R, h⟩ := List.mem_iff_append.mp hp
  refine ⟨insertExcursion r L R p v h hv hvp, ?_, ?_, ?_⟩
  · intro u hu
    simpa [insertExcursion, h, List.mem_append, or_assoc, or_left_comm, or_comm] using
      (Or.inl hu : u ∈ r.visits ∨ u = v)
  · simp [insertExcursion]
  · exact insertExcursion_flow r L R p v h hv hvp

theorem exists_insertExcursions {depot : V} (r : LegalRoute depot)
    (p v : V) (hp : p ∈ r.visits) (hv : v ≠ depot) (hvp : v ≠ p) (n : ℕ) :
    ∃ r' : LegalRoute depot,
      (∀ u, u ∈ r.visits → u ∈ r'.visits) ∧ (0 < n → v ∈ r'.visits) ∧
      ∀ i j, routeFlow r'.vertices i j = routeFlow r.vertices i j +
        n * (if p = i ∧ v = j then 1 else 0) +
        n * (if v = i ∧ p = j then 1 else 0) := by
  induction n with
  | zero => exact ⟨r, fun _ h => h, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨s, hkeep, _, hflow⟩ := ih
    obtain ⟨t, hkeep', hvisit, ht⟩ := exists_insertExcursion s p v (hkeep p hp) hv hvp
    refine ⟨t, fun u hu => hkeep' u (hkeep u hu), fun _ => hvisit, ?_⟩
    intro i j
    rw [ht, hflow]
    simp only [Nat.add_mul, one_mul]
    omega

theorem exists_family_insertExcursion {I : Type*} [Fintype I] [DecidableEq I]
    {depot : V} (rs : I → LegalRoute depot) (r : I) (p v : V)
    (hp : p ∈ (rs r).visits) (hv : v ≠ depot) (hvp : v ≠ p) :
    ∃ rs' : I → LegalRoute depot,
      ∀ i j, totalRouteFlow Finset.univ rs' i j = totalRouteFlow Finset.univ rs i j +
        (if p = i ∧ v = j then 1 else 0) +
        (if v = i ∧ p = j then 1 else 0) := by
  obtain ⟨s, _, _, hs⟩ := exists_insertExcursion (rs r) p v hp hv hvp
  let rs' := Function.update rs r s
  refine ⟨rs', ?_⟩
  intro i j
  have hterm (k : I) : routeFlow (rs' k).vertices i j = routeFlow (rs k).vertices i j +
      (if k = r then (if p = i ∧ v = j then 1 else 0) +
        (if v = i ∧ p = j then 1 else 0) else 0) := by
    by_cases hk : k = r
    · subst k
      simpa [rs', add_assoc] using hs i j
    · simp [rs', Function.update_of_ne hk, hk]
  unfold totalRouteFlow
  simp_rw [hterm]
  simp [Finset.sum_add_distrib, add_assoc]

end UAVProof.RouteSplice

#print axioms UAVProof.RouteSplice.insertExcursion_flow
#print axioms UAVProof.RouteSplice.exists_insertExcursions
#print axioms UAVProof.RouteSplice.exists_family_insertExcursion
