import LeanCompletion.UAV.Connectivity
import Mathlib.Tactic

namespace UAVProof.ResourceCuts

variable {V ι : Type*}
variable [DecidableEq V] [Fintype V]
variable {depot : V}

/-- Whether a route services at least one vertex of S. -/
def Serves (r : LegalRoute depot) (S : Finset V) : Prop :=
  ∃ v ∈ r.visits, v ∈ S

/-- Number of selected routes that service S.
Repeated visits by the same route count only once here. -/
noncomputable def servingCount
    (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (S : Finset V) : ℕ := by
  classical
  exact (ks.filter (fun k => Serves (routes k) S)).card

/-- The aggregate cut flow is the sum of individual cut flows. -/
theorem cutFlow_sum
    (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (S : Finset V) :
    outCutFlow S (totalRouteFlow ks routes) =
      ∑ k ∈ ks, outCutFlow S (routeFlow (routes k).vertices) := by
  unfold outCutFlow totalRouteFlow
  calc
    (∑ i ∈ S,
      ∑ j ∈ Finset.univ.filter (fun j => j ∉ S),
        ∑ k ∈ ks, routeFlow (routes k).vertices i j)
        =
      ∑ i ∈ S, ∑ k ∈ ks,
        ∑ j ∈ Finset.univ.filter (fun j => j ∉ S),
          routeFlow (routes k).vertices i j := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_comm
    _ = ∑ k ∈ ks, ∑ i ∈ S,
          ∑ j ∈ Finset.univ.filter (fun j => j ∉ S),
            routeFlow (routes k).vertices i j := by
              exact Finset.sum_comm

/-- Every route servicing a depot-free set contributes at least
one exit. Multiple exits can only increase the aggregate cut flow. -/
theorem servingCount_le_cutFlow
    (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (S : Finset V)
    (hdepot : depot ∉ S) :
    servingCount ks routes S ≤
      outCutFlow S (totalRouteFlow ks routes) := by
  classical
  have hroute :
      ∀ k ∈ ks,
        (if Serves (routes k) S then 1 else 0) ≤
          outCutFlow S (routeFlow (routes k).vertices) := by
    intro k _
    by_cases h : Serves (routes k) S
    · simpa [h] using
        (routes k).outCutFlow_ge_one S hdepot h
    · simp [h]

  have hsum := Finset.sum_le_sum hroute
  have hcount :
      (∑ k ∈ ks, if Serves (routes k) S then 1 else 0) =
        servingCount ks routes S := by
    simp [servingCount]

  rw [hcount] at hsum
  rw [cutFlow_sum]
  exact hsum

/-- Abstract resource accounting.

work k is the service resource spent inside S.
overhead k is the rest of the resource consumption.
A route not servicing S contributes zero work to S.
Each servicing route has overhead at least tau.
-/
theorem service_le_serving_capacity
    (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (S : Finset V)
    (work overhead : ι → ℚ)
    (W T tau : ℚ)
    (hcover : (∑ k ∈ ks, work k) = W)
    (hzero : ∀ k ∈ ks,
      ¬ Serves (routes k) S → work k = 0)
    (hbudget : ∀ k ∈ ks,
      work k + overhead k ≤ T)
    (hoverhead : ∀ k ∈ ks,
      Serves (routes k) S → tau ≤ overhead k) :
    W ≤ (servingCount ks routes S : ℚ) * (T - tau) := by
  classical
  have hwork :
      ∀ k ∈ ks,
        work k ≤
          if Serves (routes k) S then T - tau else 0 := by
    intro k hk
    by_cases h : Serves (routes k) S
    · have hb := hbudget k hk
      have ho := hoverhead k hk h
      simp only [if_pos h]
      linarith
    · rw [if_neg h, hzero k hk h]

  have hsum := Finset.sum_le_sum hwork
  have hcapacity :
      (∑ k ∈ ks,
        if Serves (routes k) S then T - tau else 0) =
      (servingCount ks routes S : ℚ) * (T - tau) := by
    rw [← Finset.sum_filter]
    simp [servingCount, nsmul_eq_mul]
    <;> ring


  rw [hcover, hcapacity] at hsum
  exact hsum

/-- Resource capacity expressed as an aggregate cut inequality. -/
theorem service_le_cut_capacity
    (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (S : Finset V)
    (hdepot : depot ∉ S)
    (work overhead : ι → ℚ)
    (W T tau : ℚ)
    (hremaining : 0 ≤ T - tau)
    (hcover : (∑ k ∈ ks, work k) = W)
    (hzero : ∀ k ∈ ks,
      ¬ Serves (routes k) S → work k = 0)
    (hbudget : ∀ k ∈ ks,
      work k + overhead k ≤ T)
    (hoverhead : ∀ k ∈ ks,
      Serves (routes k) S → tau ≤ overhead k) :
    W ≤
      (outCutFlow S (totalRouteFlow ks routes) : ℚ) *
        (T - tau) := by
  have hservice :=
    service_le_serving_capacity
      ks routes S work overhead W T tau
      hcover hzero hbudget hoverhead

  have hcount :
      (servingCount ks routes S : ℚ) ≤
        (outCutFlow S (totalRouteFlow ks routes) : ℚ) := by
    exact_mod_cast servingCount_le_cutFlow ks routes S hdepot

  exact hservice.trans
    (mul_le_mul_of_nonneg_right hcount hremaining)

#print axioms servingCount_le_cutFlow
#print axioms service_le_serving_capacity
#print axioms service_le_cut_capacity


/-- Service consumed inside S by one route.
Every occurrence in the visit list is charged. -/
def routeServiceIn
    (r : LegalRoute depot)
    (S : Finset V)
    (service : V → ℚ) : ℚ :=
  ∑ i ∈ S, service i * (r.visits.count i : ℚ)

/-- Service required inside S. -/
def requiredServiceIn
    (S : Finset V)
    (service : V → ℚ)
    (required : V → ℕ) : ℚ :=
  ∑ i ∈ S, service i * (required i : ℚ)

omit [DecidableEq V] [Fintype V] in
/-- A route not servicing S contributes zero service to S. -/

theorem routeServiceIn_zero_of_not_serves
    [DecidableEq V]
    (r : LegalRoute depot)
    (S : Finset V)
    (service : V → ℚ)
    (hnot : ¬ Serves r S) :
    routeServiceIn r S service = 0 := by
  unfold routeServiceIn
  apply Finset.sum_eq_zero
  intro i hi
  have hmissing : i ∉ r.visits := by
    intro hv
    apply hnot
    exact ⟨i, hv, hi⟩
  rw [List.count_eq_zero.mpr hmissing]
  simp


omit [Fintype V] in
/-- Nonnegative service fees give nonnegative route service. -/

theorem routeServiceIn_nonneg
    (r : LegalRoute depot)
    (S : Finset V)
    (service : V → ℚ)
    (hservice : ∀ i ∈ S, 0 ≤ service i) :
    0 ≤ routeServiceIn r S service := by
  unfold routeServiceIn
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hservice i hi) (Nat.cast_nonneg _)

omit [Fintype V] in
/-- Exact visit coverage implies exact service accounting.
Repeated visits are counted with their full multiplicity. -/

theorem sum_routeServiceIn_eq_required
    (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (S : Finset V)
    (service : V → ℚ)
    (required : V → ℕ)
    (hdepot : depot ∉ S)
    (hvisits : ∀ i, i ≠ depot →
      totalVisitCount ks routes i = required i) :
    (∑ k ∈ ks, routeServiceIn (routes k) S service) =
      requiredServiceIn S service required := by
  classical
  unfold routeServiceIn requiredServiceIn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi

  have hidepot : i ≠ depot := by
    intro heq
    subst i
    exact hdepot hi

  calc
    (∑ k ∈ ks,
      service i * ((routes k).visits.count i : ℚ))
        =
      service i * (totalVisitCount ks routes i : ℚ) := by
        simp [totalVisitCount, Finset.mul_sum]
    _ = service i * (required i : ℚ) := by
        rw [hvisits i hidepot]

/-- The resource cut with service accounting derived from
actual visit lists and exact coverage. -/
theorem requiredService_le_cut_capacity
    (ks : Finset ι)
    (routes : ι → LegalRoute depot)
    (S : Finset V)
    (service : V → ℚ)
    (required : V → ℕ)
    (overhead : ι → ℚ)
    (T tau : ℚ)
    (hdepot : depot ∉ S)
    (hvisits : ∀ i, i ≠ depot →
      totalVisitCount ks routes i = required i)
    (hremaining : 0 ≤ T - tau)
    (hbudget : ∀ k ∈ ks,
      routeServiceIn (routes k) S service + overhead k ≤ T)
    (hoverhead : ∀ k ∈ ks,
      Serves (routes k) S → tau ≤ overhead k) :
    requiredServiceIn S service required ≤
      (outCutFlow S (totalRouteFlow ks routes) : ℚ) *
        (T - tau) := by
  apply service_le_cut_capacity
    ks routes S hdepot
    (fun k => routeServiceIn (routes k) S service)
    overhead
    (requiredServiceIn S service required)
    T tau hremaining

  · exact sum_routeServiceIn_eq_required
      ks routes S service required hdepot hvisits

  · intro k _ hnot
    exact routeServiceIn_zero_of_not_serves
      (routes k) S service hnot

  · exact hbudget

  · exact hoverhead

#print axioms routeServiceIn_zero_of_not_serves
#print axioms sum_routeServiceIn_eq_required
#print axioms requiredService_le_cut_capacity












end UAVProof.ResourceCuts
