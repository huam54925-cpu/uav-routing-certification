import LeanCompletion.UAV.CopyFiberCompression

/-!
# Service cost factors through the selected-copy count profile

Proof candidate; local Lean compilation is pending.
This module proves only the algebraic service identity and its consequences.
It does not define or compute the minimum cut for a profile.

Nonnegative service and positive budget are NOT needed for these identities.
The depot-free assumption matters: copyService assigns zero to the depot copy,
even when the physical service function has a nonzero value at the depot.
-/

namespace UAVProof.CopyProfileService

open VisitCopyLift CopyFiberCompression

section FiniteGrouping

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]


omit [Fintype W] [DecidableEq W] in
/-- Group a finite weighted sum by projection fibres.
The projection need not be injective or surjective. -/
theorem weighted_sum_eq_fibre_counts
    (π : W → V) (S : Finset W) (weight : V → ℚ) :
    (∑ c ∈ S, weight (π c)) =
      ∑ v : V, weight v * (fibreCount π S v : ℚ) := by
  classical
  calc
    (∑ c ∈ S, weight (π c)) =
        ∑ c ∈ S, ∑ v : V, if π c = v then weight v else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      simp
    _ = ∑ v : V, ∑ c ∈ S, if π c = v then weight v else 0 :=
      Finset.sum_comm
    _ = ∑ v : V, weight v * (fibreCount π S v : ℚ) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.sum_filter]
      simp [fibreCount, nsmul_eq_mul, mul_comm]

end FiniteGrouping

section VisitProfiles

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of selected occurrences of each physical vertex. -/
def visitProfile (depot : V) (required : V → ℕ)
    (S : Finset (VisitCopy depot required)) : V → ℕ :=
  fibreCount (project depot required) S

/-- Algebraic work associated with a physical count vector. -/
def profileWork (service : V → ℚ) (q : V → ℕ) : ℚ :=
  ∑ v : V, service v * (q v : ℚ)

omit [Fintype V] in
theorem visitProfile_depot_eq_zero
    (depot : V) (required : V → ℕ)
    (S : Finset (VisitCopy depot required)) (hdepot : none ∉ S) :
    visitProfile depot required S depot = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  ext c
  constructor
  · intro hc
    obtain ⟨hcS, hproj⟩ := Finset.mem_filter.mp hc
    have hcNone : c = none :=
      (project_eq_depot_iff depot required c).mp hproj
    subst c
    exact (hdepot hcS).elim
  · simp

/-- Main identity: a depot-free copy subset has exactly its profile's work. -/
theorem copy_service_eq_profileWork
    (depot : V) (required : V → ℕ) (service : V → ℚ)
    (S : Finset (VisitCopy depot required)) (hdepot : none ∉ S) :
    (∑ c ∈ S, copyService depot required service c) =
      profileWork service (visitProfile depot required S) := by
  classical
  calc
    (∑ c ∈ S, copyService depot required service c) =
        ∑ c ∈ S, service (project depot required c) := by
      apply Finset.sum_congr rfl
      intro c hc
      cases c with
      | none => exact (hdepot hc).elim
      | some c => rfl
    _ = profileWork service (visitProfile depot required S) :=
      weighted_sum_eq_fibre_counts (project depot required) S service

/-- Equal profiles imply equal service costs, regardless of the chosen copies. -/
theorem copy_service_eq_of_same_profile
    (depot : V) (required : V → ℕ) (service : V → ℚ)
    (S R : Finset (VisitCopy depot required))
    (hS : none ∉ S) (hR : none ∉ R)
    (hprofile : visitProfile depot required S = visitProfile depot required R) :
    (∑ c ∈ S, copyService depot required service c) =
      ∑ c ∈ R, copyService depot required service c := by
  rw [copy_service_eq_profileWork depot required service S hS,
    copy_service_eq_profileWork depot required service R hR, hprofile]

/-- The rounded required number of routes also factors through the profile.
No claim is made here about the cut flow on the other side of the inequality. -/
theorem rounded_requirement_eq_profile
    (depot : V) (required : V → ℕ) (service : V → ℚ) (T : ℚ)
    (S : Finset (VisitCopy depot required)) (hS : none ∉ S) :
    Int.ceil ((∑ c ∈ S, copyService depot required service c) / T) =
      Int.ceil (profileWork service (visitProfile depot required S) / T) := by
  rw [copy_service_eq_profileWork depot required service S hS]

end VisitProfiles

namespace FourNode

open FixedFlowObstruction CopyLiftObstruction.FourNode
open CopyFiberCompression.FourNode

/-- Apply the general identity to the two previously checked subsets. -/
theorem example_same_service_from_profile :
    (∑ c ∈ badSet, copyService (0 : Node) required service c) =
      ∑ c ∈ alternativeSet, copyService (0 : Node) required service c := by
  apply copy_service_eq_of_same_profile
    (0 : Node) required service badSet alternativeSet
    depot_not_mem_badSet alternative_depot_free
  exact same_copy_profile

end FourNode
end UAVProof.CopyProfileService

#print axioms UAVProof.CopyProfileService.weighted_sum_eq_fibre_counts
#print axioms UAVProof.CopyProfileService.visitProfile_depot_eq_zero
#print axioms UAVProof.CopyProfileService.copy_service_eq_profileWork
#print axioms UAVProof.CopyProfileService.copy_service_eq_of_same_profile
#print axioms UAVProof.CopyProfileService.rounded_requirement_eq_profile
#print axioms UAVProof.CopyProfileService.FourNode.example_same_service_from_profile
