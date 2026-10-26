import LeanCompletion.UAV.CopyLiftObstruction

/-!
# First limits of copy-information compression

Proof candidate, pending local Lean compilation.

1. A subset splitting a projection fibre is not a full preimage.
2. For the existing witness, every depot-free full preimage passes its cut.
3. Two copy subsets have identical per-vertex counts but different cut flows
   and opposite capacity-cut outcomes, on the SAME fixed structural lift.

The third result rules out recovering an individual subset's cut outcome
from counts alone. It does NOT rule out taking a minimum cut over all subsets
with a given count profile, or retaining additional connectivity information.
-/

namespace UAVProof.CopyFiberCompression

open ResourceCuts VisitCopyLift

section General

variable {V W : Type*} [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Select every copy of each physical vertex in U. -/
def fullFibreSet (π : W → V) (U : Finset V) : Finset W :=
  Finset.univ.filter (fun c => π c ∈ U)

/-- Membership cannot distinguish two copies of the same physical vertex. -/
theorem fullFibreSet_membership
    (π : W → V) (U : Finset V) (a b : W) (hab : π a = π b) :
    a ∈ fullFibreSet π U ↔ b ∈ fullFibreSet π U := by
  simp only [fullFibreSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hab]

/-- Splitting even one fibre prevents representation by a physical subset. -/
theorem not_fullFibreSet_of_split
    (π : W → V) (S : Finset W) (a b : W)
    (ha : a ∈ S) (hb : b ∉ S) (hab : π a = π b) :
    ¬ ∃ U : Finset V, S = fullFibreSet π U := by
  rintro ⟨U, rfl⟩
  exact hb ((fullFibreSet_membership π U a b hab).mp ha)

/-- A possible compressed description: selected-copy counts at each vertex. -/
def fibreCount (π : W → V) (S : Finset W) (v : V) : ℕ :=
  (S.filter (fun c => π c = v)).card

end General

namespace FourNode

open FixedFlowObstruction CopyLiftObstruction.FourNode

theorem badSet_not_fullFibreSet :
    ¬ ∃ U : Finset Node,
      badSet = fullFibreSet (project (0 : Node) required) U := by
  obtain ⟨ha, hb, hab⟩ := badSet_splits_a_fibre
  exact not_fullFibreSet_of_split
    (project (0 : Node) required) badSet aFirst aOther ha hb hab

/-- Cut predicate on the SAME explicit witnessFlow throughout this module. -/
def CutHolds (S : Finset Copy) : Prop :=
  Int.ceil ((∑ c ∈ S, copyService (0 : Node) required service c) / capacity) ≤
    (outCutFlow S witnessFlow : ℤ)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Finite certificate: all eight depot-free physical selections pass upstairs.
The local limits allow kernel reduction of the nested finite sums. -/
theorem all_full_fibre_cuts_pass :
    ∀ U : Finset Node, (0 : Node) ∉ U →
      CutHolds (fullFibreSet (project (0 : Node) required) U) := by
  unfold CutHolds
  decide +kernel

def copyProfile (S : Finset Copy) : Node → ℕ :=
  fibreCount (project (0 : Node) required) S

/-- Replace aReturn by aOther while retaining two a copies and the b copy. -/
def alternativeSet : Finset Copy := {aFirst, bOnly, aOther}

theorem same_copy_profile : copyProfile badSet = copyProfile alternativeSet := by
  have h : ∀ v : Node, copyProfile badSet v = copyProfile alternativeSet v := by
    decide +kernel
  exact funext h

theorem profile_values :
    copyProfile badSet (0 : Node) = 0 ∧
    copyProfile badSet (1 : Node) = 2 ∧
    copyProfile badSet (2 : Node) = 1 ∧
    copyProfile badSet (3 : Node) = 0 := by
  decide +kernel

theorem alternative_nonempty : alternativeSet.Nonempty := by decide +kernel
theorem alternative_depot_free : (none : Copy) ∉ alternativeSet := by decide +kernel

theorem alternative_service_eq_four :
    (∑ c ∈ alternativeSet, copyService (0 : Node) required service c) = (4 : ℚ) := by
  decide +kernel

theorem alternative_outCut_eq_two : outCutFlow alternativeSet witnessFlow = 2 := by
  decide +kernel

theorem alternative_cut_passes : CutHolds alternativeSet := by
  unfold CutHolds
  decide +kernel

theorem bad_cut_fails : ¬ CutHolds badSet := by
  intro h
  exact (not_le_of_gt badSet_violates_capacity) h

/-- No function of the profile alone recovers each subset's exact cut flow. -/
theorem no_profile_only_cut_value :
    ¬ ∃ f : (Node → ℕ) → ℕ,
      ∀ S : Finset Copy, S.Nonempty → (none : Copy) ∉ S →
        outCutFlow S witnessFlow = f (copyProfile S) := by
  rintro ⟨f, hf⟩
  have hbad := hf badSet badSet_nonempty depot_not_mem_badSet
  have halt := hf alternativeSet alternative_nonempty alternative_depot_free
  rw [badSet_outCut_eq_one] at hbad
  rw [alternative_outCut_eq_two] at halt
  rw [same_copy_profile] at hbad
  omega

/-- Even the individual cut's pass/fail status cannot be a predicate of
the count profile alone, without further information about which copies. -/
theorem no_profile_only_cut_classifier :
    ¬ ∃ P : (Node → ℕ) → Prop,
      ∀ S : Finset Copy, S.Nonempty → (none : Copy) ∉ S →
        (CutHolds S ↔ P (copyProfile S)) := by
  rintro ⟨P, hP⟩
  have halt : P (copyProfile alternativeSet) :=
    (hP alternativeSet alternative_nonempty alternative_depot_free).mp
      alternative_cut_passes
  have hbad : P (copyProfile badSet) := by
    rw [same_copy_profile]
    exact halt
  exact bad_cut_fails
    ((hP badSet badSet_nonempty depot_not_mem_badSet).mpr hbad)

/-- A concrete separation, with both subsets nonempty and depot-free. -/
theorem same_profile_different_cut_outcomes :
    badSet.Nonempty ∧ (none : Copy) ∉ badSet ∧
    alternativeSet.Nonempty ∧ (none : Copy) ∉ alternativeSet ∧
    copyProfile badSet = copyProfile alternativeSet ∧
    outCutFlow badSet witnessFlow = 1 ∧
    outCutFlow alternativeSet witnessFlow = 2 ∧
    (¬ CutHolds badSet) ∧ CutHolds alternativeSet := by
  exact ⟨badSet_nonempty, depot_not_mem_badSet, alternative_nonempty,
    alternative_depot_free, same_copy_profile, badSet_outCut_eq_one,
    alternative_outCut_eq_two, bad_cut_fails, alternative_cut_passes⟩

end FourNode
end UAVProof.CopyFiberCompression

#print axioms UAVProof.CopyFiberCompression.not_fullFibreSet_of_split
#print axioms UAVProof.CopyFiberCompression.FourNode.badSet_not_fullFibreSet
#print axioms UAVProof.CopyFiberCompression.FourNode.all_full_fibre_cuts_pass
#print axioms UAVProof.CopyFiberCompression.FourNode.same_copy_profile
#print axioms UAVProof.CopyFiberCompression.FourNode.profile_values
#print axioms UAVProof.CopyFiberCompression.FourNode.alternative_service_eq_four
#print axioms UAVProof.CopyFiberCompression.FourNode.no_profile_only_cut_value
#print axioms UAVProof.CopyFiberCompression.FourNode.no_profile_only_cut_classifier
#print axioms UAVProof.CopyFiberCompression.FourNode.same_profile_different_cut_outcomes
