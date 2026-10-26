import LeanCompletion.UAV.CopyProfileMinimum

/-!
# Exact regrouping of copy service-capacity cuts by count profile

Proof candidate; local Lean compilation is pending.

The same copy flow y occurs on both sides. No claim is made that kappa is
efficient to compute or that a profile alone determines an individual cut.
This is an algebraic equivalence of inequalities: nonnegative service and
positive budget remain assumptions of the routing application, not of this
regrouping identity itself.
-/

namespace UAVProof.CopyProfileCuts

open VisitCopyLift CopyProfileService CopyProfileMinimum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All depot-free copy cuts, including the harmless empty subset. -/
def AllCopyCuts
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) : Prop :=
  ∀ S : Finset (VisitCopy depot required), none ∉ S →
    Int.ceil ((∑ c ∈ S, copyService depot required service c) / T) ≤
      (outCutFlow S y : ℤ)

/-- One worst-cut inequality for each realizable count profile. -/
def AllProfileCuts
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) : Prop :=
  ∀ (q : V → ℕ) (hq : RealizableProfile depot required q),
    Int.ceil (profileWork service q / T) ≤ (kappa depot required y q hq : ℤ)

/-- Forward direction: apply the copy cut to an attaining subset. -/
theorem profile_cuts_of_copy_cuts
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ)
    (hcuts : AllCopyCuts depot required y service T) :
    AllProfileCuts depot required y service T := by
  intro q hq
  obtain ⟨S, hS, hprofile, hmin⟩ := kappa_attained depot required y q hq
  have hcut := hcuts S hS
  rw [rounded_requirement_eq_profile depot required service T S hS,
    hprofile, hmin] at hcut
  exact hcut

/-- Reverse direction: every subset's cut dominates its profile minimum. -/
theorem copy_cuts_of_profile_cuts
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ)
    (hcuts : AllProfileCuts depot required y service T) :
    AllCopyCuts depot required y service T := by
  intro S hS
  have hq : RealizableProfile depot required (visitProfile depot required S) :=
    ⟨S, hS, rfl⟩
  have hle := kappa_le_cut depot required y
    (visitProfile depot required S) hq S hS rfl
  have hleZ :
      (kappa depot required y (visitProfile depot required S) hq : ℤ) ≤
        (outCutFlow S y : ℤ) := by
    exact_mod_cast hle
  rw [rounded_requirement_eq_profile depot required service T S hS]
  exact (hcuts (visitProfile depot required S) hq).trans hleZ

/-- Main equivalence: regrouping preserves all the capacity inequalities. -/
theorem copy_cuts_iff_profile_cuts
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) :
    AllCopyCuts depot required y service T ↔
      AllProfileCuts depot required y service T := by
  exact ⟨profile_cuts_of_copy_cuts depot required y service T,
    copy_cuts_of_profile_cuts depot required y service T⟩

/-- Match the original lift definition, which quantifies over nonempty subsets.
The empty-subset inequality is 0 <= 0 and requires no budget assumption. -/
theorem nonempty_copy_cuts_iff_all_copy_cuts
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) :
    (∀ S : Finset (VisitCopy depot required), S.Nonempty → none ∉ S →
      Int.ceil ((∑ c ∈ S, copyService depot required service c) / T) ≤
        (outCutFlow S y : ℤ)) ↔
    AllCopyCuts depot required y service T := by
  classical
  constructor
  · intro h S hS
    by_cases hempty : S = ∅
    · subst S
      simp [outCutFlow]
    · exact h S (Finset.nonempty_iff_ne_empty.mpr hempty) hS
  · intro h S _hNonempty hS
    exact h S hS

/-- Direct interface to the rounded_cuts field of IsServiceCopyLift. -/
theorem nonempty_copy_cuts_iff_profile_cuts
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (service : V → ℚ) (T : ℚ) :
    (∀ S : Finset (VisitCopy depot required), S.Nonempty → none ∉ S →
      Int.ceil ((∑ c ∈ S, copyService depot required service c) / T) ≤
        (outCutFlow S y : ℤ)) ↔
    AllProfileCuts depot required y service T := by
  exact (nonempty_copy_cuts_iff_all_copy_cuts depot required y service T).trans
    (copy_cuts_iff_profile_cuts depot required y service T)

end UAVProof.CopyProfileCuts

#print axioms UAVProof.CopyProfileCuts.profile_cuts_of_copy_cuts
#print axioms UAVProof.CopyProfileCuts.copy_cuts_of_profile_cuts
#print axioms UAVProof.CopyProfileCuts.copy_cuts_iff_profile_cuts
#print axioms UAVProof.CopyProfileCuts.nonempty_copy_cuts_iff_all_copy_cuts
#print axioms UAVProof.CopyProfileCuts.nonempty_copy_cuts_iff_profile_cuts
