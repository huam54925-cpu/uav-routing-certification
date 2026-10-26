import LeanCompletion.UAV.CopyProfileService

/-!
# Minimum outgoing cut for a realizable copy-count profile

Proof candidate; local Lean compilation is pending.

The definition takes a proof that the profile is realizable. No default value
is assigned to an unrealizable profile. Empty subsets are allowed, as in the
stated minimization domain. There are no service-budget assumptions here.

Nat.find selects the least attainable natural-number cut value. This is a
mathematical definition, not a claim of an efficient minimization algorithm.
-/

namespace UAVProof.CopyProfileMinimum

open VisitCopyLift CopyProfileService

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A profile is realizable by a depot-free subset of the canonical copies. -/
def RealizableProfile
    (depot : V) (required : V → ℕ) (q : V → ℕ) : Prop :=
  ∃ S : Finset (VisitCopy depot required),
    none ∉ S ∧ visitProfile depot required S = q

/-- A cut value is attained by some depot-free subset with the given profile. -/
def AttainedCutValue
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) (k : ℕ) : Prop :=
  ∃ S : Finset (VisitCopy depot required),
    none ∉ S ∧ visitProfile depot required S = q ∧ outCutFlow S y = k

/-- Realizability supplies at least one attained cut value. -/
theorem exists_attained_cut_value
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) (hq : RealizableProfile depot required q) :
    ∃ k : ℕ, AttainedCutValue depot required y q k := by
  obtain ⟨S, hS, hprofile⟩ := hq
  exact ⟨outCutFlow S y, S, hS, hprofile, rfl⟩

/-- The least attained cut value, defined only with a realizability witness. -/
noncomputable def kappa
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) (hq : RealizableProfile depot required q) : ℕ := by
  classical
  exact Nat.find (exists_attained_cut_value depot required y q hq)

/-- First target: some eligible subset attains the minimum. -/
theorem kappa_attained
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) (hq : RealizableProfile depot required q) :
    ∃ S : Finset (VisitCopy depot required),
      none ∉ S ∧ visitProfile depot required S = q ∧
      outCutFlow S y = kappa depot required y q hq := by
  classical
  exact Nat.find_spec (exists_attained_cut_value depot required y q hq)

/-- Second target: the minimum is no larger than any eligible subset's cut. -/
theorem kappa_le_cut
    (depot : V) (required : V → ℕ)
    (y : VisitCopy depot required → VisitCopy depot required → ℕ)
    (q : V → ℕ) (hq : RealizableProfile depot required q)
    (S : Finset (VisitCopy depot required))
    (hS : none ∉ S) (hprofile : visitProfile depot required S = q) :
    kappa depot required y q hq ≤ outCutFlow S y := by
  classical
  exact Nat.find_min' (exists_attained_cut_value depot required y q hq)
    (show AttainedCutValue depot required y q (outCutFlow S y) from
      ⟨S, hS, hprofile, rfl⟩)

end UAVProof.CopyProfileMinimum

#print axioms UAVProof.CopyProfileMinimum.exists_attained_cut_value
#print axioms UAVProof.CopyProfileMinimum.kappa_attained
#print axioms UAVProof.CopyProfileMinimum.kappa_le_cut
