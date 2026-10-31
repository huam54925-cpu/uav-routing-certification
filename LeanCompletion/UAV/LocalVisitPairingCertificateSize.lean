import LeanCompletion.UAV.LocalVisitPairingFiniteChecker
import Mathlib.Data.Nat.Size

/-!
# Raw candidate cardinality and fixed-width representation capacity

Let N count non-depot visits with multiplicity, M = N + 1, and B = gridBound.
The actual three-field candidate type has cardinality M^M (N+1)^M (B+1)^M.
This includes invalid candidates and all redundant depot entries; it does not
count valid certificates or route decompositions. No budget-sign assumption is
needed, since the candidate type exists even for negative budgets.

After fixing copy indices, each copy has a successor index, a rank, and a
potential numerator. Widths wN, wN, wB give total capacity 2^L, where
L = (N+1) * (2*wN + wB). We prove cardinality and numerical capacity bounds,
not an implemented binary encoder, parser, or serialization round trip.
No search algorithm, checker runtime bound, or polynomial bound in the original
binary input length is claimed. In particular N is the expanded visit count.
-/

namespace UAVProof.LocalVisitPairingCertificateSize

open VisitCopyLift LocalVisitPairingBounds LocalVisitPairingFiniteCertificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every occurrence is counted separately; the depot contributes exactly one
copy, independently of its demand. This includes zero task demand. -/
theorem visitCopy_card (depot : V) (required : V → ℕ) :
    Fintype.card (VisitCopy depot required) = totalVisits depot required + 1 := by
  simp only [VisitCopy, Fintype.card_option, Fintype.card_sigma, Fintype.card_fin]
  congr 1
  exact (Finset.sum_subtype (Finset.univ.erase depot) (by simp) required).symm

/-- Unpack exactly the existing three fields, including the depot entries. -/
def candidateFieldsEquiv (depot : V) (required : V → ℕ) (service : V → ℚ) (T : ℚ) :
    FiniteCandidate depot required service T ≃
      ((VisitCopy depot required → VisitCopy depot required) ×
        (VisitCopy depot required → Fin (totalVisits depot required + 1)) ×
        (VisitCopy depot required → Fin (gridBound service T + 1))) where
  toFun := fun code => (code.next, code.rank, code.potential)
  invFun := fun f => ⟨f.1, f.2.1, f.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Exact cardinality of raw data, before validity filtering. -/
theorem finiteCandidate_card (depot : V) (required : V → ℕ)
    (service : V → ℚ) (T : ℚ) :
    Fintype.card (FiniteCandidate depot required service T) =
      Fintype.card (VisitCopy depot required) ^ Fintype.card (VisitCopy depot required) *
        (totalVisits depot required + 1) ^ Fintype.card (VisitCopy depot required) *
        (gridBound service T + 1) ^ Fintype.card (VisitCopy depot required) := by
  classical
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, mul_assoc] using
    Fintype.card_congr (candidateFieldsEquiv depot required service T)

theorem finiteCandidate_card_simplified (depot : V) (required : V → ℕ)
    (service : V → ℚ) (T : ℚ) :
    Fintype.card (FiniteCandidate depot required service T) =
      (totalVisits depot required + 1) ^ (2 * (totalVisits depot required + 1)) *
        (gridBound service T + 1) ^ (totalVisits depot required + 1) := by
  rw [finiteCandidate_card, visitCopy_card, ← pow_add, ← two_mul]

/-- Fixed-width storage capacity, with the same two widths for successor and
rank. This is a numerical bound, not a binary encoding implementation. -/
theorem finiteCandidate_card_le_two_pow (depot : V) (required : V → ℕ)
    (service : V → ℚ) (T : ℚ) (wN wB : ℕ)
    (hN : totalVisits depot required + 1 ≤ 2 ^ wN)
    (hB : gridBound service T + 1 ≤ 2 ^ wB) :
    Fintype.card (FiniteCandidate depot required service T) ≤
      2 ^ ((totalVisits depot required + 1) * (2 * wN + wB)) := by
  rw [finiteCandidate_card_simplified]
  calc
    _ ≤ (2 ^ wN) ^ (2 * (totalVisits depot required + 1)) *
        (2 ^ wB) ^ (totalVisits depot required + 1) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hN _) (Nat.pow_le_pow_left hB _)
    _ = _ := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring

/-- Width for all naturals from zero through n, inclusive. -/
def valueWidth (n : ℕ) : ℕ := n.size

theorem valueWidth_capacity (n : ℕ) : n + 1 ≤ 2 ^ valueWidth n :=
  Nat.lt_size_self n

@[simp] theorem valueWidth_zero : valueWidth 0 = 0 := rfl

/-- A concrete choice of sufficient widths; the singleton range uses zero bits. -/
def representationLength (depot : V) (required : V → ℕ) (service : V → ℚ) (T : ℚ) : ℕ :=
  (totalVisits depot required + 1) *
    (2 * valueWidth (totalVisits depot required) + valueWidth (gridBound service T))

theorem finiteCandidate_card_le_representationCapacity
    (depot : V) (required : V → ℕ) (service : V → ℚ) (T : ℚ) :
    Fintype.card (FiniteCandidate depot required service T) ≤
      2 ^ representationLength depot required service T :=
  finiteCandidate_card_le_two_pow depot required service T _ _
    (valueWidth_capacity _) (valueWidth_capacity _)

/-- Even with no task copies, raw depot potential values have not been removed. -/
theorem finiteCandidate_card_of_totalVisits_zero
    (depot : V) (required : V → ℕ) (service : V → ℚ) (T : ℚ)
    (hN : totalVisits depot required = 0) :
    Fintype.card (FiniteCandidate depot required service T) = gridBound service T + 1 := by
  simp [finiteCandidate_card_simplified, hN]

theorem representationLength_of_zero_bounds
    (depot : V) (required : V → ℕ) (service : V → ℚ) (T : ℚ)
    (hN : totalVisits depot required = 0) (hB : gridBound service T = 0) :
    representationLength depot required service T = 0 := by
  simp [representationLength, hN, hB]

#check visitCopy_card
#print axioms visitCopy_card
#check finiteCandidate_card
#print axioms finiteCandidate_card
#check finiteCandidate_card_simplified
#print axioms finiteCandidate_card_simplified
#check finiteCandidate_card_le_two_pow
#print axioms finiteCandidate_card_le_two_pow
#check valueWidth_capacity
#print axioms valueWidth_capacity
#check finiteCandidate_card_le_representationCapacity
#print axioms finiteCandidate_card_le_representationCapacity
#check finiteCandidate_card_of_totalVisits_zero
#print axioms finiteCandidate_card_of_totalVisits_zero
#check representationLength_of_zero_bounds
#print axioms representationLength_of_zero_bounds

end UAVProof.LocalVisitPairingCertificateSize
