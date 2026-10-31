import LeanCompletion.UAV.LocalVisitPairingCertificateSize

/-!
# Rational input bounds for finite candidate representation capacity

Reuse the existing service denominator D, grid bound B and representation
length. Sden counts the binary sizes of the canonical service denominators;
the budget contributes the size of its absolute canonical numerator.

These are numerical capacity bounds, not an encoder or a runtime theorem.
N remains the expanded visit count. Service numerators, the budget denominator,
flow entries, demand encoding, signs and framing still belong to the full input.
No polynomial bound in compact binary input length is asserted.
-/

namespace UAVProof.LocalVisitPairingInputSize

open scoped BigOperators
open LocalVisitPairingPotentialGrid LocalVisitPairingFiniteCertificate
open LocalVisitPairingBounds LocalVisitPairingCertificateSize

/-- A finite product of bounded naturals fits the sum of the exponent bounds,
including the empty product. -/
theorem prod_le_two_pow_sum {ι : Type*} (s : Finset ι) (f w : ι → ℕ)
    (h : ∀ i ∈ s, f i ≤ 2 ^ w i) :
    ∏ i ∈ s, f i ≤ 2 ^ (∑ i ∈ s, w i) := by
  calc
    _ ≤ ∏ i ∈ s, 2 ^ w i := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) h
    _ = _ := Finset.prod_pow_eq_pow_sum s w 2

variable {V : Type*} [Fintype V]

/-- Only the canonical service denominator widths, including the depot. -/
def serviceDenominatorSize (service : V → ℚ) : ℕ :=
  ∑ v, (service v).den.size

theorem serviceDenominator_le_two_pow (service : V → ℚ) :
    serviceDenominator service ≤ 2 ^ serviceDenominatorSize service :=
  prod_le_two_pow_sum Finset.univ (fun v => (service v).den)
    (fun v => (service v).den.size) (fun _ _ => (Nat.lt_size_self _).le)

/-- Works even when V is empty: then D=1 and Sden=0. -/
theorem serviceDenominator_size_le_succ (service : V → ℚ) :
    (serviceDenominator service).size ≤ serviceDenominatorSize service + 1 := by
  simpa only [Nat.size_pow] using
    Nat.size_le_size (serviceDenominator_le_two_pow service)

/-- The stronger bound explicitly requires a nonempty physical type. -/
theorem serviceDenominator_size_le [Nonempty V] (service : V → ℚ) :
    (serviceDenominator service).size ≤ serviceDenominatorSize service := by
  apply Nat.size_le.mpr
  calc
    _ < ∏ v, 2 ^ (service v).den.size :=
      Finset.prod_lt_prod_of_nonempty (fun v _ => (service v).den_pos)
        (fun v _ => Nat.lt_size_self _) Finset.univ_nonempty
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

/-- A nonnegative rational is bounded by its absolute canonical numerator. -/
theorem budget_le_num_natAbs (T : ℚ) (hT : 0 ≤ T) :
    T ≤ (T.num.natAbs : ℚ) := by
  have hd : (1 : ℚ) ≤ T.den := by exact_mod_cast T.den_pos
  have hn : (T.num : ℚ) ≤ (T.num.natAbs : ℚ) := by
    have hcast : (T.num : ℚ) ≤ ((T.num.natAbs : ℤ) : ℚ) :=
      Int.cast_le.mpr Int.le_natAbs
    simpa only [Int.cast_natCast] using hcast
  calc
    T = 1 * T := (one_mul T).symm
    _ ≤ (T.den : ℚ) * T := mul_le_mul_of_nonneg_right hd hT
    _ = (T.num : ℚ) := Rat.den_mul_eq_num T
    _ ≤ _ := hn

theorem gridBound_le_denominator_mul_num (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
    gridBound service T ≤ serviceDenominator service * T.num.natAbs := by
  have hb : (gridBound service T : ℚ) ≤ (serviceDenominator service : ℚ) * T := by
    have hf := Int.floor_le ((serviceDenominator service : ℚ) * T)
    rw [← gridBound_cast service T hT] at hf
    simpa only [Int.cast_natCast] using hf
  have hm := mul_le_mul_of_nonneg_left (budget_le_num_natAbs T hT)
    (Nat.cast_nonneg (serviceDenominator service) : (0 : ℚ) ≤ _)
  exact_mod_cast hb.trans hm

/-- Strictness comes from the numerator bound, including numerator zero. -/
theorem gridBound_lt_two_pow_inputSize (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
    gridBound service T < 2 ^ (serviceDenominatorSize service + T.num.natAbs.size) := by
  calc
    _ ≤ serviceDenominator service * T.num.natAbs :=
      gridBound_le_denominator_mul_num service T hT
    _ ≤ 2 ^ serviceDenominatorSize service * T.num.natAbs :=
      Nat.mul_le_mul_right _ (serviceDenominator_le_two_pow service)
    _ < 2 ^ serviceDenominatorSize service * 2 ^ T.num.natAbs.size :=
      Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self _) (by positivity)
    _ = _ := (pow_add _ _ _).symm

theorem gridBound_size_le (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
    (gridBound service T).size ≤ serviceDenominatorSize service + T.num.natAbs.size :=
  Nat.size_le.mpr (gridBound_lt_two_pow_inputSize service T hT)

variable [DecidableEq V]

theorem representationLength_le_inputSize (depot : V) (required : V → ℕ)
    (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
    representationLength depot required service T ≤
      (totalVisits depot required + 1) *
        (2 * (totalVisits depot required).size + serviceDenominatorSize service +
          T.num.natAbs.size) := by
  unfold representationLength valueWidth
  apply Nat.mul_le_mul_left
  have := gridBound_size_le service T hT
  omega

theorem finiteCandidate_card_le_inputCapacity (depot : V) (required : V → ℕ)
    (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
    Fintype.card (FiniteCandidate depot required service T) ≤
      2 ^ ((totalVisits depot required + 1) *
        (2 * (totalVisits depot required).size + serviceDenominatorSize service +
          T.num.natAbs.size)) :=
  (finiteCandidate_card_le_representationCapacity depot required service T).trans
    (Nat.pow_le_pow_right (by decide)
      (representationLength_le_inputSize depot required service T hT))

/-! Boundary checks use kernel proofs, not native_decide. -/

omit [DecidableEq V] in
theorem gridBound_zero_budget (service : V → ℚ) : gridBound service 0 = 0 := by
  simp [gridBound]

omit [DecidableEq V] in
theorem serviceDenominator_eq_one (service : V → ℚ)
    (h : ∀ v, (service v).den = 1) : serviceDenominator service = 1 := by
  simp [serviceDenominator, h]

theorem zero_task_representation (depot : V) (required : V → ℕ)
    (service : V → ℚ) (T : ℚ) (hzero : ∀ v, v ≠ depot → required v = 0) :
    representationLength depot required service T = (gridBound service T).size := by
  simp [representationLength, valueWidth,
    totalVisits_eq_zero_of_task_zero depot required hzero]

theorem empty_denominator_boundary :
    serviceDenominator (fun v : Fin 0 => (v.val : ℚ)) = 1 ∧
    serviceDenominatorSize (fun v : Fin 0 => (v.val : ℚ)) = 0 ∧
    (serviceDenominator (fun v : Fin 0 => (v.val : ℚ))).size = 1 := by
  decide +kernel

theorem unit_denominator_fractional_budget_boundary :
    serviceDenominator (fun _ : Fin 1 => (1 : ℚ)) = 1 ∧
    (0 : ℚ) < 1 / 2 ∧ (1 / 2 : ℚ) < 1 ∧
    gridBound (fun _ : Fin 1 => (1 : ℚ)) (1 / 2) = 0 := by
  decide +kernel

/-- D=2, T=3/4 and D*T=3/2: floor must give 1, not 2. -/
theorem nonintegral_scaled_budget_boundary :
    serviceDenominator (fun _ : Fin 1 => (1 / 2 : ℚ)) = 2 ∧
    (serviceDenominator (fun _ : Fin 1 => (1 / 2 : ℚ)) : ℚ) * (3 / 4) = 3 / 2 ∧
    gridBound (fun _ : Fin 1 => (1 / 2 : ℚ)) (3 / 4) = 1 ∧
    (gridBound (fun _ : Fin 1 => (1 / 2 : ℚ)) (3 / 4)).size = 1 := by
  decide +kernel

/-- Zero task demand still leaves the raw depot potential field. -/
theorem zero_demand_positive_grid_boundary :
    representationLength (0 : Fin 2) (fun _ => 0) (fun _ => (1 : ℚ)) 2 = 2 := by
  decide +kernel

theorem zero_demand_zero_budget_boundary :
    representationLength (0 : Fin 2) (fun _ => 0) (fun _ => (1 : ℚ)) 0 = 0 ∧
    (0 : ℚ).num.natAbs.size = 0 := by
  decide +kernel

#check prod_le_two_pow_sum
#print axioms prod_le_two_pow_sum
#check serviceDenominator_le_two_pow
#print axioms serviceDenominator_le_two_pow
#check serviceDenominator_size_le_succ
#print axioms serviceDenominator_size_le_succ
#check serviceDenominator_size_le
#print axioms serviceDenominator_size_le
#check budget_le_num_natAbs
#print axioms budget_le_num_natAbs
#check gridBound_le_denominator_mul_num
#print axioms gridBound_le_denominator_mul_num
#check gridBound_lt_two_pow_inputSize
#print axioms gridBound_lt_two_pow_inputSize
#check gridBound_size_le
#print axioms gridBound_size_le
#check representationLength_le_inputSize
#print axioms representationLength_le_inputSize
#check finiteCandidate_card_le_inputCapacity
#print axioms finiteCandidate_card_le_inputCapacity
#check gridBound_zero_budget
#print axioms gridBound_zero_budget
#check serviceDenominator_eq_one
#print axioms serviceDenominator_eq_one
#check zero_task_representation
#print axioms zero_task_representation
#check empty_denominator_boundary
#print axioms empty_denominator_boundary
#check unit_denominator_fractional_budget_boundary
#print axioms unit_denominator_fractional_budget_boundary
#check nonintegral_scaled_budget_boundary
#print axioms nonintegral_scaled_budget_boundary
#check zero_demand_positive_grid_boundary
#print axioms zero_demand_positive_grid_boundary
#check zero_demand_zero_budget_boundary
#print axioms zero_demand_zero_budget_boundary

end UAVProof.LocalVisitPairingInputSize
