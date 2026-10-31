import LeanCompletion.UAV.LocalVisitPairingBounds
import Mathlib.Data.Rat.Floor

/-!
# A common denominator for canonical suffix-service potentials

Scaling every input service fee to an integer also scales every finite list
sum and every canonical routePotential value to an integer. Repeated visits
are counted with multiplicity. This integrality statement needs no sign or
budget assumptions and applies at the depot and to empty route families.

For finite physical types, the product of input service denominators is a
positive common denominator. The depot service fee may participate in this
product; no assumption on depot demand is made. The budget denominator is
not included, so the upper bound uses the integer floor of D * T.

With nonnegative fees and budget, the existing canonical potential bounds
give nonnegative integer witnesses, then natural-number witnesses. No
truncation is used until integer nonnegativity has been proved. The result
concerns the specified canonical suffix potential, not every budget potential.
No finite-certificate encoding, input-next preservation, search algorithm or
polynomial bit-complexity claim is made here.
-/

namespace UAVProof.LocalVisitPairingPotentialGrid

open scoped BigOperators
open ResourceCuts VisitCopyLift LocalVisitPairingCompleteness LocalVisitPairingBounds

section ListService

variable {V : Type*}

/-- Integrality is closed under finite sums, even without a positivity condition
on D. List induction retains each occurrence of a repeated vertex. -/
theorem service_sum_integral (service : V → ℚ) (D : ℕ)
    (hgrid : ∀ v, ∃ z : ℤ, (D : ℚ) * service v = (z : ℚ)) (visits : List V) :
    ∃ z : ℤ, (D : ℚ) * (visits.map service).sum = (z : ℚ) := by
  induction visits with
  | nil => exact ⟨0, by simp⟩
  | cons v visits ih =>
    obtain ⟨zv, hv⟩ := hgrid v
    obtain ⟨zs, hs⟩ := ih
    refine ⟨zv + zs, ?_⟩
    rw [List.map_cons, List.sum_cons, mul_add, hv, hs, Int.cast_add]

theorem suffix_service_integral (service : V → ℚ) (D : ℕ)
    (hgrid : ∀ v, ∃ z : ℤ, (D : ℚ) * service v = (z : ℚ))
    (visits : List V) (i : ℕ) :
    ∃ z : ℤ, (D : ℚ) * ((visits.drop i).map service).sum = (z : ℚ) :=
  service_sum_integral service D hgrid (visits.drop i)

end ListService

section CommonDenominator

variable {V : Type*} [Fintype V]

/-- A positive common denominator using every input service denominator.
This deliberately makes no least-common-multiple or size optimality claim. -/
def serviceDenominator (service : V → ℚ) : ℕ := ∏ v, (service v).den

theorem serviceDenominator_pos (service : V → ℚ) : 0 < serviceDenominator service :=
  Finset.prod_pos (fun v _ => (service v).den_pos)

theorem serviceDenominator_integral (service : V → ℚ) (v : V) :
    ∃ z : ℤ, (serviceDenominator service : ℚ) * service v = (z : ℚ) := by
  have hdiv : (service v).den ∣ serviceDenominator service :=
    Finset.dvd_prod_of_mem (fun w => (service w).den) (Finset.mem_univ v)
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨(k : ℤ) * (service v).num, ?_⟩
  rw [hk, Nat.cast_mul]
  calc
    ((service v).den : ℚ) * (k : ℚ) * service v =
        (k : ℚ) * ((service v).den * service v) := by ring
    _ = ((k : ℤ) * (service v).num : ℤ) := by
      rw [Rat.den_mul_eq_num]
      simp

omit [Fintype V] in
/-- Every finite rational service input has a positive common denominator,
independently of its signs, task demands, route family, and budget. -/
theorem exists_service_denominator [Finite V] (service : V → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ v, ∃ z : ℤ, (D : ℚ) * service v = (z : ℚ) := by
  letI := Fintype.ofFinite V
  exact ⟨serviceDenominator service, serviceDenominator_pos service,
    serviceDenominator_integral service⟩

end CommonDenominator

section RoutePotential

variable {V : Type*} [DecidableEq V]
variable {ι : Type*} [Fintype ι]
variable (depot : V) (required : V → ℕ) (routes : ι → LegalRoute depot)
variable (hcover : ∀ v, v ≠ depot → totalVisitCount Finset.univ routes v = required v)

/-- A single common service denominator works at every canonical copy.
No finite physical-type or nonempty route-family hypothesis is needed here. -/
theorem routePotential_integral (service : V → ℚ) (D : ℕ)
    (hgrid : ∀ v, ∃ z : ℤ, (D : ℚ) * service v = (z : ℚ))
    (c : VisitCopy depot required) :
    ∃ z : ℤ, (D : ℚ) * routePotential depot required routes hcover service c = (z : ℚ) := by
  by_cases hc : c = none
  · subst c
    exact ⟨0, by simp⟩
  · obtain ⟨p, rfl, _⟩ := existsUnique_positionCopy depot required routes hcover c hc
    rw [routePotential_position]
    exact suffix_service_integral service D hgrid (routes p.1).visits p.2.val

/-- First bound an actual integer witness. The budget need not lie on the grid. -/
theorem routePotential_int_grid_bounds [Fintype V]
    (service : V → ℚ) (hservice : ∀ v, 0 ≤ service v) (T : ℚ) (hT : 0 ≤ T)
    (hbudget : ∀ r, routeServiceIn (routes r) Finset.univ service ≤ T)
    (D : ℕ) (hD : 0 < D)
    (hgrid : ∀ v, ∃ z : ℤ, (D : ℚ) * service v = (z : ℚ))
    (c : VisitCopy depot required) :
    ∃ z : ℤ, (D : ℚ) * routePotential depot required routes hcover service c = (z : ℚ) ∧
      0 ≤ z ∧ z ≤ Int.floor ((D : ℚ) * T) := by
  obtain ⟨z, hz⟩ := routePotential_integral depot required routes hcover service D hgrid c
  have hb := routePotential_bounds depot required routes hcover service hservice T hT hbudget c
  have hDq : 0 ≤ (D : ℚ) := le_of_lt (by exact_mod_cast hD)
  refine ⟨z, hz, ?_, ?_⟩
  · have hzq : (0 : ℚ) ≤ (z : ℚ) := by
      rw [← hz]
      exact mul_nonneg hDq hb.1
    exact_mod_cast hzq
  · apply Int.le_floor.mpr
    rw [← hz]
    exact mul_le_mul_of_nonneg_left hb.2 hDq

/-- Only after proving 0 ≤ z do we convert the integer witness to a natural.
Its integer cast retains the floor bound, without truncating a negative value. -/
theorem routePotential_nat_grid_bounds [Fintype V]
    (service : V → ℚ) (hservice : ∀ v, 0 ≤ service v) (T : ℚ) (hT : 0 ≤ T)
    (hbudget : ∀ r, routeServiceIn (routes r) Finset.univ service ≤ T)
    (D : ℕ) (hD : 0 < D)
    (hgrid : ∀ v, ∃ z : ℤ, (D : ℚ) * service v = (z : ℚ))
    (c : VisitCopy depot required) :
    ∃ k : ℕ, (k : ℚ) = (D : ℚ) * routePotential depot required routes hcover service c ∧
      (k : ℤ) ≤ Int.floor ((D : ℚ) * T) := by
  obtain ⟨z, hz, hz0, hzbound⟩ :=
    routePotential_int_grid_bounds depot required routes hcover
      service hservice T hT hbudget D hD hgrid c
  have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
  refine ⟨z.toNat, ?_, ?_⟩
  · calc
      (z.toNat : ℚ) = ((z.toNat : ℤ) : ℚ) := by simp only [Int.cast_natCast]
      _ = (z : ℚ) := congrArg (fun n : ℤ => (n : ℚ)) hcast
      _ = (D : ℚ) * routePotential depot required routes hcover service c := hz.symm
  · simpa only [hcast] using hzbound

/-- Choose the same positive D for every canonical potential value. D depends
only on the input service fees; in particular it does not include T's denominator. -/
theorem exists_routePotential_nat_grid [Fintype V]
    (service : V → ℚ) (hservice : ∀ v, 0 ≤ service v) (T : ℚ) (hT : 0 ≤ T)
    (hbudget : ∀ r, routeServiceIn (routes r) Finset.univ service ≤ T) :
    ∃ D : ℕ, 0 < D ∧
      (∀ v, ∃ z : ℤ, (D : ℚ) * service v = (z : ℚ)) ∧
      ∀ c : VisitCopy depot required, ∃ k : ℕ,
        (k : ℚ) = (D : ℚ) * routePotential depot required routes hcover service c ∧
          (k : ℤ) ≤ Int.floor ((D : ℚ) * T) := by
  refine ⟨serviceDenominator service, serviceDenominator_pos service,
    serviceDenominator_integral service, ?_⟩
  intro c
  exact routePotential_nat_grid_bounds depot required routes hcover service hservice T hT hbudget
    (serviceDenominator service) (serviceDenominator_pos service)
    (serviceDenominator_integral service) c

end RoutePotential

end UAVProof.LocalVisitPairingPotentialGrid

#check UAVProof.LocalVisitPairingPotentialGrid.service_sum_integral
#check UAVProof.LocalVisitPairingPotentialGrid.suffix_service_integral
#check UAVProof.LocalVisitPairingPotentialGrid.serviceDenominator
#check UAVProof.LocalVisitPairingPotentialGrid.serviceDenominator_pos
#check UAVProof.LocalVisitPairingPotentialGrid.serviceDenominator_integral
#check UAVProof.LocalVisitPairingPotentialGrid.exists_service_denominator
#check UAVProof.LocalVisitPairingPotentialGrid.routePotential_integral
#check UAVProof.LocalVisitPairingPotentialGrid.routePotential_int_grid_bounds
#check UAVProof.LocalVisitPairingPotentialGrid.routePotential_nat_grid_bounds
#check UAVProof.LocalVisitPairingPotentialGrid.exists_routePotential_nat_grid

#print axioms UAVProof.LocalVisitPairingPotentialGrid.service_sum_integral
#print axioms UAVProof.LocalVisitPairingPotentialGrid.suffix_service_integral
#print axioms UAVProof.LocalVisitPairingPotentialGrid.serviceDenominator_pos
#print axioms UAVProof.LocalVisitPairingPotentialGrid.serviceDenominator_integral
#print axioms UAVProof.LocalVisitPairingPotentialGrid.exists_service_denominator
#print axioms UAVProof.LocalVisitPairingPotentialGrid.routePotential_integral
#print axioms UAVProof.LocalVisitPairingPotentialGrid.routePotential_int_grid_bounds
#print axioms UAVProof.LocalVisitPairingPotentialGrid.routePotential_nat_grid_bounds
#print axioms UAVProof.LocalVisitPairingPotentialGrid.exists_routePotential_nat_grid
