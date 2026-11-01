import LeanCompletion.UAV.HubSpokePacking
import Mathlib.Algebra.Order.Floor.Div

/-! A closed budget criterion for one satellite and a nonempty fleet. -/
namespace UAVProof.SingleSatelliteClosed
open SupportExactFeasibility HubSpokeSupportExact

theorem exists_bounded_allocation (m n k : ℕ) (h : n ≤ m * k) :
    ∃ a : Fin m → ℕ, (∑ r, a r) = n ∧ ∀ r, a r ≤ k := by
  induction m generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    subst n
    exact ⟨Fin.elim0, by simp, fun r => Fin.elim0 r⟩
  | succ m ih =>
    have hrest : n - min n k ≤ m * k := by
      rw [Nat.succ_mul] at h
      omega
    obtain ⟨a, ha, hk⟩ := ih (n - min n k) hrest
    refine ⟨Fin.cons (min n k) a, ?_, ?_⟩
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, ha]
      omega
    · intro r
      refine Fin.cases ?_ (fun i => ?_) r
      · simpa using Nat.min_le_right n k
      · simpa using hk i

theorem exists_large_row (m n : ℕ) (hm : 0 < m) (a : Fin m → ℕ)
    (ha : (∑ r, a r) = n) : ∃ r, n ⌈/⌉ m ≤ a r := by
  classical
  by_cases hq : n ⌈/⌉ m = 0
  · exact ⟨⟨0, hm⟩, by simp [hq]⟩
  by_contra hn
  push_neg at hn
  have hb : n ≤ m * (n ⌈/⌉ m - 1) := by
    calc
      n = ∑ r, a r := ha.symm
      _ ≤ ∑ _ : Fin m, (n ⌈/⌉ m - 1) := Finset.sum_le_sum (fun r _ => by have := hn r; omega)
      _ = m * (n ⌈/⌉ m - 1) := by simp
  have := (ceilDiv_le_iff_le_mul hm).mpr hb
  omega

theorem allocation_budget_iff (m n : ℕ) (hm : 0 < m) (base weight T : ℚ)
    (hw : 0 ≤ weight) :
    (∃ a : Fin m → ℕ, (∑ r, a r) = n ∧ ∀ r, base + weight * (a r : ℚ) ≤ T) ↔
      base + weight * ((n ⌈/⌉ m : ℕ) : ℚ) ≤ T := by
  constructor
  · rintro ⟨a, ha, hb⟩
    obtain ⟨r, hr⟩ := exists_large_row m n hm a ha
    have hrq : ((n ⌈/⌉ m : ℕ) : ℚ) ≤ (a r : ℚ) := by exact_mod_cast hr
    exact (add_le_add_right (mul_le_mul_of_nonneg_left hrq hw) base).trans (by simpa [add_comm] using hb r)
  · intro hb
    have hbound : n ≤ m * (n ⌈/⌉ m) := (ceilDiv_le_iff_le_mul hm).mp le_rfl
    obtain ⟨a, ha, hk⟩ := exists_bounded_allocation m n (n ⌈/⌉ m) hbound
    refine ⟨a, ha, fun r => ?_⟩
    have hrq : (a r : ℚ) ≤ ((n ⌈/⌉ m : ℕ) : ℚ) := by exact_mod_cast hk r
    have := mul_le_mul_of_nonneg_left hrq hw
    linarith

/-- The hub requirement is m+n, as encoded by `required`. Zero satellite
demand and zero fees are allowed; m=0 is handled by the general matrix theorem. -/
theorem exact_iff_closed (m n : ℕ) (hm : 0 < m) (s : Node Unit → ℚ) (T : ℚ)
    (ha : 0 ≤ s hub) (hb : 0 ≤ s (satellite ())) :
    ExactFeasible depot (canonicalFlow m (fun _ : Unit => n))
      (required m (fun _ : Unit => n)) m s T ↔
      s hub + (s hub + s (satellite ())) * ((n ⌈/⌉ m : ℕ) : ℚ) ≤ T := by
  rw [HubSpokePacking.exact_iff_matrix]
  rw [← allocation_budget_iff m n hm (s hub) (s hub + s (satellite ())) T (add_nonneg ha hb)]
  constructor
  · rintro ⟨a, hc, hbudget⟩
    exact ⟨fun r => a r (), hc (), fun r => by simpa using hbudget r⟩
  · rintro ⟨a, hc, hbudget⟩
    exact ⟨fun r _ => a r, fun _ => hc, fun r => by simpa using hbudget r⟩

end UAVProof.SingleSatelliteClosed

#print axioms UAVProof.SingleSatelliteClosed.allocation_budget_iff
#print axioms UAVProof.SingleSatelliteClosed.exact_iff_closed
