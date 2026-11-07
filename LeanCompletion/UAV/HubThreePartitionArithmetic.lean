import LeanCompletion.UAV.HubSpokePacking

/-!
Finite arithmetic for the strict-hub three-partition semantic correspondence.
Weights and budgets are natural numbers. Strict bounds are multiplied through,
so no natural-number division is used. Empty row and item types are allowed.
-/

namespace UAVProof.HubThreePartitionArithmetic

variable {R I : Type*} [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
/-- A natural-number column with sum one has exactly one entry equal to one. -/
theorem unit_column_unique (n : R → I → ℕ)
    (hcol : ∀ i, ∑ r, n r i = 1) :
    ∀ i, ∃! r, n r i = 1 := by
  intro i
  have hpos : 0 < ∑ r, n r i := by rw [hcol i]; omega
  obtain ⟨r, hr, hnr⟩ := Finset.sum_pos_iff.mp hpos
  have hle : n r i ≤ 1 := by
    calc
      n r i ≤ ∑ r, n r i :=
        Finset.single_le_sum (fun q _ => Nat.zero_le (n q i)) hr
      _ = 1 := hcol i
  have hone : n r i = 1 := by omega
  refine ⟨r, hone, ?_⟩
  intro r' hr'
  by_contra hne
  have herase : ∑ q ∈ Finset.univ.erase r, n q i = 0 := by
    have h := Finset.sum_erase_add (s := Finset.univ) (f := fun q => n q i) hr
    change (∑ q ∈ Finset.univ.erase r, n q i) + n r i = ∑ q, n q i at h
    rw [hcol i, hone] at h
    omega
  have hzero : n r' i = 0 := by
    have hmem : r' ∈ Finset.univ.erase r := by simp [hne]
    have hle := Finset.single_le_sum (fun q (_ : q ∈ Finset.univ.erase r) =>
      Nat.zero_le (n q i)) hmem
    rw [herase] at hle
    omega
  omega

omit [Fintype I] [DecidableEq I] in
/-- Unit columns are precisely the indicator matrix of an item-to-row assignment. -/
theorem unit_column_assignment (n : R → I → ℕ)
    (hcol : ∀ i, ∑ r, n r i = 1) :
    ∃ assign : I → R, ∀ r i, n r i = if assign i = r then 1 else 0 := by
  classical
  choose assign hass huniq using unit_column_unique n hcol
  refine ⟨assign, ?_⟩
  intro r i
  by_cases heq : assign i = r
  · subst r
    simp [hass]
  · have hle : n r i ≤ 1 := by
      calc
        n r i ≤ ∑ r, n r i :=
          Finset.single_le_sum (fun q _ => Nat.zero_le (n q i)) (Finset.mem_univ r)
        _ = 1 := hcol i
    have hnot : n r i ≠ 1 := by
      intro hone
      exact heq (huniq i r hone).symm
    simp [heq, show n r i = 0 by omega]

omit [DecidableEq R] [DecidableEq I] in
/-- Total weight equal to total capacity makes every bounded row saturate. -/
theorem row_loads_saturate (n : R → I → ℕ) (a : I → ℕ) (B : ℕ)
    (hcol : ∀ i, ∑ r, n r i = 1)
    (htotal : ∑ i, a i = Fintype.card R * B)
    (hbudget : ∀ r, ∑ i, a i * n r i ≤ B) :
    ∀ r, ∑ i, a i * n r i = B := by
  have hsum : (∑ r, ∑ i, a i * n r i) = ∑ _r : R, B := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcol, mul_one]
    simpa using htotal
  exact fun r => (Finset.sum_eq_sum_iff_of_le (fun r _ => hbudget r)).mp hsum
    r (Finset.mem_univ r)

omit [Fintype I] [DecidableEq I] in
/-- A set of weight B has three items under the strict B/4 and B/2 bounds. -/
theorem card_eq_three_of_sum_eq (a : I → ℕ) (B : ℕ)
    (hB : 0 < B) (lower : ∀ i, B < 4 * a i) (upper : ∀ i, 2 * a i < B)
    (P : Finset I) (hsum : ∑ i ∈ P, a i = B) : P.card = 3 := by
  have hne : P.Nonempty := by
    by_contra h
    have hempty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hempty] at hsum
    omega
  have hupper : 2 * B < P.card * B := by
    have h := Finset.sum_lt_sum_of_nonempty hne (fun i (_ : i ∈ P) => upper i)
    simpa [← Finset.mul_sum, hsum] using h
  have hlower : P.card * B < 4 * B := by
    have h := Finset.sum_lt_sum_of_nonempty hne (fun i (_ : i ∈ P) => lower i)
    simpa [← Finset.mul_sum, hsum] using h
  have hcardlo : 2 < P.card := by
    by_contra h
    have hmul := Nat.mul_le_mul_right B (Nat.le_of_not_gt h)
    omega
  have hcardhi : P.card < 4 := by
    by_contra h
    have hmul := Nat.mul_le_mul_right B (Nat.le_of_not_gt h)
    omega
  omega

end UAVProof.HubThreePartitionArithmetic

#print axioms UAVProof.HubThreePartitionArithmetic.unit_column_unique
#print axioms UAVProof.HubThreePartitionArithmetic.unit_column_assignment
#print axioms UAVProof.HubThreePartitionArithmetic.row_loads_saturate
#print axioms UAVProof.HubThreePartitionArithmetic.card_eq_three_of_sum_eq
