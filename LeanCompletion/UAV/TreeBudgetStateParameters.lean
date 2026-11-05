import LeanCompletion.UAV.TreeBudgetMemoBounds

/-! Two numerical envelopes for the existing finite-state bound. Root values
are excluded throughout; zero-valued coordinates do not affect the product.
These are combinatorial inequalities, not encoded runtime or FPT/XP results. -/
namespace UAVProof.TreeBudgetStateParameters
open TreeFlowExistence TreeBudgetMemoBounds
variable {n : ℕ}

def nonrootVertices (R : RootedTree (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v ≠ R.root)

/-- M: total multiplicity of the nonroot parent edges. -/
def totalMultiplicity (R : RootedTree (Fin n)) (H : Fin n → ℕ) : ℕ :=
  ∑ v ∈ nonrootVertices R, H v

def positiveCoordinates (R : RootedTree (Fin n)) (H : Fin n → ℕ) : Finset (Fin n) :=
  (nonrootVertices R).filter (fun v => 0 < H v)

/-- t: only positive nonroot coordinates contribute more than one state choice. -/
def positiveCount (R : RootedTree (Fin n)) (H : Fin n → ℕ) : ℕ :=
  (positiveCoordinates R H).card

/-- U: the maximum nonroot multiplicity; the supremum of an empty Nat finset
is zero. Including zero coordinates gives the same maximum as positive support. -/
def maxMultiplicity (R : RootedTree (Fin n)) (H : Fin n → ℕ) : ℕ :=
  (nonrootVertices R).sup H

theorem add_one_le_two_pow (h : ℕ) : h + 1 ≤ 2 ^ h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ]
    omega

/-- This finite-product inequality also covers an empty index set. -/
theorem prod_add_one_le_two_pow_sum {α : Type*} (s : Finset α) (H : α → ℕ) :
    (∏ v ∈ s, (H v + 1)) ≤ 2 ^ (∑ v ∈ s, H v) := by
  calc
    (∏ v ∈ s, (H v + 1)) ≤ ∏ v ∈ s, 2 ^ H v :=
      Finset.prod_le_prod' (fun v _ => add_one_le_two_pow (H v))
    _ = 2 ^ (∑ v ∈ s, H v) := Finset.prod_pow_eq_pow_sum s H 2

theorem multiplicity_le_maxMultiplicity (R : RootedTree (Fin n))
    (H : Fin n → ℕ) (v : Fin n) (hv : v ≠ R.root) : H v ≤ maxMultiplicity R H := by
  exact Finset.le_sup (by simp [nonrootVertices, hv])

/-- Removing zero coordinates removes only factors equal to one. -/
theorem stateBound_eq_prod_positiveCoordinates (R : RootedTree (Fin n))
    (H : Fin n → ℕ) :
    stateBound R H = ∏ v ∈ positiveCoordinates R H, (H v + 1) := by
  change (∏ v ∈ nonrootVertices R, (H v + 1)) =
    ∏ v ∈ (nonrootVertices R).filter (fun v => 0 < H v), (H v + 1)
  symm
  apply Finset.prod_filter_of_ne
  intro v _ hv
  omega

/-- S(H) is bounded exponentially in total nonroot multiplicity M. -/
theorem stateBound_le_two_pow_totalMultiplicity (R : RootedTree (Fin n))
    (H : Fin n → ℕ) : stateBound R H ≤ 2 ^ totalMultiplicity R H :=
  prod_add_one_le_two_pow_sum (nonrootVertices R) H

/-- S(H) is at most (U+1)^t, including t=0 and U=0 without extra assumptions. -/
theorem stateBound_le_maxMultiplicity_pow_positiveCount (R : RootedTree (Fin n))
    (H : Fin n → ℕ) :
    stateBound R H ≤ (maxMultiplicity R H + 1) ^ positiveCount R H := by
  rw [stateBound_eq_prod_positiveCoordinates]
  apply Finset.prod_le_pow_card
  intro v hv
  simp only [positiveCoordinates, nonrootVertices, Finset.mem_filter,
    Finset.mem_univ, true_and] at hv
  exact Nat.add_le_add_right (multiplicity_le_maxMultiplicity R H v hv.1) 1

end UAVProof.TreeBudgetStateParameters

#print axioms UAVProof.TreeBudgetStateParameters.add_one_le_two_pow
#print axioms UAVProof.TreeBudgetStateParameters.prod_add_one_le_two_pow_sum
#print axioms UAVProof.TreeBudgetStateParameters.multiplicity_le_maxMultiplicity
#print axioms UAVProof.TreeBudgetStateParameters.stateBound_eq_prod_positiveCoordinates
#print axioms UAVProof.TreeBudgetStateParameters.stateBound_le_two_pow_totalMultiplicity
#print axioms UAVProof.TreeBudgetStateParameters.stateBound_le_maxMultiplicity_pow_positiveCount
