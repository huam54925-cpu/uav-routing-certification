import LeanCompletion.UAV.TreeBudgetSubtreeIntegerWitnessSeed
import LeanCompletion.UAV.TreeBudgetSubtreeMassBounds

/-! Reject incompatible root mass before preprocessing or allocating route vectors.
The guard preserves the whole certificate, including the empty successful one. -/
namespace UAVProof.TreeBudgetSubtreeResource
open TreeFlowExistence TreeBudgetRow TreeBudgetSubtreeExecutable
variable {N : ℕ}

def rootMass (R : RootedTree (Fin N)) (H : Fin N → ℕ) : ℕ :=
  ((childrenList R R.root).map H).sum

theorem rootMass_eq (R : RootedTree (Fin N)) (H : Fin N → ℕ) :
    rootMass R H = ∑ v ∈ R.children R.root, H v :=
  childrenList_sum R R.root H

theorem matrixFeasible_rootMass (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ)
    (hf : TreeBudgetMatrix.MatrixFeasible R H m s T) : m = rootMass R H := by
  classical
  obtain ⟨a, hc, hr, _, _⟩ := hf
  rw [rootMass_eq]
  calc
    m = ∑ i : Fin m, rootDegree R (a i) := by simp [hr]
    _ = ∑ v ∈ R.children R.root, ∑ i : Fin m, a i v := by
      unfold rootDegree
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_congr rfl fun v hv => hc v ((R.mem_children _ _).mp hv).1

def solveGuarded (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    Option (TreeBudgetCertificate.Certificate (Fin N)) :=
  if m = rootMass R H then TreeBudgetSubtreeIntegerWitnessSeed.solveAuto R H s m T
  else none

theorem solveGuarded_eq (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) :
    solveGuarded R H s m T = TreeBudgetSubtreeIntegerWitnessSeed.solveAuto R H s m T := by
  unfold solveGuarded
  split
  · rfl
  · rename_i hbad
    symm
    apply (TreeBudgetSubtreeIntegerWitnessSeed.solveAuto_none_iff R H s m T).2
    intro hf
    exact hbad (matrixFeasible_rootMass R H s m T hf)

theorem rootMass_le_totalMass (R : RootedTree (Fin N)) (H : Fin N → ℕ) :
    rootMass R H ≤ totalMass R H :=
  compatible_routes_le_mass R H _ (rootMass_eq R H)

theorem guarded_routes_le_mass (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (m : ℕ) (hm : m = rootMass R H) : m ≤ totalMass R H :=
  hm ▸ rootMass_le_totalMass R H

theorem globalProduct_zero (R : RootedTree (Fin N)) (H : Fin N → ℕ) :
    globalProduct R H 0 = 1 := by
  classical
  unfold globalProduct
  apply Finset.prod_eq_one
  intro v _
  by_cases h : H v = 0 <;> simp [columnFactor, columnCount, h]

/-- Unlike the earlier positive-route bound, this includes zero routes. -/
theorem guarded_globalProduct_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (m : ℕ) (hm : m = rootMass R H) :
    globalProduct R H m ≤ (max 1 (totalMass R H)) ^ totalMass R H := by
  by_cases hz : m = 0
  · rw [hz, globalProduct_zero]
    exact Nat.one_le_pow _ _ (by omega)
  · exact (globalProduct_le_mass R H m (by omega)).trans
      (Nat.pow_le_pow_left ((guarded_routes_le_mass R H m hm).trans (le_max_right _ _)) _)

end UAVProof.TreeBudgetSubtreeResource
