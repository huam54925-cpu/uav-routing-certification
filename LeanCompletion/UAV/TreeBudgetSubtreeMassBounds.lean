import LeanCompletion.UAV.TreeBudgetSubtreeStatsGlobalBounds
import Mathlib.Data.Sym.Card

/-! The mass bound is conditional on the positive route dimension. -/
namespace UAVProof.TreeBudgetSubtreeExecutable
open TreeFlowExistence TreeBudgetSubtreeStats

theorem columnCount_le_pow (m h : ℕ) (hm : 0 < m) : columnCount m h ≤ m ^ h := by
  classical
  have hs : Function.Surjective (@Sym.ofVector (Fin m) h) := by
    intro s
    refine ⟨⟨s.val.toList, (Multiset.length_toList s.val).trans s.property⟩, ?_⟩
    apply Subtype.ext
    simp [Sym.ofVector]
  have hc := Fintype.card_le_of_surjective _ hs
  rw [Sym.card_sym_eq_choose, Fintype.card_congr (Equiv.vectorEquivFin (Fin m) h)] at hc
  simp only [Fintype.card_fin, Fintype.card_fun] at hc
  cases m with
  | zero => omega
  | succ k =>
    have he : k + 1 + h - 1 = h + k := by omega
    rw [he] at hc
    have he' : (h + k).choose h = (h + k).choose k := Nat.choose_symm_of_eq_add rfl
    simpa only [columnCount, he'] using hc

theorem columnFactor_le_pow (m h : ℕ) (hm : 0 < m) : columnFactor m h ≤ m ^ h := by
  apply max_le
  · exact Nat.one_le_pow _ _ hm
  · exact columnCount_le_pow m h hm

noncomputable def totalMass {N : ℕ} (R : RootedTree (Fin N)) (H : Fin N → ℕ) : ℕ :=
  ∑ v ∈ Finset.univ.erase R.root, H v

theorem globalProduct_le_mass {N : ℕ} (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (m : ℕ) (hm : 0 < m) : globalProduct R H m ≤ m ^ totalMass R H := by
  unfold globalProduct totalMass
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' (fun _ _ => columnFactor_le_pow m _ hm)

theorem compatible_routes_le_mass {N : ℕ} (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (m : ℕ) (hm : m = ∑ u ∈ R.children R.root, H u) : m ≤ totalMass R H := by
  rw [hm]
  apply Finset.sum_le_sum_of_subset
  intro u hu
  exact Finset.mem_erase.mpr ⟨((R.mem_children _ _).mp hu).1, Finset.mem_univ _⟩

theorem canonical_logicalWork_le {N : ℕ} (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m : ℕ) (T : ℚ) (hm : 0 < m)
    (hroot : m = ∑ u ∈ R.children R.root, H u) :
    logicalWork (checkCompactStats R H s m T).stats ≤
      32 * N * (totalMass R H + 1) ^ 2 * (totalMass R H) ^ (2 * totalMass R H) := by
  let M := totalMass R H
  have hmM : m ≤ M := compatible_routes_le_mass R H m hroot
  have hH : ∀ v, v ≠ R.root → H v ≤ M := by
    intro v hv
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩)
  have hP : globalProduct R H m ≤ M ^ M :=
    (globalProduct_le_mass R H m hm).trans (Nat.pow_le_pow_left hmM M)
  apply (checkCompactStats_logicalWork_le R H s m M T hH).trans
  calc
    32 * N * (m + 1) * (M + 1) * globalProduct R H m ^ 2 ≤
        32 * N * (M + 1) * (M + 1) * (M ^ M) ^ 2 := by gcongr
    _ = _ := by simp only [← pow_mul]; ring

end UAVProof.TreeBudgetSubtreeExecutable
