import LeanCompletion.UAV.TreeBudgetSubtreeStats
import Mathlib.Data.Nat.Choose.Sum

/-! Exact weak-composition lengths and call-tree sizes for the existing
range-based candidate generator, including dimension zero. -/
namespace UAVProof.TreeBudgetSubtreeExecutable

def columnCount : ℕ → ℕ → ℕ
  | 0, h => if h = 0 then 1 else 0
  | m + 1, h => (h + m).choose m

theorem consV_injective {m : ℕ} (a : ℕ) : Function.Injective (@consV m a) := by
  intro x y h
  apply vector_ext
  intro i
  have := congrArg (fun q => val q i.succ) h
  simpa using this

theorem compositionsV_nodup (m h : ℕ) : (compositionsV m h).Nodup := by
  induction m generalizing h with
  | zero => by_cases hh : h = 0 <;> simp [compositionsV, hh]
  | succ m ih =>
    rw [compositionsV, List.nodup_flatMap]
    refine ⟨fun a _ => (ih (h - a)).map (consV_injective a), ?_⟩
    apply (List.nodup_range (n := h + 1)).imp
    intro a b hab x hx hy
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨r, _, hr⟩ := List.mem_map.mp hy
    apply hab
    have := congrArg (fun z => val z 0) hr
    simpa using this.symm

theorem sum_range_reverse (h : ℕ) (f : ℕ → ℕ) :
    (∑ a ∈ Finset.range (h + 1), f (h - a)) = ∑ a ∈ Finset.range (h + 1), f a := by
  simpa using Finset.sum_range_reflect f (h + 1)

theorem compositionsV_length (m h : ℕ) : (compositionsV m h).length = columnCount m h := by
  induction m generalizing h with
  | zero => by_cases hh : h = 0 <;> simp [compositionsV, columnCount, hh]
  | succ m ih =>
    simp only [compositionsV, List.length_flatMap, List.length_map, ih]
    rw [← List.sum_toFinset _ (List.nodup_range (n := h + 1))]
    simp only [List.toFinset_range]
    rw [sum_range_reverse]
    cases m with
    | zero => simp [columnCount]
    | succ m =>
      simp only [columnCount]
      simpa [Nat.add_assoc] using Nat.sum_range_add_choose h m

end UAVProof.TreeBudgetSubtreeExecutable

namespace UAVProof.TreeBudgetSubtreeStats
open TreeBudgetSubtreeExecutable

theorem sumStats_compositionCalls (ss : List DPStats) :
    (sumStats ss).compositionCalls = (ss.map DPStats.compositionCalls).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [sumStats, DPStats.add, ih]

theorem sumStats_rangeChoices (ss : List DPStats) :
    (sumStats ss).rangeChoices = (ss.map DPStats.rangeChoices).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [sumStats, DPStats.add, ih]

theorem compositionProfile_calls (m h : ℕ) :
    (compositionProfile m h).compositionCalls = (h + m + 1).choose m := by
  induction m generalizing h with
  | zero => simp [compositionProfile]
  | succ m ih =>
    simp only [compositionProfile, DPStats.add, sumStats_compositionCalls, List.map_map,
      Function.comp_def, ih]
    rw [← List.sum_toFinset _ (List.nodup_range (n := h + 1))]
    simp only [List.toFinset_range]
    rw [sum_range_reverse h (fun j => (j + m + 1).choose m)]
    have hh := Nat.sum_range_add_choose (h + 1) m
    rw [Finset.sum_range_succ'] at hh
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem compositionProfile_choices (m h : ℕ) :
    (compositionProfile m h).rangeChoices + 1 = (compositionProfile m h).compositionCalls := by
  induction m generalizing h with
  | zero => rfl
  | succ m ih =>
    simp only [compositionProfile, DPStats.add, sumStats_compositionCalls, sumStats_rangeChoices,
      List.map_map, Function.comp_def]
    have hs : (((List.range (h + 1)).map fun a =>
        (compositionProfile m (h - a)).rangeChoices + 1).sum) =
        ((List.range (h + 1)).map fun a => (compositionProfile m (h - a)).compositionCalls).sum := by
      simp_rw [ih]
    rw [List.sum_map_add] at hs
    simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul, mul_one] at hs
    omega

theorem compositionProfile_calls_le (m h : ℕ) :
    (compositionProfile m h).compositionCalls ≤ (m + 1) * (h + 1) * max 1 (columnCount m h) := by
  rw [compositionProfile_calls]
  cases m with
  | zero => by_cases hh : h = 0 <;> simp [columnCount, hh]
  | succ k =>
    have hq : 1 ≤ (h + k).choose k := Nat.choose_pos (by omega)
    simp only [columnCount, max_eq_right hq]
    have ha := Nat.add_one_mul_choose_eq (h + k) k
    have hb := Nat.choose_mul_succ_eq (h + k + 1) (k + 1)
    have hc : h + k + 1 + 1 - (k + 1) = h + 1 := by omega
    rw [hc] at hb
    have h1 : h + k + 1 ≤ (k + 1) * (h + 1) := by nlinarith
    have h2 : h + k + 1 + 1 ≤ (k + 1 + 1) * (h + 1) := by nlinarith
    have hp := Nat.mul_le_mul h1 h2
    have hqp := Nat.mul_le_mul_right ((h + k).choose k) hp
    have he : (h + (k + 1) + 1).choose (k + 1) * ((k + 1) * (h + 1)) =
        ((h + k + 1) * (h + k + 1 + 1)) * (h + k).choose k := by
      calc
        _ = ((h + k + 1).choose (k + 1) * (h + k + 1 + 1)) * (k + 1) := by
          rw [show h + (k + 1) + 1 = h + k + 1 + 1 by omega]
          nlinarith [hb]
        _ = _ := by nlinarith [ha]
    nlinarith

end UAVProof.TreeBudgetSubtreeStats
