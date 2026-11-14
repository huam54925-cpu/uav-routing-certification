import LeanCompletion.UAV.TreeBudgetSubtreeDP

/-! Fixed column sums determine total linear cost, including signed costs.
These results leave the executable representation unchanged. -/
namespace UAVProof.TreeBudgetSubtreeState
open TreeFlowExistence TreeBudgetRow
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : RootedTree V} {H : V → ℕ} {m : ℕ} {s : V → ℚ} {v : V}

noncomputable def subtreeTotal (R : RootedTree V) (H : V → ℕ)
    (s : V → ℚ) (v : V) : ℚ :=
  ∑ x ∈ subtree R v, linearWeight R s x * (H x : ℚ)

theorem compact_cost_sum {z : CompactState m} (hz : CompactRep R H m s v z) :
    (∑ i, z.cost i) = subtreeTotal R H s v := by
  obtain ⟨n, hn, _, _, hc⟩ := hz
  simp_rw [← hc, subtreeLinearCost]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.mul_sum, ← Nat.cast_sum, hn.column x ((mem_subtree _ _ _).mp hx)]

theorem compact_cost_zero_of_not_active {z : CompactState m}
    (hz : CompactRep R H m s v z) (i : Fin m) (hi : i ∉ z.active) : z.cost i = 0 := by
  obtain ⟨n, hn, _, ha, hc⟩ := hz
  have ht : n i v = 0 := by have := mt (ha i).mpr hi; omega
  rw [← hc i, subtreeLinearCost]
  simp [hn.zero_of_top_zero i ht]

theorem compact_cost_eq_of_le {z z' : CompactState m}
    (hz : CompactRep R H m s v z) (hz' : CompactRep R H m s v z')
    (hle : ∀ i, z.cost i ≤ z'.cost i) : z.cost = z'.cost := by
  funext i
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp
    ((compact_cost_sum hz).trans (compact_cost_sum hz').symm) i (Finset.mem_univ i)

theorem compact_cost_eq_of_succ_eq {z z' : CompactState (m + 1)}
    (hz : CompactRep R H (m + 1) s v z) (hz' : CompactRep R H (m + 1) s v z')
    (he : ∀ i : Fin m, z.cost i.succ = z'.cost i.succ) : z.cost = z'.cost := by
  have hs := (compact_cost_sum hz).trans (compact_cost_sum hz').symm
  simp only [Fin.sum_univ_succ] at hs
  have ht : (∑ i : Fin m, z.cost i.succ) = ∑ i : Fin m, z'.cost i.succ :=
    Finset.sum_congr rfl (fun i _ => he i)
  funext i
  refine Fin.cases ?_ he i
  linarith

theorem compact_cost_recover {z : CompactState m} (hz : CompactRep R H m s v z)
    (p : Fin m) : z.cost p = subtreeTotal R H s v - ∑ i ∈ Finset.univ.erase p, z.cost i := by
  have hs := Finset.sum_erase_add Finset.univ z.cost (Finset.mem_univ p)
  rw [compact_cost_sum hz] at hs
  linarith

theorem compact_active_card_le {z : CompactState m} (hz : CompactRep R H m s v z) :
    z.active.card ≤ min m (H v) := by
  obtain ⟨n, hn, _, ha, _⟩ := hz
  apply le_min (by simpa using z.active.card_le_univ)
  calc
    z.active.card = ∑ i ∈ z.active, 1 := by simp
    _ ≤ ∑ i ∈ z.active, n i v := Finset.sum_le_sum (fun i hi => (ha i).mp hi)
    _ ≤ ∑ i, n i v := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = H v := hn.column v .self

theorem compact_active_card_root_child {z : CompactState m}
    (hz : CompactRep R H m s v z) (hp : R.parent v = R.root) : z.active.card = H v := by
  obtain ⟨n, hn, hcap, ha, _⟩ := hz
  rw [← hn.column v .self]
  simp_rw [capped_eq_indicator (fun i => n i v) z.active (hcap hp) ha]
  simp

theorem compact_zero_top_demands {z : CompactState m}
    (hz : CompactRep R H m s v z) (hzero : H v = 0) :
    ∀ x, InSubtree R v x → H x = 0 := by
  obtain ⟨n, hn, _, _, _⟩ := hz
  intro x hx
  rw [← hn.column x hx]
  apply Finset.sum_eq_zero
  intro i _
  exact hn.zero_of_top_zero i (by have := hn.entry_le i v .self; omega) x

theorem compact_zero_routes_demands {z : CompactState 0}
    (hz : CompactRep R H 0 s v z) : ∀ x, InSubtree R v x → H x = 0 := by
  obtain ⟨n, hn, _, _, _⟩ := hz
  intro x hx
  simpa using (hn.column x hx).symm

theorem compact_zero_rep (hzero : ∀ x, InSubtree R v x → H x = 0) :
    CompactRep R H m s v ⟨∅, fun _ => 0⟩ := by
  refine ⟨fun _ _ => 0, ⟨by simp, ?_, by simp⟩, by simp [RootChildCap], by simp, ?_⟩
  · intro x hx; simp [hzero x hx]
  · intro i; simp [subtreeLinearCost]

theorem compact_zero_top_iff {z : CompactState m} (hzero : H v = 0) :
    CompactRep R H m s v z ↔
      (∀ x, InSubtree R v x → H x = 0) ∧ z = ⟨∅, fun _ => 0⟩ := by
  constructor
  · intro hz
    refine ⟨compact_zero_top_demands hz hzero, ?_⟩
    have ha : z.active = ∅ := Finset.card_eq_zero.mp (by
      have hh := compact_active_card_le hz
      have : z.active.card ≤ 0 := by simpa only [hzero, min_zero] using hh
      omega)
    have hc : z.cost = fun _ => 0 := funext (fun i =>
      compact_cost_zero_of_not_active hz i (by simp [ha]))
    cases z
    simp_all
  · rintro ⟨hh, rfl⟩; exact compact_zero_rep hh

theorem compact_zero_routes_iff {z : CompactState 0} :
    CompactRep R H 0 s v z ↔
      (∀ x, InSubtree R v x → H x = 0) ∧ z = ⟨∅, fun _ => 0⟩ := by
  have he : z = ⟨∅, fun _ => 0⟩ := by
    cases z with
    | mk a c =>
      have ha : a = ∅ := by ext i; exact Fin.elim0 i
      have hc : c = fun _ => 0 := funext (fun i => Fin.elim0 i)
      simp [ha, hc]
  constructor
  · intro hz; exact ⟨compact_zero_routes_demands hz, he⟩
  · rintro ⟨hh, rfl⟩; exact compact_zero_rep hh

end UAVProof.TreeBudgetSubtreeState

namespace UAVProof.TreeBudgetSubtreeExecutable
open TreeFlowExistence TreeBudgetSubtreeState

theorem executable_cost_sum {N m : ℕ} (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (v : Fin N) (hv : v ≠ R.root)
    {e : ExecCompactState m} (he : e ∈ computeCompact R H s m v) :
    (∑ i, val e.cost i) = subtreeTotal R H s v :=
  compact_cost_sum ((computeCompact_spec R H s m v hv e).mp he)

end UAVProof.TreeBudgetSubtreeExecutable
