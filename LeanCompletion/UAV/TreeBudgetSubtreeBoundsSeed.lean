import LeanCompletion.UAV.TreeBudgetSubtreeStats
import Mathlib.Tactic

/-!
Draft seed against df2d3f46bafb15b1d0943105e5b3ce3fc63912d7.
NOT compiled in the authoring session. Run in the existing pinned local project.
No new axioms or unfinished proof placeholders are used here. Later grid,
cardinality, full statistics and integer-executor theorems are NOT supplied by
this file; their contracts and paper proofs are in the companion TeX.
-/

namespace UAVProof.TreeBudgetSubtreeBoundsSeed

open TreeFlowExistence TreeBudgetSubtreeState
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def subtreeTotal (R : RootedTree V) (H : V → ℕ)
    (s : V → ℚ) (v : V) : ℚ :=
  ∑ x ∈ subtree R v, linearWeight R s x * (H x : ℚ)

theorem compact_cost_sum {R : RootedTree V} {H : V → ℕ} {m : ℕ}
    {s : V → ℚ} {v : V} {z : CompactState m}
    (hz : CompactRep R H m s v z) :
    (∑ i, z.cost i) = subtreeTotal R H s v := by
  classical
  rcases hz with ⟨n, hn, _hcap, _ha, hc⟩
  calc
    (∑ i, z.cost i) =
        ∑ i, ∑ x ∈ subtree R v,
          linearWeight R s x * (n i x : ℚ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hc i).symm
    _ = ∑ x ∈ subtree R v, ∑ i,
          linearWeight R s x * (n i x : ℚ) := by
      rw [Finset.sum_comm]
    _ = subtreeTotal R H s v := by
      unfold subtreeTotal
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast hn.column x ((mem_subtree R v x).mp hx)

theorem compact_cost_zero_of_not_active
    {R : RootedTree V} {H : V → ℕ} {m : ℕ}
    {s : V → ℚ} {v : V} {z : CompactState m}
    (hz : CompactRep R H m s v z) (i : Fin m)
    (hi : i ∉ z.active) : z.cost i = 0 := by
  classical
  rcases hz with ⟨n, hn, _hcap, ha, hc⟩
  have ht : n i v = 0 := by
    have hnp : ¬ 0 < n i v := fun h => hi ((ha i).mpr h)
    omega
  rw [← hc i, subtreeLinearCost]
  apply Finset.sum_eq_zero
  intro x _
  rw [hn.zero_of_top_zero i ht x, Nat.cast_zero, mul_zero]

/-- Equal-total coordinatewise domination forces equality of cost vectors.
    It does not assert equality of active supports. -/
theorem compact_cost_eq_of_le
    {R : RootedTree V} {H : V → ℕ} {m : ℕ}
    {s : V → ℚ} {v : V} {z z' : CompactState m}
    (hz : CompactRep R H m s v z)
    (hz' : CompactRep R H m s v z')
    (hle : ∀ i, z.cost i ≤ z'.cost i) : z.cost = z'.cost := by
  classical
  have hs : (∑ i, z.cost i) = ∑ i, z'.cost i :=
    (compact_cost_sum hz).trans (compact_cost_sum hz').symm
  have he := (Finset.sum_eq_sum_iff_of_le
    (s := (Finset.univ : Finset (Fin m)))
    (f := z.cost) (g := z'.cost) (fun i _ => hle i)).mp hs
  funext i
  exact he i (Finset.mem_univ i)

/-- For a nonempty label type, forgetting coordinate zero loses no cost data
    on a fixed realizable-state fibre. No executable representation is changed. -/
theorem compact_cost_eq_of_succ_eq
    {R : RootedTree V} {H : V → ℕ} {k : ℕ}
    {s : V → ℚ} {v : V} {z z' : CompactState (k + 1)}
    (hz : CompactRep R H (k + 1) s v z)
    (hz' : CompactRep R H (k + 1) s v z')
    (ht : ∀ i : Fin k, z.cost i.succ = z'.cost i.succ) :
    z.cost = z'.cost := by
  classical
  have hs : (∑ i, z.cost i) = ∑ i, z'.cost i :=
    (compact_cost_sum hz).trans (compact_cost_sum hz').symm
  have htail : (∑ i : Fin k, z.cost i.succ) =
      ∑ i : Fin k, z'.cost i.succ :=
    Finset.sum_congr rfl (fun i _ => ht i)
  simp only [Fin.sum_univ_succ] at hs
  have hzero : z.cost 0 = z'.cost 0 := by linarith
  funext i
  exact Fin.cases hzero ht i

theorem executable_cost_sum {N m : ℕ} (R : RootedTree (Fin N))
    (H : Fin N → ℕ) (s : Fin N → ℚ) (v : Fin N)
    (hv : v ≠ R.root) (e : ExecCompactState m)
    (he : e ∈ computeCompact R H s m v) :
    (∑ i, val e.cost i) = subtreeTotal R H s v := by
  have hz := (computeCompact_spec R H s m v hv e).mp he
  simpa only [decodeState] using compact_cost_sum hz

/-- Pure list envelope; applies before any grid or semantic bound. -/
theorem insideCosts_length_le {m : ℕ}
    (a : Vector Bool m) (base : Vector ℚ m)
    (ts : List (List (ExecCompactState m))) :
    (insideCosts a base ts).length ≤ (ts.map List.length).prod := by
  induction ts with
  | nil => simp [insideCosts]
  | cons t ts ih =>
    change (insideRaw a t (insideCosts a base ts)).dedup.length ≤
      ((t :: ts).map List.length).prod
    calc
      _ ≤ (insideRaw a t (insideCosts a base ts)).length :=
        (List.dedup_sublist _).length_le
      _ = (t.filter (fun e => subsetB e.active a)).length *
          (insideCosts a base ts).length := insideRaw_length _ _ _
      _ ≤ t.length * (ts.map List.length).prod :=
        Nat.mul_le_mul (List.length_filter_le _ _) ih
      _ = _ := by simp

theorem rootFold_length_le {m : ℕ}
    (ts : List (List (ExecCompactState m))) :
    (rootFold ts).length ≤ (ts.map List.length).prod := by
  induction ts with
  | nil => simp [rootFold]
  | cons t ts ih =>
    change ((rootRaw t (rootFold ts)).filter rootCapB).dedup.length ≤
      ((t :: ts).map List.length).prod
    calc
      _ ≤ ((rootRaw t (rootFold ts)).filter rootCapB).length :=
        (List.dedup_sublist _).length_le
      _ ≤ (rootRaw t (rootFold ts)).length := List.length_filter_le _ _
      _ = t.length * (rootFold ts).length := rootRaw_length _ _
      _ ≤ t.length * (ts.map List.length).prod := Nat.mul_le_mul_left _ ih
      _ = _ := by simp

end UAVProof.TreeBudgetSubtreeBoundsSeed

#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.compact_cost_sum
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.compact_cost_zero_of_not_active
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.compact_cost_eq_of_le
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.compact_cost_eq_of_succ_eq
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.executable_cost_sum
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.insideCosts_length_le
#print axioms UAVProof.TreeBudgetSubtreeBoundsSeed.rootFold_length_le
