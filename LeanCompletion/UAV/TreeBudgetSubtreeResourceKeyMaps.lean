import LeanCompletion.UAV.TreeBudgetSubtreeResourceStats

/-! The full list map is charged independently of short-circuit comparisons. -/
namespace UAVProof.TreeBudgetSubtreeResourceSeed
open TreeFlowExistence TreeBudgetSubtreeState TreeBudgetSubtreeExecutable
open TreeBudgetSubtreeStats TreeBudgetSubtreeIntegerWitnessSeed
variable {N m : ℕ}

def MapBound (s : DPStats) (p : PayloadStats) : Prop :=
  2 * p.keyMapCells ≤ s.dedupInput * (s.maxRawTable - 1)

theorem mapBound_zero (s : DPStats) : MapBound s {} := by simp [MapBound]

theorem mapBound_add {s t : DPStats} {p q : PayloadStats}
    (hs : MapBound s p) (ht : MapBound t q) : MapBound (s.add t) (p.add q) := by
  have h₁ := Nat.mul_le_mul_left s.dedupInput
    (Nat.sub_le_sub_right (le_max_left s.maxRawTable t.maxRawTable) 1)
  have h₂ := Nat.mul_le_mul_left t.dedupInput
    (Nat.sub_le_sub_right (le_max_right s.maxRawTable t.maxRawTable) 1)
  simp only [MapBound, DPStats.add, PayloadStats.add, Nat.add_mul] at *
  omega

theorem mapBound_stats_left (s : DPStats) {t : DPStats} {p : PayloadStats}
    (h : MapBound t p) : MapBound (s.add t) p := by
  simpa using mapBound_add (mapBound_zero s) h

theorem mapBound_sum {α : Type} (xs : List α) (s : α → DPStats) (p : α → PayloadStats)
    (h : ∀ x ∈ xs, MapBound (s x) (p x)) :
    MapBound (sumStats (xs.map s)) (sumPayload (xs.map p)) := by
  induction xs with
  | nil => exact mapBound_zero _
  | cons x xs ih =>
    exact mapBound_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem dedupResource_mapBound {α κ : Type} [DecidableEq κ] (key : α → κ) (xs : List α) :
    MapBound (dedupResource key xs).keyStats (dedupResource key xs).payload := by
  simpa [MapBound, dedupResource] using keyMapSpec_triangle key xs

theorem insideR_mapBound (a : Vector Bool m) (base : Vector ℤ m)
    (ts : List (List (Entry N m))) : MapBound (insideR a base ts).keyStats
      (insideR a base ts).payload := by
  induction ts with
  | nil => exact mapBound_zero _
  | cons t ts ih =>
    exact mapBound_add ih (mapBound_add (by simp [MapBound]) (dedupResource_mapBound _ _))

theorem nodeR_mapBound (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) (ts : List (List (Entry N m))) :
    MapBound (nodeR R H w m v ts).keyStats (nodeR R H w m v ts).payload := by
  have hz (xs : List (Inside N m)) :
      (sumPayload (xs.map fun b => glueCharge N m b.picks.length)).keyMapCells = 0 := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa [sumPayload, PayloadStats.add, glueCharge] using ih
  unfold nodeR
  apply mapBound_stats_left
  apply mapBound_add
  · apply mapBound_sum
    intro r hr
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hr
    exact mapBound_add (insideR_mapBound _ _ _) (by simp [MapBound, hz])
  · exact dedupResource_mapBound _ _

theorem computeR_mapBound (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (v : Fin N) :
    MapBound (computeR R H w m v).keyStats (computeR R H w m v).payload := by
  rw [computeR]
  apply mapBound_stats_left
  apply mapBound_add
  · apply mapBound_sum
    intro r hr
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hr
    exact computeR_mapBound R H w m u.val
  · exact nodeR_mapBound _ _ _ _ _ _
termination_by R.rank v
decreasing_by exact R.child_rank ((mem_childrenList _ _ _).mp u.property)

theorem rootsR_mapBound (ts : List (List (Entry N m))) :
    MapBound (rootsR ts).keyStats (rootsR ts).payload := by
  induction ts with
  | nil => exact mapBound_zero _
  | cons t ts ih =>
    exact mapBound_add ih (mapBound_add (by simp [MapBound]) (dedupResource_mapBound _ _))

theorem solveR_mapBound (R : RootedTree (Fin N)) (H : Fin N → ℕ) (w : Fin N → ℤ)
    (m : ℕ) (B : ℤ) : MapBound (solveR R H w m B).keyStats (solveR R H w m B).payload := by
  have hf (r : Option (Root N m)) : (finishR R r).2.keyMapCells = 0 := by
    cases r <;> rfl
  unfold solveR
  apply mapBound_add
  · apply mapBound_sum
    intro r hr
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
    exact computeR_mapBound _ _ _ _ _
  · exact mapBound_add (rootsR_mapBound _) (by simp [MapBound, hf])

theorem solveAutoR_keyMapCells_le (R : RootedTree (Fin N)) (H : Fin N → ℕ)
    (s : Fin N → ℚ) (m U : ℕ) (T : ℚ) (hU : ∀ v, v ≠ R.root → H v ≤ U) :
    (solveAutoR R H s m T).payload.keyMapCells ≤
      (N - 1) * globalProduct R H m * (globalProduct R H m - 1) := by
  have h := solveR_mapBound R H
    (val (TreeBudgetSubtreeAutoScaleSeed.prepare R s T).weight) m
    (TreeBudgetSubtreeAutoScaleSeed.prepare R s T).budget
  change MapBound (solveAutoR R H s m T).keyStats _ at h
  unfold MapBound at h
  rw [solveAutoR_keyStats] at h
  have hb := (checkCompactStats_bounds R H s m U T hU).1
  have hi : (checkCompactStats R H s m T).stats.dedupInput ≤
      2 * (N - 1) * globalProduct R H m := hb.2.2.2.2.2.2.2.2.2.2.2.1
  have hm : (checkCompactStats R H s m T).stats.maxRawTable ≤ globalProduct R H m :=
    hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hh := Nat.mul_le_mul hi (Nat.sub_le_sub_right hm 1)
  change (solveR R H (val (TreeBudgetSubtreeAutoScaleSeed.prepare R s T).weight) m
    (TreeBudgetSubtreeAutoScaleSeed.prepare R s T).budget).payload.keyMapCells ≤ _
  nlinarith

end UAVProof.TreeBudgetSubtreeResourceSeed
