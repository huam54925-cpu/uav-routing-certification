import LeanCompletion.UAV.TreeBudgetSubtreeScalarVectors

namespace UAVProof.TreeBudgetSubtreeScalar
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats TreeFlowExistence

def compositionsC : (m : Nat) → Nat → Counted (Measured (List (Vector Nat m)))
  | 0, h => ⟨⟨if h = 0 then [emptyV] else [], { compositionCalls := 1 }⟩, 4⟩
  | m+1, h =>
    let rs := (List.range (h+1)).map fun a =>
      let r := compositionsC m (h-a)
      let c := mapC (consC a) r.value.value
      (⟨⟨c.value, r.value.stats⟩, r.ops + c.ops + 1⟩ :
        Counted (Measured (List (Vector Nat (m+1)))))
    let flat := flatMapC (fun r => ⟨r.value.value, 1⟩) rs
    ⟨⟨flat.value, ({ compositionCalls := 1, rangeChoices := h+1 } : DPStats).add
      (sumStats (rs.map fun r => r.value.stats))⟩,
      (rs.map Counted.ops).sum + flat.ops + 6*(h+1)+4⟩

@[simp] theorem compositionsC_value (m h : Nat) :
    (compositionsC m h).value = compositionsStats m h := by
  induction m generalizing h with
  | zero => rfl
  | succ m ih =>
    simp [compositionsC, compositionsStats, ih, List.map_map, List.flatMap_map, Function.comp_def]

def candidateCapC {N m : Nat} (R : RootedTree (Fin N)) (v : Fin N)
    (q : Vector Nat m) : Counted Bool :=
  if R.parent v = R.root then
    let r := allC (fun i => ⟨decide (val q i ≤ 1), 2⟩) (List.finRange m)
    ⟨r.value, r.ops + 2*m+4⟩
  else ⟨true, 3⟩

@[simp] theorem candidateCapC_value {N m : Nat} (R : RootedTree (Fin N)) (v : Fin N)
    (q : Vector Nat m) :
    (candidateCapC R v q).value = decide (R.parent v = R.root → ∀ i, val q i ≤ 1) := by
  by_cases h : R.parent v = R.root
  · apply Bool.eq_iff_iff.mpr
    simp [candidateCapC, h]
  · simp [candidateCapC, h]

theorem candidateCapC_bound {N m : Nat} (R : RootedTree (Fin N)) (v : Fin N)
    (q : Vector Nat m) : (candidateCapC R v q).ops ≤ 7*m+5 := by
  have hh := allC_bound (fun i => (⟨decide (val q i ≤ 1), 2⟩ : Counted Bool))
    (List.finRange m) 2 (by simp)
  simp only [List.length_finRange] at hh
  unfold candidateCapC
  split <;> dsimp only <;> omega

def candidatesC {N : Nat} (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (m : Nat) (v : Fin N) : Counted (Measured (List (Vector Nat m))) :=
  let r := compositionsC m (H v)
  let qs := filterC (candidateCapC R v) r.value.value
  ⟨⟨qs.value, r.value.stats.add
    { columnsGenerated := r.value.value.length, columnsAccepted := qs.value.length }⟩,
    r.ops + qs.ops + 3⟩

@[simp] theorem candidatesC_value {N : Nat} (R : RootedTree (Fin N)) (H : Fin N → Nat)
    (m : Nat) (v : Fin N) : (candidatesC R H m v).value = localCandidatesStats R H m v := by
  simp [candidatesC, localCandidatesStats]

end UAVProof.TreeBudgetSubtreeScalar
