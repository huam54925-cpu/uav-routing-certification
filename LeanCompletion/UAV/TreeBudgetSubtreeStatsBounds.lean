import LeanCompletion.UAV.TreeBudgetSubtreeTableBounds

/-! Logical work envelopes for the actual profiles. Comparisons are charged
twice to retain the triangular deduplication bound without rounding. -/
namespace UAVProof.TreeBudgetSubtreeStats
open TreeBudgetSubtreeExecutable TreeFlowExistence TreeBudgetSubtreeState
variable {m N : ℕ}

def logicalWork (s : DPStats) : ℕ := s.nodeCalls + s.compositionCalls + s.rangeChoices +
  s.columnsGenerated + s.columnsAccepted + s.subsetCalls + s.insidePairs + s.rootPairs +
  s.rootRejected + s.ratAdds + s.ratMuls + s.dedupInput + s.dedupOutput + s.eqCalls + s.acceptCalls

def Covers (s b : DPStats) : Prop :=
  s.nodeCalls ≤ b.nodeCalls ∧ s.compositionCalls ≤ b.compositionCalls ∧
  s.rangeChoices ≤ b.rangeChoices ∧ s.columnsGenerated ≤ b.columnsGenerated ∧
  s.columnsAccepted ≤ b.columnsAccepted ∧ s.subsetCalls ≤ b.subsetCalls ∧
  s.insidePairs ≤ b.insidePairs ∧ s.rootPairs ≤ b.rootPairs ∧ s.rootRejected ≤ b.rootRejected ∧
  s.ratAdds ≤ b.ratAdds ∧ s.ratMuls ≤ b.ratMuls ∧ s.dedupInput ≤ b.dedupInput ∧
  s.dedupOutput ≤ b.dedupOutput ∧ 2 * s.eqCalls ≤ b.eqCalls ∧ s.acceptCalls ≤ b.acceptCalls ∧
  s.maxRawTable ≤ b.maxRawTable ∧ s.maxDedupTable ≤ b.maxDedupTable

theorem covers_add {s t b c : DPStats} (hs : Covers s b) (ht : Covers t c) :
    Covers (s.add t) (b.add c) := by
  simp only [Covers, DPStats.add] at *
  omega

theorem covers_mono {s b c : DPStats} (hs : Covers s b)
    (hbc : ∀ t, Covers t b → Covers t c) : Covers s c := hbc s hs

def dedupEnvelope (B : ℕ) : DPStats :=
  { dedupInput := B, dedupOutput := B, eqCalls := B ^ 2, maxRawTable := B, maxDedupTable := B }

theorem dedupProfile_bounds {α : Type} [DecidableEq α] (xs : List α) (B : ℕ)
    (h : xs.length ≤ B) : Covers (dedupProfile xs) (dedupEnvelope B) := by
  have hd := (List.dedup_sublist xs).length_le
  have he := dedupComparisons_bound xs
  have hs : 2 * dedupComparisons xs ≤ B ^ 2 := by
    have ht : xs.length * (xs.length - 1) ≤ xs.length * xs.length :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have hb : xs.length * xs.length ≤ B * B := Nat.mul_le_mul h h
    nlinarith
  simp only [Covers, dedupProfile, dedupEnvelope]
  omega

def safeProduct (ts : List (List (ExecCompactState m))) : ℕ :=
  (ts.map fun t => max 1 t.length).prod

theorem safeProduct_pos (ts : List (List (ExecCompactState m))) : 1 ≤ safeProduct ts := by
  induction ts with
  | nil => simp [safeProduct]
  | cons t ts ih =>
    change 1 ≤ max 1 t.length * safeProduct ts
    nlinarith [le_max_left 1 t.length]

theorem tableProduct_le_safeProduct (ts : List (List (ExecCompactState m))) :
    tableProduct ts ≤ safeProduct ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact Nat.mul_le_mul (le_max_right _ _) ih

def insideEnvelope (m k B : ℕ) : DPStats :=
  { subsetCalls := k * B, insidePairs := k * B, ratAdds := m * (k * B),
    dedupInput := k * B, dedupOutput := k * B, eqCalls := k * B ^ 2,
    maxRawTable := B, maxDedupTable := B }

theorem insideProfile_bounds (a : Vector Bool m) (base : Vector ℚ m)
    (ts : List (List (ExecCompactState m))) :
    Covers (insideProfile a base ts) (insideEnvelope m ts.length (safeProduct ts)) := by
  induction ts with
  | nil => simp [insideProfile, insideEnvelope, safeProduct, Covers]
  | cons t ts ih =>
    let B := safeProduct (t :: ts)
    have hp := safeProduct_pos ts
    have hb : safeProduct ts ≤ B := by
      dsimp [B, safeProduct]
      exact Nat.le_mul_of_pos_left _ (by omega)
    have ht : t.length ≤ B := by
      change t.length ≤ max 1 t.length * safeProduct ts
      nlinarith [le_max_right 1 t.length]
    have hr : (insideRaw a t (insideCosts a base ts)).length ≤ B :=
      (insideRaw_length_le a base t ts).trans (tableProduct_le_safeProduct (t :: ts))
    have hd := dedupProfile_bounds (insideRaw a t (insideCosts a base ts)) B hr
    have hi : Covers (insideProfile a base ts) (insideEnvelope m ts.length B) := by
      have hmul := Nat.mul_le_mul_left ts.length hb
      have hadd := Nat.mul_le_mul_left m hmul
      have heq := Nat.mul_le_mul_left ts.length (Nat.pow_le_pow_left hb 2)
      simp only [Covers, insideEnvelope] at ih ⊢
      omega
    have hstep : Covers (insideStep m t.length (insideRaw a t (insideCosts a base ts)).length)
        { subsetCalls := B, insidePairs := B, ratAdds := m * B } := by
      have ha := Nat.mul_le_mul_left m hr
      simp only [Covers, insideStep]
      omega
    have hh := covers_add hi (covers_add hstep hd)
    rw [insideProfile]
    rw [← insideRaw_length]
    have he : (insideEnvelope m ts.length B).add
        (({ subsetCalls := B, insidePairs := B, ratAdds := m * B } : DPStats).add
          (dedupEnvelope B)) = insideEnvelope m (t :: ts).length B := by
      simp only [insideEnvelope, dedupEnvelope, DPStats.add, List.length_cons]
      congr 1 <;> simp <;> ring
    rw [he] at hh
    exact hh

def rootEnvelope (m k B : ℕ) : DPStats :=
  { rootPairs := k * B, rootRejected := k * B, ratAdds := m * (k * B),
    dedupInput := k * B, dedupOutput := k * B, eqCalls := k * B ^ 2,
    maxRawTable := B, maxDedupTable := B }

theorem rootProfile_bounds (ts : List (List (ExecCompactState m))) :
    Covers (rootProfile ts) (rootEnvelope m ts.length (safeProduct ts)) := by
  induction ts with
  | nil => simp [rootProfile, rootEnvelope, safeProduct, Covers]
  | cons t ts ih =>
    let B := safeProduct (t :: ts)
    have hb : safeProduct ts ≤ B := by
      dsimp [B, safeProduct]
      exact Nat.le_mul_of_pos_left _ (by omega)
    have hr : (rootRaw t (rootFold ts)).length ≤ B :=
      (rootRaw_length_le t ts).trans (tableProduct_le_safeProduct (t :: ts))
    have hk : ((rootRaw t (rootFold ts)).filter rootCapB).length ≤ B :=
      (List.length_filter_le _ _).trans hr
    have hd := dedupProfile_bounds ((rootRaw t (rootFold ts)).filter rootCapB) B hk
    have hi : Covers (rootProfile ts) (rootEnvelope m ts.length B) := by
      have hmul := Nat.mul_le_mul_left ts.length hb
      have hadd := Nat.mul_le_mul_left m hmul
      have heq := Nat.mul_le_mul_left ts.length (Nat.pow_le_pow_left hb 2)
      simp only [Covers, rootEnvelope] at ih ⊢
      omega
    have hstep : Covers (rootStep m (rootRaw t (rootFold ts)).length
        ((rootRaw t (rootFold ts)).filter rootCapB).length)
        { rootPairs := B, rootRejected := B, ratAdds := m * B, maxRawTable := B } := by
      have ha := Nat.mul_le_mul_left m hr
      simp only [Covers, rootStep]
      omega
    have hh := covers_add hi (covers_add hstep hd)
    rw [rootProfile, ← rootRaw_length]
    have he : (rootEnvelope m ts.length B).add
        (({ rootPairs := B, rootRejected := B, ratAdds := m * B, maxRawTable := B } : DPStats).add
          (dedupEnvelope B)) =
        rootEnvelope m (t :: ts).length B := by
      simp only [rootEnvelope, dedupEnvelope, DPStats.add, List.length_cons]
      congr 1 <;> simp <;> ring
    rw [he] at hh
    exact hh

end UAVProof.TreeBudgetSubtreeStats
