import LeanCompletion.UAV.TreeBudgetSubtreeDP

/-! Logical operation counts, not machine steps. Maxima describe single lists,
not live memory. Equality counts are whole-element decisions, with short circuit. -/
namespace UAVProof.TreeBudgetSubtreeStats
open TreeBudgetSubtreeExecutable

structure DPStats where
  nodeCalls : Nat := 0
  compositionCalls : Nat := 0
  rangeChoices : Nat := 0
  columnsGenerated : Nat := 0
  columnsAccepted : Nat := 0
  subsetCalls : Nat := 0
  insidePairs : Nat := 0
  rootPairs : Nat := 0
  rootRejected : Nat := 0
  ratAdds : Nat := 0
  ratMuls : Nat := 0
  dedupInput : Nat := 0
  dedupOutput : Nat := 0
  eqCalls : Nat := 0
  acceptCalls : Nat := 0
  maxRawTable : Nat := 0
  maxDedupTable : Nat := 0
  deriving DecidableEq, Repr, Inhabited

def DPStats.add (a b : DPStats) : DPStats :=
  ⟨a.nodeCalls + b.nodeCalls, a.compositionCalls + b.compositionCalls,
   a.rangeChoices + b.rangeChoices, a.columnsGenerated + b.columnsGenerated,
   a.columnsAccepted + b.columnsAccepted, a.subsetCalls + b.subsetCalls,
   a.insidePairs + b.insidePairs, a.rootPairs + b.rootPairs,
   a.rootRejected + b.rootRejected, a.ratAdds + b.ratAdds, a.ratMuls + b.ratMuls,
   a.dedupInput + b.dedupInput, a.dedupOutput + b.dedupOutput, a.eqCalls + b.eqCalls,
   a.acceptCalls + b.acceptCalls, max a.maxRawTable b.maxRawTable,
   max a.maxDedupTable b.maxDedupTable⟩

def sumStats : List DPStats → DPStats
  | [] => {}
  | s :: ss => s.add (sumStats ss)

structure Measured (α : Type) where
  value : α
  stats : DPStats

def collect {α : Type} (xs : List (Measured α)) : Measured (List α) :=
  ⟨xs.map Measured.value, sumStats (xs.map Measured.stats)⟩

def memberCounted {α : Type} [DecidableEq α] (x : α) : List α → Bool × Nat
  | [] => (false, 0)
  | y :: ys => if x = y then (true, 1) else
      let r := memberCounted x ys
      (r.1, r.2 + 1)

/-- Independent scan specification: includes the successful comparison. -/
def scanComparisons {α : Type} [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | y :: ys => if x = y then 1 else 1 + scanComparisons x ys

theorem memberCounted_erase {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    (memberCounted x xs).1 = decide (x ∈ xs) := by
  induction xs with
  | nil => rfl
  | cons y ys ih => by_cases h : x = y <;> simp [memberCounted, h, ih]

theorem memberCounted_count {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    (memberCounted x xs).2 = scanComparisons x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : x = y <;> simp [memberCounted, scanComparisons, h, ih, Nat.add_comm]

theorem scanComparisons_le {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    scanComparisons x xs ≤ xs.length := by
  induction xs with
  | nil => simp [scanComparisons]
  | cons y ys ih => simp only [scanComparisons, List.length_cons]; split <;> omega

def dedupCounted {α : Type} [DecidableEq α] : List α → List α × Nat
  | [] => ([], 0)
  | x :: xs =>
      let r := dedupCounted xs
      let found := memberCounted x r.1
      (if found.1 then r.1 else x :: r.1, r.2 + found.2)

/-- Cost recurrence uses the ordinary deduplicated tail, independently of the
instrumented executor. Deletions are deliberately not used as comparisons. -/
def dedupComparisons {α : Type} [DecidableEq α] : List α → Nat
  | [] => 0
  | x :: xs => dedupComparisons xs + scanComparisons x xs.dedup

theorem dedupCounted_erase {α : Type} [DecidableEq α] (xs : List α) :
    (dedupCounted xs).1 = xs.dedup := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [dedupCounted, memberCounted_erase, ih, List.dedup_cons']

theorem dedupCounted_count {α : Type} [DecidableEq α] (xs : List α) :
    (dedupCounted xs).2 = dedupComparisons xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [dedupCounted, dedupComparisons, ih,
      memberCounted_count, dedupCounted_erase]

theorem dedupComparisons_bound {α : Type} [DecidableEq α] (xs : List α) :
    2 * dedupComparisons xs ≤ xs.length * (xs.length - 1) := by
  induction xs with
  | nil => simp [dedupComparisons]
  | cons x xs ih =>
    have hs := (scanComparisons_le x xs.dedup).trans (List.dedup_sublist xs).length_le
    simp only [dedupComparisons, List.length_cons, Nat.add_sub_cancel]
    have h : xs.length * (xs.length - 1) + 2 * xs.length =
        (xs.length + 1) * xs.length := by
      cases xs.length with
      | zero => simp
      | succ n => simp; ring
    omega

def dedupProfile {α : Type} [DecidableEq α] (xs : List α) : DPStats :=
  { dedupInput := xs.length, dedupOutput := xs.dedup.length,
    eqCalls := dedupComparisons xs, maxRawTable := xs.length,
    maxDedupTable := xs.dedup.length }

def dedupStats {α : Type} [DecidableEq α] (xs : List α) : Measured (List α) :=
  let r := dedupCounted xs
  ⟨r.1, { dedupInput := xs.length, dedupOutput := r.1.length,
          eqCalls := r.2, maxRawTable := xs.length, maxDedupTable := r.1.length }⟩

@[simp] theorem dedupStats_erase {α : Type} [DecidableEq α] (xs : List α) :
    (dedupStats xs).value = xs.dedup := dedupCounted_erase xs

@[simp] theorem dedupStats_count {α : Type} [DecidableEq α] (xs : List α) :
    (dedupStats xs).stats = dedupProfile xs := by
  simp [dedupStats, dedupProfile, dedupCounted_erase, dedupCounted_count]

def anyCounted {α : Type} (p : α → Bool) : List α → Bool × Nat
  | [] => (false, 0)
  | x :: xs => if p x then (true, 1) else
      let r := anyCounted p xs
      (r.1, r.2 + 1)

def acceptComparisons {α : Type} (p : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => if p x then 1 else 1 + acceptComparisons p xs

theorem anyCounted_spec {α : Type} (p : α → Bool) (xs : List α) :
    (anyCounted p xs).1 = xs.any p ∧
    (anyCounted p xs).2 = acceptComparisons p xs := by
  induction xs with
  | nil => simp [anyCounted, acceptComparisons]
  | cons x xs ih => cases hx : p x <;> simp [anyCounted, acceptComparisons, hx, ih, Nat.add_comm]

end UAVProof.TreeBudgetSubtreeStats
