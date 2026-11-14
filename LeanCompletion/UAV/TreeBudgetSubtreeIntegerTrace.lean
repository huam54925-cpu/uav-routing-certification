import LeanCompletion.UAV.TreeBudgetSubtreeIntegerStats

/-! Equality outcomes in execution order: tail deduplication first, then the
short-circuit membership scan. This is a logical trace, not a bit-cost model. -/
namespace UAVProof.TreeBudgetSubtreeInteger
open TreeBudgetSubtreeStats

def scanTrace {α : Type} [DecidableEq α] (x : α) : List α → List Bool
  | [] => []
  | y :: ys => decide (x = y) :: if x = y then [] else scanTrace x ys

def dedupTrace {α : Type} [DecidableEq α] : List α → List Bool
  | [] => []
  | x :: xs => dedupTrace xs ++ scanTrace x xs.dedup

theorem scanTrace_length {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    (scanTrace x xs).length = scanComparisons x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => by_cases h : x = y <;> simp [scanTrace, scanComparisons, h, ih, Nat.add_comm]

theorem dedupTrace_length {α : Type} [DecidableEq α] (xs : List α) :
    (dedupTrace xs).length = dedupComparisons xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [dedupTrace, dedupComparisons, scanTrace_length, ih]

theorem scanTrace_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (x : α) (xs : List α) :
    scanTrace (f x) (xs.map f) = scanTrace x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp [scanTrace, hf.eq_iff, ih]

theorem dedupTrace_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) :
    dedupTrace (xs.map f) = dedupTrace xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [dedupTrace, List.dedup_map_of_injective hf, scanTrace_map f hf, ih]

theorem dedupTrace_liftCost {m D : ℕ} (hD : 0 < D) (xs : List (Vector ℤ m)) :
    dedupTrace (xs.map (liftCost D)) = dedupTrace xs :=
  dedupTrace_map _ (liftCost_injective hD) xs

theorem dedupTrace_liftState {m D : ℕ} (hD : 0 < D) (xs : List (IntState m)) :
    dedupTrace (xs.map (liftState D)) = dedupTrace xs :=
  dedupTrace_map _ (liftState_injective hD) xs

theorem dedupTrace_liftRoot {m D : ℕ} (hD : 0 < D) (xs : List (IntRoot m)) :
    dedupTrace (xs.map (liftRoot D)) = dedupTrace xs :=
  dedupTrace_map _ (liftRoot_injective hD) xs

end UAVProof.TreeBudgetSubtreeInteger
