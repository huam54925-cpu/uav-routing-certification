import LeanCompletion.UAV.TreeBudgetSubtreeScalarPrimitives

namespace UAVProof.TreeBudgetSubtreeScalar
open TreeBudgetSubtreeStats TreeBudgetSubtreeResourceSeed

def memberC {κ : Type} (eq : κ → κ → Counted Bool) (x : κ) :
    List κ → Counted (Bool × Nat)
  | [] => ⟨(false, 0), 1⟩
  | y :: ys => let c := eq x y
              if c.value then ⟨(true, 1), c.ops + 4⟩
              else let r := memberC eq x ys
                   ⟨(r.value.1, r.value.2 + 1), c.ops + r.ops + 4⟩

@[simp] theorem memberC_value {κ : Type} [DecidableEq κ] (eq : κ → κ → Counted Bool)
    (he : ∀ x y, (eq x y).value = decide (x = y)) (x : κ) (xs : List κ) :
    (memberC eq x xs).value = memberCounted x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => by_cases h : x = y <;> simp [memberC, memberCounted, he, h, ih]

def memberWork {κ : Type} [DecidableEq κ] (c : κ → κ → Nat) (x : κ) : List κ → Nat
  | [] => 1
  | y :: ys => c x y + 4 + if x = y then 0 else memberWork c x ys

theorem memberC_ops {κ : Type} [DecidableEq κ] (eq : κ → κ → Counted Bool)
    (he : ∀ x y, (eq x y).value = decide (x = y)) (x : κ) (xs : List κ) :
    (memberC eq x xs).ops = memberWork (fun x y => (eq x y).ops) x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : x = y <;> simp [memberC, memberWork, he, h, ih] <;> omega

theorem memberC_bound {κ : Type} (eq : κ → κ → Counted Bool) (k : Nat)
    (hk : ∀ x y, (eq x y).ops ≤ k) (x : κ) (xs : List κ) :
    (memberC eq x xs).ops ≤ (k + 4) * (memberC eq x xs).value.2 + 1 := by
  induction xs with
  | nil => simp [memberC]
  | cons y ys ih =>
    have h := hk x y
    simp only [memberC]
    split <;> dsimp only <;> nlinarith

/-- The entire tail key map is evaluated before the short-circuit scan. -/
def dedupTraceC {α κ : Type} (key : α → κ) (eq : κ → κ → Counted Bool) :
    List α → Counted (DedupTrace α)
  | [] => ⟨⟨[], 0, 0⟩, 1⟩
  | x :: xs =>
    let r := dedupTraceC key eq xs
    let keys := mapC (fun y => ⟨key y, 1⟩) r.value.value
    let hit := memberC eq (key x) keys.value
    ⟨⟨if hit.value.1 then r.value.value else x :: r.value.value,
      r.value.comparisons + hit.value.2, r.value.keyMapCells + keys.value.length⟩,
      r.ops + keys.ops + hit.ops + 7⟩

@[simp] theorem dedupTraceC_value {α κ : Type} [DecidableEq κ] (key : α → κ)
    (eq : κ → κ → Counted Bool) (he : ∀ x y, (eq x y).value = decide (x = y))
    (xs : List α) : (dedupTraceC key eq xs).value = dedupKeyCounted key xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [dedupTraceC, dedupKeyCounted, ih, memberC_value eq he]

def dedupWork {α κ : Type} [DecidableEq κ] (key : α → κ) (c : κ → κ → Nat) :
    List α → Nat
  | [] => 1
  | x :: xs =>
    let tail := TreeBudgetSubtreeWitness.dedupKey key xs
    dedupWork key c xs + (4 * tail.length + 1) + memberWork c (key x) (tail.map key) + 7

theorem dedupTraceC_ops {α κ : Type} [DecidableEq κ] (key : α → κ)
    (eq : κ → κ → Counted Bool) (he : ∀ x y, (eq x y).value = decide (x = y))
    (xs : List α) :
    (dedupTraceC key eq xs).ops = dedupWork key (fun x y => (eq x y).ops) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [dedupTraceC, dedupWork, ih, dedupTraceC_value key eq he,
      memberC_ops eq he, mapWork_eq]
    omega

theorem dedupTraceC_bound {α κ : Type} (key : α → κ) (eq : κ → κ → Counted Bool)
    (k : Nat) (hk : ∀ x y, (eq x y).ops ≤ k) (xs : List α) :
    (dedupTraceC key eq xs).ops ≤ 10 * xs.length +
      4 * (dedupTraceC key eq xs).value.keyMapCells +
      (k + 4) * (dedupTraceC key eq xs).value.comparisons + 1 := by
  induction xs with
  | nil => simp [dedupTraceC]
  | cons x xs ih =>
    have hm := memberC_bound eq k hk (key x)
      (mapC (fun y => ⟨key y, 1⟩) (dedupTraceC key eq xs).value.value).value
    simp only [dedupTraceC, mapC_ops, mapC_value, mapWork_eq,
      List.length_cons, List.length_map] at *
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] at *
    nlinarith

def dedupC {α κ : Type} (key : α → κ) (eq : κ → κ → Counted Bool)
    (xs : List α) : Counted (ResourceResult (List α)) :=
  let r := dedupTraceC key eq xs
  ⟨⟨r.value.value,
    { dedupInput := xs.length, dedupOutput := r.value.value.length,
      eqCalls := r.value.comparisons, maxRawTable := xs.length,
      maxDedupTable := r.value.value.length }, { keyMapCells := r.value.keyMapCells }⟩,
    r.ops + 2⟩

@[simp] theorem dedupC_value {α κ : Type} [DecidableEq κ] (key : α → κ)
    (eq : κ → κ → Counted Bool) (he : ∀ x y, (eq x y).value = decide (x = y))
    (xs : List α) : (dedupC key eq xs).value = dedupResource key xs := by
  simp [dedupC, dedupResource, dedupTraceC_value key eq he]

theorem dedupC_bound {α κ : Type} (key : α → κ) (eq : κ → κ → Counted Bool)
    (k : Nat) (hk : ∀ x y, (eq x y).ops ≤ k) (xs : List α) :
    (dedupC key eq xs).ops ≤ (k + 14) *
      (1 + (dedupC key eq xs).value.keyStats.dedupInput +
        (dedupC key eq xs).value.keyStats.eqCalls +
        (dedupC key eq xs).value.payload.keyMapCells) := by
  have h := dedupTraceC_bound key eq k hk xs
  dsimp only [dedupC]
  nlinarith

end UAVProof.TreeBudgetSubtreeScalar
