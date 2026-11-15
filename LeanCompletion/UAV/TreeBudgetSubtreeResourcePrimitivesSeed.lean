import LeanCompletion.UAV.TreeBudgetSubtreeIntegerWitnessSeed
import LeanCompletion.UAV.TreeBudgetSubtreeStatsPrimitives

/-!
Resource primitives adapted from the supplied 2026-11-15 seed package.
Baseline: 58d54620aa8634238409bf6c6e98a91db40c670a, Lean v4.30.0-rc2.
These are source-level charges. They do not measure compiled allocations,
reference-counting, garbage collection, or the cost of maintaining counters.
-/
namespace UAVProof.TreeBudgetSubtreeResourceSeed
open TreeBudgetSubtreeStats

structure PayloadStats where
  matrices : Nat := 0
  matrixCells : Nat := 0
  childReads : Nat := 0
  natAdds : Nat := 0
  tempCells : Nat := 0
  columnReads : Nat := 0
  pickCons : Nat := 0
  keyMapCells : Nat := 0
  rootZeroCells : Nat := 0
  deriving DecidableEq, Repr, Inhabited

def PayloadStats.add (a b : PayloadStats) : PayloadStats :=
  ⟨a.matrices + b.matrices, a.matrixCells + b.matrixCells,
   a.childReads + b.childReads, a.natAdds + b.natAdds,
   a.tempCells + b.tempCells, a.columnReads + b.columnReads,
   a.pickCons + b.pickCons, a.keyMapCells + b.keyMapCells,
   a.rootZeroCells + b.rootZeroCells⟩

def PayloadStats.work (p : PayloadStats) : Nat :=
  p.matrices + p.matrixCells + p.childReads + p.natAdds + p.tempCells +
    p.columnReads + p.pickCons + p.keyMapCells + p.rootZeroCells

@[simp] theorem PayloadStats.zero_add (p : PayloadStats) : ({} : PayloadStats).add p = p := by
  cases p
  simp [PayloadStats.add]

@[simp] theorem PayloadStats.add_zero (p : PayloadStats) : p.add {} = p := by
  cases p
  simp [PayloadStats.add]

def sumPayload : List PayloadStats → PayloadStats
  | [] => {}
  | p :: ps => p.add (sumPayload ps)

structure ResourceResult (α : Type) where
  value : α
  keyStats : DPStats
  payload : PayloadStats

structure DedupTrace (α : Type) where
  value : List α
  comparisons : Nat
  keyMapCells : Nat

/-- One traversal: preserve rightmost payloads and charge the whole key map
before the short-circuit membership scan. -/
def dedupKeyCounted {α κ : Type} [DecidableEq κ] (key : α → κ) :
    List α → DedupTrace α
  | [] => ⟨[], 0, 0⟩
  | x :: xs =>
    let r := dedupKeyCounted key xs
    let keys := r.value.map key
    let hit := memberCounted (key x) keys
    ⟨if hit.1 then r.value else x :: r.value,
      r.comparisons + hit.2, r.keyMapCells + keys.length⟩

@[simp] theorem dedupKeyCounted_erase {α κ : Type} [DecidableEq κ]
    (key : α → κ) (xs : List α) :
    (dedupKeyCounted key xs).value = TreeBudgetSubtreeWitness.dedupKey key xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [dedupKeyCounted, TreeBudgetSubtreeWitness.dedupKey,
      memberCounted_erase, ih]

theorem dedupKeyCounted_comparisons {α κ : Type} [DecidableEq κ]
    (key : α → κ) (xs : List α) :
    (dedupKeyCounted key xs).comparisons = dedupComparisons (xs.map key) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [dedupKeyCounted, dedupComparisons, ih, memberCounted_count,
      TreeBudgetSubtreeWitness.dedupKey_map]

def keyMapSpec {α κ : Type} [DecidableEq κ] (key : α → κ) : List α → Nat
  | [] => 0
  | _ :: xs => keyMapSpec key xs + (TreeBudgetSubtreeWitness.dedupKey key xs).length

@[simp] theorem dedupKeyCounted_keyMapCells {α κ : Type} [DecidableEq κ]
    (key : α → κ) (xs : List α) :
    (dedupKeyCounted key xs).keyMapCells = keyMapSpec key xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [dedupKeyCounted, keyMapSpec, ih]

theorem dedupKey_length_le {α κ : Type} [DecidableEq κ]
    (key : α → κ) (xs : List α) :
    (TreeBudgetSubtreeWitness.dedupKey key xs).length ≤ xs.length := by
  have h := (List.dedup_sublist (xs.map key)).length_le
  rw [← TreeBudgetSubtreeWitness.dedupKey_map key xs] at h
  simpa only [List.length_map] using h

theorem comparisons_le_keyMapCells {α κ : Type} [DecidableEq κ]
    (key : α → κ) (xs : List α) :
    (dedupKeyCounted key xs).comparisons ≤ (dedupKeyCounted key xs).keyMapCells := by
  induction xs with
  | nil => simp [dedupKeyCounted]
  | cons x xs ih =>
    have h := scanComparisons_le (key x) ((dedupKeyCounted key xs).value.map key)
    simpa only [dedupKeyCounted, memberCounted_count] using Nat.add_le_add ih h

theorem keyMapSpec_triangle {α κ : Type} [DecidableEq κ]
    (key : α → κ) (xs : List α) :
    2 * keyMapSpec key xs ≤ xs.length * (xs.length - 1) := by
  induction xs with
  | nil => simp [keyMapSpec]
  | cons x xs ih =>
    have hs := dedupKey_length_le key xs
    have hpoly : xs.length * (xs.length - 1) + 2 * xs.length =
        (xs.length + 1) * xs.length := by
      cases xs.length with
      | zero => simp
      | succ n => simp; ring
    simp only [keyMapSpec, List.length_cons, Nat.add_sub_cancel]
    omega

def dedupResource {α κ : Type} [DecidableEq κ] (key : α → κ)
    (xs : List α) : ResourceResult (List α) :=
  let r := dedupKeyCounted key xs
  ⟨r.value,
   { dedupInput := xs.length, dedupOutput := r.value.length,
     eqCalls := r.comparisons, maxRawTable := xs.length,
     maxDedupTable := r.value.length },
   { keyMapCells := r.keyMapCells }⟩

@[simp] theorem dedupResource_erase {α κ : Type} [DecidableEq κ]
    (key : α → κ) (xs : List α) :
    (dedupResource key xs).value = TreeBudgetSubtreeWitness.dedupKey key xs := by
  simp [dedupResource]

/-- No injectivity of key is needed: equal keys may have different payloads. -/
theorem dedupResource_keyStats {α κ : Type} [DecidableEq κ]
    (key : α → κ) (xs : List α) :
    (dedupResource key xs).keyStats = dedupProfile (xs.map key) := by
  have hlen : (TreeBudgetSubtreeWitness.dedupKey key xs).length =
      (xs.map key).dedup.length := by
    simpa only [List.length_map] using
      congrArg List.length (TreeBudgetSubtreeWitness.dedupKey_map key xs)
  simp [dedupResource, dedupProfile, dedupKeyCounted_comparisons, hlen]

/-- Unlike anyCounted, this returns the selected representative itself. -/
def findCounted {α : Type} (p : α → Bool) : List α → Option α × Nat
  | [] => (none, 0)
  | x :: xs => if p x then (some x, 1) else
    let r := findCounted p xs
    (r.1, r.2 + 1)

theorem findCounted_spec {α : Type} (p : α → Bool) (xs : List α) :
    (findCounted p xs).1 = xs.find? p ∧
    (findCounted p xs).2 = acceptComparisons p xs := by
  induction xs with
  | nil => simp [findCounted, acceptComparisons]
  | cons x xs ih =>
    cases hx : p x <;>
      simp [findCounted, List.find?, acceptComparisons, hx, ih, Nat.add_comm]

theorem findCounted_count_eq_any {α : Type} (p : α → Bool) (xs : List α) :
    (findCounted p xs).2 = (anyCounted p xs).2 :=
  (findCounted_spec p xs).2.trans (anyCounted_spec p xs).2.symm

example : (dedupKeyCounted Prod.fst [(0, 3), (1, 5), (0, 7)]).value =
    [(1, 5), (0, 7)] := by decide +kernel

example : (findCounted (fun n : Nat => decide (2 ≤ n)) [0, 2, 3]) =
    (some 2, 2) := by decide +kernel

#print axioms dedupKeyCounted_erase
#print axioms dedupKeyCounted_comparisons
#print axioms comparisons_le_keyMapCells
#print axioms keyMapSpec_triangle
#print axioms dedupResource_keyStats
#print axioms findCounted_spec
end UAVProof.TreeBudgetSubtreeResourceSeed
