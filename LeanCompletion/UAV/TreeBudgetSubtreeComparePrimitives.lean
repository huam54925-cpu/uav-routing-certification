import LeanCompletion.UAV.TreeBudgetSubtreeFull

/-! Explicit left-to-right coordinate scans. These are not a cost model for
Lean's derived array equality or its compiler replacements. Rat equality is
one normalized-rational equality decision, not multiplication or reduction. -/
namespace UAVProof.TreeBudgetSubtreeCompare
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats
variable {m : Nat}

def scan {α : Type} (p : α → Bool) : List α → Bool × Nat
  | [] => (true, 0)
  | i :: is => if p i then let r := scan p is; (r.1, 1 + r.2) else (false, 1)

def scanWork {α : Type} (p : α → Bool) : List α → Nat
  | [] => 0
  | i :: is => if p i then 1 + scanWork p is else 1

theorem scan_spec {α : Type} (p : α → Bool) (is : List α) :
    (scan p is).1 = is.all p ∧ (scan p is).2 = scanWork p is := by
  induction is with
  | nil => simp [scan, scanWork]
  | cons i is ih => cases h : p i <;> simp [scan, scanWork, h, ih]

def vectorEq {α : Type} [DecidableEq α] (x y : Vector α m) : Bool :=
  (List.finRange m).all fun i => decide (val x i = val y i)

def vectorScan {α : Type} [DecidableEq α] (x y : Vector α m) : Bool × Nat :=
  scan (fun i => decide (val x i = val y i)) (List.finRange m)

theorem vectorEq_correct {α : Type} [DecidableEq α] (x y : Vector α m) :
    vectorEq x y = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [vectorEq, List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]
  exact ⟨vector_ext, fun h i => by rw [h]⟩

@[simp] theorem vectorScan_value {α : Type} [DecidableEq α] (x y : Vector α m) :
    (vectorScan x y).1 = vectorEq x y := (scan_spec _ _).1

theorem vectorScan_count {α : Type} [DecidableEq α] (x y : Vector α m) :
    (vectorScan x y).2 = scanWork (fun i => decide (val x i = val y i)) (List.finRange m) :=
  (scan_spec _ _).2

structure CompareCounts where
  calls : Nat := 0
  keyVectorCalls : Nat := 0
  keyRejects : Nat := 0
  costVectorCalls : Nat := 0
  costRejects : Nat := 0
  equalStates : Nat := 0
  keyCoordinateChecks : Nat := 0
  ratCoordinateChecks : Nat := 0
  deriving DecidableEq, Repr, Inhabited

def CompareCounts.add (a b : CompareCounts) : CompareCounts :=
  ⟨a.calls + b.calls, a.keyVectorCalls + b.keyVectorCalls, a.keyRejects + b.keyRejects,
   a.costVectorCalls + b.costVectorCalls, a.costRejects + b.costRejects,
   a.equalStates + b.equalStates, a.keyCoordinateChecks + b.keyCoordinateChecks,
   a.ratCoordinateChecks + b.ratCoordinateChecks⟩

structure Compared (α : Type) where
  value : α
  counts : CompareCounts

def fieldsEq {α : Type} [DecidableEq α] (costFirst : Bool)
    (kx ky : Vector α m) (cx cy : Vector Rat m) : Bool :=
  if costFirst then vectorEq cx cy && vectorEq kx ky
  else vectorEq kx ky && vectorEq cx cy

def fieldsDetailed {α : Type} [DecidableEq α] (costFirst : Bool)
    (kx ky : Vector α m) (cx cy : Vector Rat m) : Compared Bool :=
  if costFirst then
    let c := vectorScan cx cy
    if c.1 then
      let k := vectorScan kx ky
      ⟨k.1, { calls := 1, keyVectorCalls := 1, keyRejects := if k.1 then 0 else 1,
              costVectorCalls := 1, equalStates := if k.1 then 1 else 0,
              keyCoordinateChecks := k.2, ratCoordinateChecks := c.2 }⟩
    else ⟨false, { calls := 1, costVectorCalls := 1, costRejects := 1,
                    ratCoordinateChecks := c.2 }⟩
  else
    let k := vectorScan kx ky
    if k.1 then
      let c := vectorScan cx cy
      ⟨c.1, { calls := 1, keyVectorCalls := 1, costVectorCalls := 1,
              costRejects := if c.1 then 0 else 1, equalStates := if c.1 then 1 else 0,
              keyCoordinateChecks := k.2, ratCoordinateChecks := c.2 }⟩
    else ⟨false, { calls := 1, keyVectorCalls := 1, keyRejects := 1,
                    keyCoordinateChecks := k.2 }⟩

theorem fieldsDetailed_value {α : Type} [DecidableEq α] (order : Bool)
    (kx ky : Vector α m) (cx cy : Vector Rat m) :
    (fieldsDetailed order kx ky cx cy).value = fieldsEq order kx ky cx cy := by
  cases order <;> cases hk : vectorEq kx ky <;> cases hc : vectorEq cx cy <;>
    simp [fieldsDetailed, fieldsEq, hk, hc]

theorem fieldsDetailed_calls {α : Type} [DecidableEq α] (order : Bool)
    (kx ky : Vector α m) (cx cy : Vector Rat m) :
    (fieldsDetailed order kx ky cx cy).counts.calls = 1 := by
  cases order <;> cases hk : vectorEq kx ky <;> cases hc : vectorEq cx cy <;>
    simp [fieldsDetailed, hk, hc]

theorem keyFirst_conservation {α : Type} [DecidableEq α]
    (kx ky : Vector α m) (cx cy : Vector Rat m) :
    let d := (fieldsDetailed false kx ky cx cy).counts
    d.calls = d.keyRejects + d.costVectorCalls ∧
      d.costVectorCalls = d.costRejects + d.equalStates := by
  cases hk : vectorEq kx ky <;> cases hc : vectorEq cx cy <;>
    simp [fieldsDetailed, hk, hc]

theorem costFirst_conservation {α : Type} [DecidableEq α]
    (kx ky : Vector α m) (cx cy : Vector Rat m) :
    let d := (fieldsDetailed true kx ky cx cy).counts
    d.calls = d.costRejects + d.keyVectorCalls ∧
      d.keyVectorCalls = d.keyRejects + d.equalStates := by
  cases hk : vectorEq kx ky <;> cases hc : vectorEq cx cy <;>
    simp [fieldsDetailed, hk, hc]

def compactEq (order : Bool) (x y : ExecCompactState m) : Bool :=
  fieldsEq order x.active y.active x.cost y.cost

def fullEq (order : Bool) (x y : ExecFullState m) : Bool :=
  fieldsEq order x.q y.q x.cost y.cost

theorem compactEq_correct (order : Bool) (x y : ExecCompactState m) :
    compactEq order x y = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  cases x; cases y; cases order <;>
    simp [compactEq, fieldsEq, vectorEq_correct, and_comm]

theorem fullEq_correct (order : Bool) (x y : ExecFullState m) :
    fullEq order x y = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  cases x; cases y; cases order <;>
    simp [fullEq, fieldsEq, vectorEq_correct, and_comm]

def compactEqDetailed (order : Bool) (x y : ExecCompactState m) : Compared Bool :=
  fieldsDetailed order x.active y.active x.cost y.cost

def fullEqDetailed (order : Bool) (x y : ExecFullState m) : Compared Bool :=
  fieldsDetailed order x.q y.q x.cost y.cost

@[simp] theorem compactEqDetailed_correct (order : Bool) (x y : ExecCompactState m) :
    (compactEqDetailed order x y).value = decide (x = y) :=
  (fieldsDetailed_value _ _ _ _ _).trans (compactEq_correct _ _ _)

@[simp] theorem fullEqDetailed_correct (order : Bool) (x y : ExecFullState m) :
    (fullEqDetailed order x y).value = decide (x = y) :=
  (fieldsDetailed_value _ _ _ _ _).trans (fullEq_correct _ _ _)

/-- Cost-only comparisons in internal folds have no key field. -/
def costDetailed (x y : Vector Rat m) : Compared Bool :=
  let r := vectorScan x y
  ⟨r.1, { calls := 1, costVectorCalls := 1, costRejects := if r.1 then 0 else 1,
          equalStates := if r.1 then 1 else 0, ratCoordinateChecks := r.2 }⟩

@[simp] theorem costDetailed_correct (x y : Vector Rat m) :
    (costDetailed x y).value = decide (x = y) := by
  simp [costDetailed, vectorEq_correct]

def rootDetailed (x y : ExecRootState m) : Compared Bool :=
  fieldsDetailed false x.used y.used x.cost y.cost

@[simp] theorem rootDetailed_correct (x y : ExecRootState m) :
    (rootDetailed x y).value = decide (x = y) := by
  rw [rootDetailed, fieldsDetailed_value]
  apply Bool.eq_iff_iff.mpr
  cases x; cases y
  simp [fieldsEq, vectorEq_correct]

def memberWith {α : Type} (eq : α → α → Bool) (x : α) : List α → Bool
  | [] => false
  | y :: ys => if eq x y then true else memberWith eq x ys

def dedupWith {α : Type} (eq : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => let ys := dedupWith eq xs
              if memberWith eq x ys then ys else x :: ys

theorem memberWith_correct {α : Type} [DecidableEq α] (eq : α → α → Bool)
    (h : ∀ x y, eq x y = decide (x = y)) (x : α) (xs : List α) :
    memberWith eq x xs = decide (x ∈ xs) := by
  induction xs with
  | nil => rfl
  | cons y ys ih => by_cases he : x = y <;> simp [memberWith, h, he, ih]

theorem dedupWith_correct {α : Type} [DecidableEq α] (eq : α → α → Bool)
    (h : ∀ x y, eq x y = decide (x = y)) (xs : List α) :
    dedupWith eq xs = xs.dedup := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [dedupWith, memberWith_correct eq h, ih, List.dedup_cons']

def memberDetailed {α : Type} (eq : α → α → Compared Bool) (x : α) : List α → Compared Bool
  | [] => ⟨false, {}⟩
  | y :: ys => let c := eq x y
              if c.value then c else let r := memberDetailed eq x ys
                                    ⟨r.value, c.counts.add r.counts⟩

def dedupDetailed {α : Type} (eq : α → α → Compared Bool) : List α → Compared (List α)
  | [] => ⟨[], {}⟩
  | x :: xs => let r := dedupDetailed eq xs
              let c := memberDetailed eq x r.value
              ⟨if c.value then r.value else x :: r.value, r.counts.add c.counts⟩

theorem memberDetailed_spec {α : Type} [DecidableEq α] (eq : α → α → Compared Bool)
    (he : ∀ x y, (eq x y).value = decide (x = y))
    (hc : ∀ x y, (eq x y).counts.calls = 1) (x : α) (xs : List α) :
    (memberDetailed eq x xs).value = (memberCounted x xs).1 ∧
      (memberDetailed eq x xs).counts.calls = (memberCounted x xs).2 := by
  induction xs with
  | nil => simp [memberDetailed, memberCounted]
  | cons y ys ih =>
    by_cases h : x = y <;>
      simp [memberDetailed, memberCounted, CompareCounts.add, he, hc, h, ih, Nat.add_comm]

theorem dedupDetailed_spec {α : Type} [DecidableEq α] (eq : α → α → Compared Bool)
    (he : ∀ x y, (eq x y).value = decide (x = y))
    (hc : ∀ x y, (eq x y).counts.calls = 1) (xs : List α) :
    (dedupDetailed eq xs).value = xs.dedup ∧
      (dedupDetailed eq xs).counts.calls = dedupComparisons xs := by
  induction xs with
  | nil => simp [dedupDetailed, dedupComparisons]
  | cons x xs ih =>
    simp [dedupDetailed, CompareCounts.add, ih, (memberDetailed_spec eq he hc _ _).1,
      (memberDetailed_spec eq he hc _ _).2, memberCounted_erase, memberCounted_count,
      dedupComparisons, List.dedup_cons']

def ratWork {α : Type} [DecidableEq α] (kx ky : Vector α m) (cx cy : Vector Rat m) : Nat :=
  if kx = ky then (vectorScan cx cy).2 else 0

theorem keyFirst_ratWork {α : Type} [DecidableEq α]
    (kx ky : Vector α m) (cx cy : Vector Rat m) :
    (fieldsDetailed false kx ky cx cy).counts.ratCoordinateChecks = ratWork kx ky cx cy := by
  by_cases h : kx = ky <;> simp [fieldsDetailed, ratWork, vectorEq_correct, h]

theorem projection_pair (x y : ExecFullState m) :
    ratWork (support x.q) (support y.q) x.cost y.cost = ratWork x.q y.q x.cost y.cost +
      if x.q ≠ y.q ∧ support x.q = support y.q then (vectorScan x.cost y.cost).2 else 0 := by
  by_cases hq : x.q = y.q
  · simp [ratWork, hq]
  · by_cases ha : support x.q = support y.q <;> simp [ratWork, hq, ha]

/-- Same input-pair list only: actual full/compact runs may compare different pairs. -/
theorem projection_pairs (ps : List (ExecFullState m × ExecFullState m)) :
    (ps.map fun p => ratWork (support p.1.q) (support p.2.q) p.1.cost p.2.cost).sum =
      (ps.map fun p => ratWork p.1.q p.2.q p.1.cost p.2.cost).sum +
      (ps.map fun p => if p.1.q ≠ p.2.q ∧ support p.1.q = support p.2.q
        then (vectorScan p.1.cost p.2.cost).2 else 0).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rcases p with ⟨x, y⟩
    simp only [List.map_cons, List.sum_cons]
    rw [projection_pair x y, ih]
    omega

end UAVProof.TreeBudgetSubtreeCompare
