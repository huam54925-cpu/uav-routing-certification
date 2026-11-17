import LeanCompletion.UAV.TreeBudgetSubtreePreRanges
import LeanCompletion.UAV.TreeBudgetSubtreeComparePrimitives

/-!
I0/I1: the scalar reference machine. A scalar read, write, arithmetic operation,
test, list constructor/destructor and branch each cost one instruction. Calls
and returns are included in the displayed control tariffs. Index enumeration
costs two instructions per cell plus one terminal test. These are source
instructions, not addresses, allocation, reference counting, or compiler time.
Counts and the old statistics are ghost observations. In particular, obtaining
their lengths/sums does not run the value computation a second time.
-/
namespace UAVProof.TreeBudgetSubtreeScalar
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats
open TreeBudgetSubtreeResourceSeed TreeBudgetSubtreeIntegerWitnessSeed
open TreeFlowExistence

structure Counted (α : Type) where
  value : α
  ops : Nat

/-- One list match, callback, output cons, and continuation per element. -/
def mapC {α β : Type} (f : α → Counted β) : List α → Counted (List β)
  | [] => ⟨[], 1⟩
  | x :: xs => let a := f x; let r := mapC f xs
              ⟨a.value :: r.value, a.ops + r.ops + 3⟩

def mapWork {α : Type} (f : α → Nat) : List α → Nat
  | [] => 1
  | x :: xs => f x + mapWork f xs + 3

@[simp] theorem mapC_value {α β : Type} (f : α → Counted β) (xs : List α) :
    (mapC f xs).value = xs.map (fun x => (f x).value) := by
  induction xs <;> simp_all [mapC]

@[simp] theorem mapC_ops {α β : Type} (f : α → Counted β) (xs : List α) :
    (mapC f xs).ops = mapWork (fun x => (f x).ops) xs := by
  induction xs <;> simp_all [mapC, mapWork]

theorem mapWork_eq {α : Type} (f : α → Nat) (xs : List α) :
    mapWork f xs = (xs.map f).sum + 3 * xs.length + 1 := by
  induction xs <;> simp_all [mapWork] <;> omega

def filterC {α : Type} (p : α → Counted Bool) : List α → Counted (List α)
  | [] => ⟨[], 1⟩
  | x :: xs => let a := p x; let r := filterC p xs
              ⟨if a.value then x :: r.value else r.value, a.ops + r.ops + 4⟩

@[simp] theorem filterC_value {α : Type} (p : α → Counted Bool) (xs : List α) :
    (filterC p xs).value = xs.filter (fun x => (p x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : (p x).value <;> simp [filterC, ih, h]

theorem filterC_ops {α : Type} (p : α → Counted Bool) (xs : List α) :
    (filterC p xs).ops = (xs.map fun x => (p x).ops).sum + 4 * xs.length + 1 := by
  induction xs <;> simp_all [filterC] <;> omega

/-- `append` copies its left list; the right list is reused. -/
def appendC {α : Type} : List α → List α → Counted (List α)
  | [], ys => ⟨ys, 1⟩
  | x :: xs, ys => let r := appendC xs ys; ⟨x :: r.value, r.ops + 3⟩

@[simp] theorem appendC_spec {α : Type} (xs ys : List α) :
    (appendC xs ys).value = xs ++ ys ∧ (appendC xs ys).ops = 3 * xs.length + 1 := by
  induction xs <;> simp_all [appendC] <;> omega

def flatMapC {α β : Type} (f : α → Counted (List β)) : List α → Counted (List β)
  | [] => ⟨[], 1⟩
  | x :: xs => let a := f x; let r := flatMapC f xs; let c := appendC a.value r.value
              ⟨c.value, a.ops + r.ops + c.ops + 3⟩

@[simp] theorem flatMapC_value {α β : Type} (f : α → Counted (List β)) (xs : List α) :
    (flatMapC f xs).value = xs.flatMap (fun x => (f x).value) := by
  induction xs <;> simp_all [flatMapC, (appendC_spec _ _).1]

theorem flatMapC_ops {α β : Type} (f : α → Counted (List β)) (xs : List α) :
    (flatMapC f xs).ops =
      (xs.map fun x => (f x).ops + 3 * (f x).value.length).sum + 4 * xs.length + 1 := by
  induction xs <;> simp_all [flatMapC, (appendC_spec _ _).2] <;> omega

/-- A short-circuit universal scan; the terminal branch is also charged. -/
def allC {α : Type} (p : α → Counted Bool) : List α → Counted Bool
  | [] => ⟨true, 1⟩
  | x :: xs => let a := p x
              if a.value then let r := allC p xs; ⟨r.value, a.ops + r.ops + 3⟩
              else ⟨false, a.ops + 3⟩

def allWork {α : Type} (p : α → Bool) (c : α → Nat) : List α → Nat
  | [] => 1
  | x :: xs => c x + 3 + if p x then allWork p c xs else 0

@[simp] theorem allC_value {α : Type} (p : α → Counted Bool) (xs : List α) :
    (allC p xs).value = xs.all (fun x => (p x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : (p x).value <;> simp [allC, ih, h]

theorem allC_ops {α : Type} (p : α → Counted Bool) (xs : List α) :
    (allC p xs).ops = allWork (fun x => (p x).value) (fun x => (p x).ops) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : (p x).value <;>
      simp [allC, allWork, ih, h] <;> omega

theorem allC_bound {α : Type} (p : α → Counted Bool) (xs : List α) (k : Nat)
    (hk : ∀ x ∈ xs, (p x).ops ≤ k) : (allC p xs).ops ≤ (k + 3) * xs.length + 1 := by
  induction xs with
  | nil => simp [allC]
  | cons x xs ih =>
    have hx := hk x (by simp)
    have ht := ih (fun y hy => hk y (by simp [hy]))
    simp only [allC, List.length_cons]
    split <;> dsimp only <;> nlinarith

/-- Enumeration, scalar reads of both coordinates, equality, and scan control. -/
def vectorEqC {α : Type} [DecidableEq α] {m : Nat} (x y : Vector α m) : Counted Bool :=
  let r := allC (fun i => ⟨decide (val x i = val y i), 3⟩) (List.finRange m)
  ⟨r.value, r.ops + 2 * m + 1⟩

@[simp] theorem vectorEqC_value {α : Type} [DecidableEq α] {m : Nat}
    (x y : Vector α m) : (vectorEqC x y).value = decide (x = y) := by
  simpa [vectorEqC, TreeBudgetSubtreeCompare.vectorEq] using
    TreeBudgetSubtreeCompare.vectorEq_correct x y

theorem vectorEqC_bound {α : Type} [DecidableEq α] {m : Nat}
    (x y : Vector α m) : (vectorEqC x y).ops ≤ 8 * m + 2 := by
  have h := allC_bound (fun i => (⟨decide (val x i = val y i), 3⟩ : Counted Bool))
    (List.finRange m) 3 (by simp)
  simp only [List.length_finRange] at h
  dsimp only [vectorEqC]
  omega

def fieldsEqC {α : Type} [DecidableEq α] {m : Nat}
    (x y : Vector α m) (a b : Vector Int m) : Counted Bool :=
  let k := vectorEqC x y
  if k.value then let c := vectorEqC a b; ⟨c.value, k.ops + c.ops + 1⟩
  else ⟨false, k.ops + 1⟩

@[simp] theorem fieldsEqC_value {α : Type} [DecidableEq α] {m : Nat}
    (x y : Vector α m) (a b : Vector Int m) :
    (fieldsEqC x y a b).value = decide (x = y ∧ a = b) := by
  by_cases h : x = y <;> simp [fieldsEqC, h]

theorem fieldsEqC_bound {α : Type} [DecidableEq α] {m : Nat}
    (x y : Vector α m) (a b : Vector Int m) :
    (fieldsEqC x y a b).ops ≤ 16 * m + 5 := by
  have h := vectorEqC_bound x y
  have g := vectorEqC_bound a b
  dsimp only [fieldsEqC]
  split <;> dsimp only <;> omega

def stateEqC {m : Nat} (x y : TreeBudgetSubtreeInteger.IntState m) : Counted Bool :=
  fieldsEqC x.active y.active x.cost y.cost

def rootEqC {m : Nat} (x y : TreeBudgetSubtreeInteger.IntRoot m) : Counted Bool :=
  fieldsEqC x.used y.used x.cost y.cost

@[simp] theorem stateEqC_value {m : Nat} (x y : TreeBudgetSubtreeInteger.IntState m) :
    (stateEqC x y).value = decide (x = y) := by
  cases x; cases y; simp [stateEqC]

@[simp] theorem rootEqC_value {m : Nat} (x y : TreeBudgetSubtreeInteger.IntRoot m) :
    (rootEqC x y).value = decide (x = y) := by
  cases x; cases y; simp [rootEqC]

def childrenC {N : Nat} (R : RootedTree (Fin N)) (v : Fin N) : Counted (List (Fin N)) :=
  let r := filterC (fun w => ⟨decide (w ≠ R.root ∧ R.parent w = v), 6⟩) (List.finRange N)
  ⟨r.value, r.ops + 2 * N + 1⟩

@[simp] theorem childrenC_value {N : Nat} (R : RootedTree (Fin N)) (v : Fin N) :
    (childrenC R v).value = childrenList R v := by simp [childrenC, childrenList]

theorem childrenC_ops {N : Nat} (R : RootedTree (Fin N)) (v : Fin N) :
    (childrenC R v).ops = 12 * N + 2 := by
  simp [childrenC, filterC_ops]; omega

end UAVProof.TreeBudgetSubtreeScalar
