import LeanCompletion.UAV.TreeBudgetSubtreeCompact

/-! Materialized executable states and child enumeration. Semantic decoding
is separate from the executable vector operations. -/
namespace UAVProof.TreeBudgetSubtreeExecutable
open TreeFlowExistence TreeBudgetSubtreeState
variable {N m : ℕ}

def childrenList (R : RootedTree (Fin N)) (v : Fin N) : List (Fin N) :=
  (List.finRange N).filter fun w => decide (w ≠ R.root ∧ R.parent w = v)

@[simp] theorem mem_childrenList (R : RootedTree (Fin N)) (v w : Fin N) :
    w ∈ childrenList R v ↔ w ∈ R.children v := by
  simp [childrenList]

theorem childrenList_nodup (R : RootedTree (Fin N)) (v : Fin N) :
    (childrenList R v).Nodup := (List.nodup_finRange N).filter _

theorem childrenList_toFinset (R : RootedTree (Fin N)) (v : Fin N) :
    (childrenList R v).toFinset = R.children v := by ext w; simp

theorem childrenList_sum {α : Type*} [AddCommMonoid α]
    (R : RootedTree (Fin N)) (v : Fin N) (f : Fin N → α) :
    ((childrenList R v).map f).sum = ∑ u ∈ R.children v, f u := by
  rw [← childrenList_toFinset]
  exact (List.sum_toFinset _ (childrenList_nodup R v)).symm

def val {α : Type*} (v : Vector α m) (i : Fin m) : α := v[i]

@[simp] theorem val_ofFn {α : Type*} (f : Fin m → α) (i : Fin m) :
    val (Vector.ofFn f) i = f i := by simp [val]

theorem vector_ext {α : Type*} {x y : Vector α m}
    (h : ∀ i, val x i = val y i) : x = y := by
  apply Vector.ext
  intro i hi
  exact h ⟨i, hi⟩

structure ExecCompactState (m : ℕ) where
  active : Vector Bool m
  cost : Vector ℚ m
  deriving DecidableEq, Inhabited

def decodeState (e : ExecCompactState m) : CompactState m :=
  ⟨Finset.univ.filter (fun i => val e.active i = true), val e.cost⟩

def encodeState (z : CompactState m) : ExecCompactState m :=
  ⟨Vector.ofFn (fun i => decide (i ∈ z.active)), Vector.ofFn z.cost⟩

@[simp] theorem mem_decodeState (e : ExecCompactState m) (i : Fin m) :
    i ∈ (decodeState e).active ↔ val e.active i = true := by simp [decodeState]

@[simp] theorem decode_encodeState (z : CompactState m) :
    decodeState (encodeState z) = z := by
  cases z with
  | mk a c =>
    unfold decodeState encodeState
    congr 1
    · ext i; simp
    · funext i; simp

@[simp] theorem encode_decodeState (e : ExecCompactState m) :
    encodeState (decodeState e) = e := by
  cases e with
  | mk a c =>
    unfold encodeState decodeState
    congr 1 <;> apply vector_ext <;> intro i <;> simp

theorem state_ext {x y : ExecCompactState m}
    (ha : ∀ i, val x.active i = val y.active i)
    (hc : ∀ i, val x.cost i = val y.cost i) : x = y := by
  cases x; cases y
  congr 1
  · exact vector_ext ha
  · exact vector_ext hc

def support (q : Vector ℕ m) : Vector Bool m := Vector.ofFn fun i => decide (0 < val q i)

def subsetB (a b : Vector Bool m) : Bool :=
  (List.finRange m).all fun i => decide (val a i = true → val b i = true)

@[simp] theorem subsetB_spec (a b : Vector Bool m) :
    subsetB a b = true ↔ ∀ i, val a i = true → val b i = true := by
  simp only [subsetB, List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq]

def addCost (x y : Vector ℚ m) : Vector ℚ m :=
  Vector.ofFn fun i => val x i + val y i

def zeroCost (m : ℕ) : Vector ℚ m := Vector.ofFn fun _ => 0

def bit (b : Bool) : ℕ := if b then 1 else 0

theorem bit_le (b : Bool) : bit b ≤ 1 := by cases b <;> decide

@[simp] theorem bit_eq_zero (b : Bool) : bit b = 0 ↔ b = false := by cases b <;> decide
@[simp] theorem bit_eq_one (b : Bool) : bit b = 1 ↔ b = true := by cases b <;> decide

end UAVProof.TreeBudgetSubtreeExecutable
