import LeanCompletion.UAV.TreeBudgetSubtreeScalarDedup

namespace UAVProof.TreeBudgetSubtreeScalar
open TreeBudgetSubtreeExecutable TreeBudgetSubtreeStats TreeBudgetSubtreeResourceSeed
open TreeBudgetSubtreeIntegerWitnessSeed TreeFlowExistence
variable {N m : Nat}

/-- One callback evaluation per cell, with scalar write and index/loop control. -/
def tabulateC {α : Type} {n : Nat} (f : Fin n → Counted α) : Counted (Vector α n) :=
  let rs := Vector.ofFn f
  ⟨rs.map Counted.value, (∑ i : Fin n, (val rs i).ops) + 5 * n + 1⟩

@[simp] theorem tabulateC_value {α : Type} {n : Nat} (f : Fin n → Counted α) :
    (tabulateC f).value = Vector.ofFn (fun i => (f i).value) := by
  apply vector_ext
  intro i
  simp [tabulateC, val]

@[simp] theorem tabulateC_ops {α : Type} {n : Nat} (f : Fin n → Counted α) :
    (tabulateC f).ops = (∑ i : Fin n, (f i).ops) + 5 * n + 1 := by
  simp [tabulateC]

def supportC (q : Vector Nat m) : Counted (Vector Bool m) :=
  tabulateC (fun i => ⟨decide (0 < val q i), 2⟩)

def addC (x y : Vector Int m) : Counted (Vector Int m) :=
  tabulateC (fun i => ⟨val x i + val y i, 3⟩)

def scaleC (w : Int) (q : Vector Nat m) : Counted (Vector Int m) :=
  tabulateC (fun i => ⟨w * ((val q i : Nat) : Int), 4⟩)

def subsetC (a b : Vector Bool m) : Counted Bool :=
  let r := allC (fun i => ⟨decide (val a i = true → val b i = true), 4⟩) (List.finRange m)
  ⟨r.value, r.ops + 2 * m + 1⟩

def capC (r : TreeBudgetSubtreeInteger.IntRoot m) : Counted Bool :=
  let c := allC (fun i => ⟨decide (val r.used i ≤ 1), 2⟩) (List.finRange m)
  ⟨c.value, c.ops + 2 * m + 1⟩

def acceptC (B : Int) (r : TreeBudgetSubtreeInteger.IntRoot m) : Counted Bool :=
  let c := allC (fun i => ⟨decide (val r.used i = 1 ∧ val r.cost i ≤ B), 5⟩) (List.finRange m)
  ⟨c.value, c.ops + 2 * m + 1⟩

def rootAddC (r : TreeBudgetSubtreeInteger.IntRoot m)
    (e : TreeBudgetSubtreeInteger.IntState m) : Counted (TreeBudgetSubtreeInteger.IntRoot m) :=
  let u := tabulateC (fun i => ⟨val r.used i + bit (val e.active i), 4⟩)
  let c := addC r.cost e.cost
  ⟨⟨u.value, c.value⟩, u.ops + c.ops + 2⟩

@[simp] theorem supportC_value (q : Vector Nat m) : (supportC q).value = support q := by
  simp [supportC, support]

@[simp] theorem addC_value (x y : Vector Int m) :
    (addC x y).value = TreeBudgetSubtreeInteger.add x y := by
  simp [addC, TreeBudgetSubtreeInteger.add]

@[simp] theorem scaleC_value (w : Int) (q : Vector Nat m) :
    (scaleC w q).value = Vector.ofFn (fun i => w * ((val q i : Nat) : Int)) := by simp [scaleC]

@[simp] theorem subsetC_value (a b : Vector Bool m) : (subsetC a b).value = subsetB a b := by
  simp [subsetC, subsetB]

@[simp] theorem capC_value (r : TreeBudgetSubtreeInteger.IntRoot m) :
    (capC r).value = TreeBudgetSubtreeInteger.cap r := by simp [capC, TreeBudgetSubtreeInteger.cap]

@[simp] theorem acceptC_value (B : Int) (r : TreeBudgetSubtreeInteger.IntRoot m) :
    (acceptC B r).value = TreeBudgetSubtreeInteger.accept B r := by
  simp [acceptC, TreeBudgetSubtreeInteger.accept]

@[simp] theorem rootAddC_value (r : TreeBudgetSubtreeInteger.IntRoot m)
    (e : TreeBudgetSubtreeInteger.IntState m) :
    (rootAddC r e).value = TreeBudgetSubtreeInteger.rootAdd r e := by
  simp [rootAddC, TreeBudgetSubtreeInteger.rootAdd]

theorem vector_arithmetic_ops (w : Int) (q : Vector Nat m) (x y : Vector Int m) :
    (supportC q).ops = 7*m+1 ∧ (addC x y).ops = 8*m+1 ∧ (scaleC w q).ops = 9*m+1 := by
  simp [supportC, addC, scaleC]; omega

theorem subsetC_bound (a b : Vector Bool m) : (subsetC a b).ops ≤ 9*m+2 := by
  have h := allC_bound (fun i => (⟨decide (val a i = true → val b i = true), 4⟩ : Counted Bool))
    (List.finRange m) 4 (by simp)
  simp only [List.length_finRange] at h
  dsimp only [subsetC]; omega

theorem capC_bound (r : TreeBudgetSubtreeInteger.IntRoot m) : (capC r).ops ≤ 7*m+2 := by
  have h := allC_bound (fun i => (⟨decide (val r.used i ≤ 1), 2⟩ : Counted Bool))
    (List.finRange m) 2 (by simp)
  simp only [List.length_finRange] at h
  dsimp only [capC]; omega

theorem acceptC_bound (B : Int) (r : TreeBudgetSubtreeInteger.IntRoot m) :
    (acceptC B r).ops ≤ 10*m+2 := by
  have h := allC_bound (fun i =>
    (⟨decide (val r.used i = 1 ∧ val r.cost i ≤ B), 5⟩ : Counted Bool))
    (List.finRange m) 5 (by simp)
  simp only [List.length_finRange] at h
  dsimp only [acceptC]; omega

@[simp] theorem rootAddC_ops (r : TreeBudgetSubtreeInteger.IntRoot m)
    (e : TreeBudgetSubtreeInteger.IntState m) : (rootAddC r e).ops = 17*m+4 := by
  simp [rootAddC, addC]; omega

def sumC : List Nat → Counted Nat
  | [] => ⟨0, 1⟩
  | x :: xs => let r := sumC xs; ⟨x + r.value, r.ops + 4⟩

@[simp] theorem sumC_spec (xs : List Nat) :
    (sumC xs).value = xs.sum ∧ (sumC xs).ops = 4*xs.length+1 := by
  induction xs <;> simp_all [sumC] <;> omega

/-- Preserve the original map-then-sum evaluation at every nonlocal coordinate. -/
def glueC (v : Fin N) (q : Vector Nat m) (es : List (Entry N m)) : Counted (Matrix N m) :=
  tabulateC fun i => tabulateC fun x =>
    if x = v then ⟨val q i, 2⟩ else
      let a := mapC (fun e => ⟨TreeBudgetSubtreeWitness.matrixVal e.matrix i x, 3⟩) es
      let b := sumC a.value
      ⟨b.value, a.ops + b.ops + 1⟩

@[simp] theorem glueC_value (v : Fin N) (q : Vector Nat m) (es : List (Entry N m)) :
    (glueC v q es).value = glue v q es := by
  simp only [glueC, tabulateC_value, glue]
  congr 1; funext i; congr 1; funext x
  split <;> simp

theorem glueC_ops (v : Fin N) (q : Vector Nat m) (es : List (Entry N m)) :
    (glueC v q es).ops = 8*m*N + 10*m*(N-1)*es.length + 5*m+1 := by
  have hn : 1 ≤ N := Nat.zero_lt_of_lt v.isLt
  have hsum : (∑ x : Fin N, if x = v then 2 else 10*es.length+3) =
      2 + (N-1)*(10*es.length+3) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    rw [Finset.sum_congr rfl (fun x hx => if_neg (Finset.mem_erase.mp hx).1)]
    simp [Nat.add_comm]
  simp only [glueC, tabulateC_ops]
  have hcell (i : Fin m) (x : Fin N) :
      (if x = v then (⟨val q i, 2⟩ : Counted Nat) else
        let a := mapC (fun e => ⟨TreeBudgetSubtreeWitness.matrixVal e.matrix i x, 3⟩) es
        let b := sumC a.value
        ⟨b.value, a.ops + b.ops + 1⟩).ops = if x = v then 2 else 10*es.length+3 := by
    split <;> simp [mapWork_eq] <;> omega
  simp only [hcell, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have he : N-1+1=N := by omega
  nlinarith

def consC (a : Nat) (q : Vector Nat m) : Counted (Vector Nat (m+1)) :=
  let f : Fin (m+1) → Nat := Fin.cons a (val q)
  tabulateC (fun i => ⟨f i, 3⟩)

@[simp] theorem consC_value (a : Nat) (q : Vector Nat m) : (consC a q).value = consV a q := by
  simp [consC, consV]

@[simp] theorem consC_ops (a : Nat) (q : Vector Nat m) : (consC a q).ops = 8*(m+1)+1 := by
  simp [consC]; omega

end UAVProof.TreeBudgetSubtreeScalar
