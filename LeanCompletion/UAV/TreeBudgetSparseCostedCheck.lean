import LeanCompletion.UAV.TreeBudgetSparseExecutionWidths

/-! Complete decoded-certificate check in the repository's reference word
model. List/array/function views follow the existing copyCells convention;
materialization, enumeration, scalar operations and folds are charged.
This is not yet a finite-alphabet TM2 simulation. -/
namespace UAVProof.TreeBudgetSparseCostedCheck
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCandidates
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetBinaryPreprocessing
open TreeBudgetSparseCodec TreeBudgetSparseVerifier TreeBudgetSparseWeightedCost
open TreeBudgetSparseExecutionWidths TreeBudgetVectorChecker TreeBudgetCertificate

def allD {α : Type} (f : α → Costed Bool) : List α → Costed Bool
  | [] => ⟨true, 1, 0⟩
  | x :: xs =>
    let head := f x
    let tail := allD f xs
    ⟨head.value && tail.value, head.steps + tail.steps + 2,
      head.allocations + tail.allocations⟩

@[simp] theorem allD_value {α : Type} (f : α → Costed Bool) (xs : List α) :
    (allD f xs).value = xs.all (fun x => (f x).value) := by
  induction xs <;> simp [allD, *]

theorem allD_work {α : Type} (f : α → Costed Bool) (xs : List α) (K : ℕ)
    (h : ∀ x ∈ xs, work (f x) ≤ K) : work (allD f xs) ≤ xs.length * (K + 2) + 1 := by
  induction xs with
  | nil => simp [allD, work]
  | cons x xs ih =>
    have hh := h x (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [allD, work, List.length_cons] at *
    nlinarith

/-- The natural range loop pays for binary index generation; Fin indices are
its proof-refined view, with one additional cell per refinement. -/
def allFinD (n : ℕ) (f : Fin n → Costed Bool) : Costed Bool :=
  let indices := rangeFrom 0 n
  let out := allD f (List.finRange n)
  ⟨out.value, indices.steps + out.steps + n + 1, indices.allocations + out.allocations + n⟩

@[simp] theorem allFinD_value (n : ℕ) (f : Fin n → Costed Bool) :
    (allFinD n f).value = (List.finRange n).all (fun v => (f v).value) := by simp [allFinD]

theorem allFinD_work (n N K : ℕ) (f : Fin n → Costed Bool) (hn : n ≤ N)
    (h : ∀ v, work (f v) ≤ K) :
    work (allFinD n f) ≤ n * (K + 256 * (N + 2) + 4) + 3 := by
  have hi := rangeFrom_work 0 n N (N + 1) (by omega)
    ((TreeBudgetCostedCodec.nat_size_le N).trans (by omega)) (by omega)
  have ht := allD_work f (List.finRange n) K (by intros; apply h)
  simp only [List.length_finRange] at ht
  simp only [allFinD, work] at *
  nlinarith

def materialize {n : ℕ} (C : Certificate (Fin n)) : Costed RawCertificate :=
  collect (List.ofFn fun i =>
    let row := copyCells (List.ofFn (C.row i))
    let count := addNatD (C.count i) 0
    (⟨(count.value, row.value), count.steps + row.steps + 2,
      count.allocations + row.allocations + 2⟩ : Costed RawEntry))

@[simp] theorem materialize_value {n : ℕ} (C : Certificate (Fin n)) :
    (materialize C).value = toRaw C := by
  simp [materialize, toRaw, List.map_ofFn, Function.comp_def]

theorem materialize_work {n : ℕ} (C : Certificate (Fin n)) (N : ℕ)
    (hn : n ≤ N) (hk : C.size ≤ N) (hc : ∀ i, (C.count i).size ≤ N) :
    work (materialize C) ≤ 256 * (N + 1) ^ 2 := by
  have ht := collect_work (List.ofFn fun i =>
    (⟨((addNatD (C.count i) 0).value, (copyCells (List.ofFn (C.row i))).value),
      (addNatD (C.count i) 0).steps + (copyCells (List.ofFn (C.row i))).steps + 2,
      (addNatD (C.count i) 0).allocations + (copyCells (List.ofFn (C.row i))).allocations + 2⟩
      : Costed RawEntry)) (128 * (N + 1)) (by
        intro x hx
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        have hs := (dynamic_steps (C.count i) 0 N (hc i) (by simp)).2.2.2
        have ha := (dynamic_allocations (C.count i) 0 N (hc i) (by simp)).2.2.2
        simp only [work, copyCells_steps, copyCells_allocations, List.length_ofFn]
        omega)
  simp only [List.length_ofFn] at ht
  change work (collect _) ≤ _
  have hm := Nat.mul_le_mul_right (128 * (N + 1) + 2) hk
  nlinarith

def countD : RawCertificate → Costed ℕ
  | [] => ⟨0, 1, 0⟩
  | e :: xs =>
    let tail := countD xs
    let out := addNatD e.1 tail.value
    ⟨out.value, tail.steps + out.steps + 1, tail.allocations + out.allocations⟩

@[simp] theorem countD_value (xs : RawCertificate) :
    (countD xs).value = (xs.map Prod.fst).sum := by induction xs <;> simp [countD, *]

theorem countD_work (xs : RawCertificate) (B : ℕ)
    (h : ((xs.map Prod.fst).sum).size ≤ B) :
    work (countD xs) ≤ xs.length * (80 * (B + 1)) + 1 := by
  have he : ∀ ys : RawCertificate, countD ys = sumNatCost (ys.map Prod.fst) := by
    intro ys
    induction ys <;> simp [countD, sumNatCost, *]
  rw [he xs]
  simpa using sumNatCost_work (xs.map Prod.fst) B h

def columnCheckD (I : Instance) (xs : RawCertificate) (v : Fin I.data.n) : Costed Bool :=
  let col := columnD xs v.val
  let eq := eqNatD col.value I.data.H[v]
  let root := eqNatD v.val I.data.parents.root.val
  ⟨root.value || eq.value, col.steps + eq.steps + root.steps + 2,
    col.allocations + eq.allocations + root.allocations⟩

@[simp] theorem columnCheckD_value (I : Instance) (C : Certificate (Fin I.data.n))
    (v : Fin I.data.n) :
    (columnCheckD I (toRaw C) v).value = decide (v ≠ I.data.parents.root →
      (List.ofFn fun i => C.count i * C.row i v).sum = I.data.H[v]) := by
  simp only [columnCheckD, columnD_toRaw, eqNatD_value]
  simp [Fin.ext_iff]

def checkD (I : Instance) (C : Certificate (Fin I.data.n)) : Costed Bool :=
  let table := materialize C
  let fees := scaleFeesCost I.data.numerators I.data.denominators I.data.budgetDenominator
  let budget := scaleBudgetCost I.data.denominators I.data.budgetNumerator
  let rows := allFinD C.size fun i =>
    let p := copyVector (Vector.ofFn (C.row i))
    let out := rowCheck I.data.parents I.data.H fees.value budget.value p.value
    ⟨out.value, p.steps + out.steps + 1, p.allocations + out.allocations⟩
  let total := countD table.value
  let count := eqNatD total.value I.routes
  let columns := allFinD I.data.n (columnCheckD I table.value)
  ⟨rows.value && count.value && columns.value,
    table.steps + fees.steps + budget.steps + rows.steps + total.steps + count.steps + columns.steps + 6,
    table.allocations + fees.allocations + budget.allocations + rows.allocations +
      total.allocations + count.allocations + columns.allocations⟩

@[simp] theorem checkD_value (I : Instance) (C : Certificate (Fin I.data.n)) :
    (checkD I C).value = check I C := by
  simp only [checkD, materialize_value, allFinD_value, copyVector_value, columnCheckD_value,
    eqNatD_value, scaleFeesCost_value _ _ _ I.data.positive,
    scaleBudgetCost_value _ _ _ I.data.budgetPositive]
  simp [check, countD_value, toRaw, List.map_ofFn, Function.comp_def]

end UAVProof.TreeBudgetSparseCostedCheck
