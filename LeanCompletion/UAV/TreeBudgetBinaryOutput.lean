import LeanCompletion.UAV.TreeBudgetBinaryPipeline
import LeanCompletion.UAV.TreeBudgetCostedCodec

/-! Actual matrix materialization and binary serialization, including row-count
and column-count words. Shared search answers are expanded only here. -/
namespace UAVProof.TreeBudgetBinaryOutput
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCodec
open TreeBudgetBinaryCodec TreeBudgetBinaryPipeline TreeBudgetVectorMemoState
variable {n : ℕ}

def matrixListCost : RowsV n → Costed Matrix
  | [] => ⟨[], 1, 0⟩
  | p :: rows =>
    let row := copyCells p.toList
    let tail := matrixListCost rows
    ⟨row.value :: tail.value, row.steps + tail.steps + 1,
      row.allocations + tail.allocations + 1⟩

@[simp] theorem matrixListCost_value (rows : RowsV n) :
    (matrixListCost rows).value = rows.map Vector.toList := by
  induction rows with
  | nil => rfl
  | cons p rows ih => simp [matrixListCost, ih]

theorem matrixListCost_steps (rows : RowsV n) :
    (matrixListCost rows).steps = rows.length * (n + 2) + 1 := by
  induction rows with
  | nil => simp [matrixListCost]
  | cons p rows ih => simp [matrixListCost, ih]; ring

theorem matrixListCost_allocations (rows : RowsV n) :
    (matrixListCost rows).allocations ≤ (matrixListCost rows).steps := by
  induction rows with
  | nil => simp [matrixListCost]
  | cons p rows ih => simp [matrixListCost] at *; omega

def matrixBitsCost : AnswerV n → Costed (Option Bits)
  | none => ⟨none, 1, 1⟩
  | some rows =>
    let matrix := matrixListCost rows
    let out := encodeMatrixD matrix.value
    ⟨some out.value, matrix.steps + out.steps + 2,
      matrix.allocations + out.allocations + 2⟩

@[simp] theorem matrixBitsCost_value (answer : AnswerV n) :
    (matrixBitsCost answer).value = matrixBits answer := by
  cases answer <;> simp [matrixBitsCost, matrixBits]

theorem matrixBitsCost_roundtrip (answer : AnswerV n) :
    (matrixBitsCost answer).value.bind parseMatrix =
      answer.map (fun rows => rows.map Vector.toList) := by
  rw [matrixBitsCost_value, matrixBits_roundtrip]

theorem matrixBitsCost_allocations (answer : AnswerV n) :
    (matrixBitsCost answer).allocations ≤ (matrixBitsCost answer).steps := by
  cases answer with
  | none => simp [matrixBitsCost]
  | some rows =>
    have hm := matrixListCost_allocations rows
    have he := encodeMatrixD_allocations_le_steps (matrixListCost rows).value
    simp only [matrixBitsCost]
    omega

theorem matrixBitsCost_steps (rows : RowsV n) (m B : ℕ)
    (hm : rows.length ≤ m) (hp : ∀ p ∈ rows, ∀ i : Fin n, p[i].size ≤ B) :
    (matrixBitsCost (some rows)).steps ≤
      m * (n + 2) + 3 + 256 * (m + 1) ^ 2 +
        (m + 1) * (512 * (n + 1) ^ 2 * (B + 1) + 8 * (n + 1) * (B + 1) + 3) := by
  have he := encodeMatrixD_steps (rows.map Vector.toList) m n B
    (by simpa using hm) (by
      intro row hr; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr; simp) (by
      intro row hr x hx
      obtain ⟨p, hpr, rfl⟩ := List.mem_map.mp hr
      obtain ⟨i, hi, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
      subst x
      exact hp p hpr ⟨i, hi⟩)
  simp only [matrixBitsCost, matrixListCost_value, matrixListCost_steps]
  have hlen := Nat.mul_le_mul_right (n + 2) hm
  omega

def executeInput (I : TreeBudgetBinaryInput.Input) : Costed Result :=
  let out := preparedSearch I
  let wire := matrixBitsCost out.value.1
  ⟨⟨I.n, wire.value, out.value.2, out.events, out.work, out.allocations⟩,
    out.work + wire.steps + 1, out.allocations + wire.allocations + 6⟩

theorem executeInput_value (I : TreeBudgetBinaryInput.Input) :
    (executeInput I).value = runInput I := by
  simp [executeInput, runInput]

end UAVProof.TreeBudgetBinaryOutput
