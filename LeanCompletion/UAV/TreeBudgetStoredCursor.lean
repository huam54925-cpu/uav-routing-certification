import LeanCompletion.UAV.TreeBudgetCostedParsing

/-! Binary traversal fuel. The bound in `Fin` is erased proof data; its value
is the result of an executed binary subtraction. Initialization uses `addNatD`
at the caller. No heap-sized unary list is constructed. -/
namespace UAVProof.TreeBudgetStoredCursor
open TreeBudgetBitMachine TreeBudgetBitPrimitives

def cursorStep (fuel : ℕ) : Costed (Option (Fin fuel)) :=
  let test := zeroNatD fuel
  if hz : test.value then
    ⟨none, test.steps + 1, test.allocations⟩
  else
    let dec := subNatD fuel 1
    have hlt : dec.value < fuel := by
      have hn : fuel ≠ 0 := by simpa only [test, zeroNatD_value, decide_eq_true_eq] using hz
      simp only [dec, subNatD_value]
      omega
    ⟨some ⟨dec.value, hlt⟩, test.steps + dec.steps + 1, test.allocations + dec.allocations⟩

@[simp] theorem cursorStep_zero : (cursorStep 0).value = none := by simp [cursorStep]

@[simp] theorem cursorStep_succ (fuel : ℕ) :
    (cursorStep (fuel + 1)).value = some ⟨fuel, by omega⟩ := by
  simp [cursorStep]

theorem cursorStep_steps (fuel B : ℕ) (hf : fuel.size ≤ B) (hB : 1 ≤ B) :
    (cursorStep fuel).steps ≤ 128 * (B + 1) + 1 := by
  have hz := (dynamic_steps fuel 0 B hf (by simp)).1
  have hd := (dynamic_steps fuel 1 B hf (by simpa using hB)).2.2.1
  change (zeroNatD fuel).steps ≤ _ at hz
  unfold cursorStep
  dsimp only
  split <;> dsimp only <;> omega

theorem cursorStep_allocations (fuel B : ℕ) (hf : fuel.size ≤ B) (hB : 1 ≤ B) :
    (cursorStep fuel).allocations ≤ 16 * (B + 1) := by
  have hz := (dynamic_allocations fuel 0 B hf (by simp)).1
  have hd := (dynamic_allocations fuel 1 B hf (by simpa using hB)).2.2.1
  change (zeroNatD fuel).allocations ≤ _ at hz
  unfold cursorStep
  dsimp only
  split <;> dsimp only <;> omega

theorem cursorStep_allocations_le_steps (fuel : ℕ) :
    (cursorStep fuel).allocations ≤ (cursorStep fuel).steps := by
  have hz := (dynamic_allocations_le_steps fuel 0).1
  have hd := (dynamic_allocations_le_steps fuel 1).2.2.1
  change (zeroNatD fuel).allocations ≤ (zeroNatD fuel).steps at hz
  unfold cursorStep
  dsimp only
  split <;> dsimp only <;> omega

end UAVProof.TreeBudgetStoredCursor
