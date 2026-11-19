import LeanCompletion.UAV.TreeBudgetCountHeaderTM2

namespace UAVProof.TreeBudgetCountGuardExamples
open TreeBudgetBinaryCodec TreeBudgetListGuardTM2

/-- Stop at the caller's return labels. The fuel also catches a mistaken
branch that keeps borrowing after the suffix has run out. -/
def observe : ℕ → Cfg → Option (Bool × Bits × Bits × Bits)
  | 0, _ => none
  | n+1, c =>
    if c.l = some 9 ∨ c.l = some 10 then
      some (decide (c.l = some 9), c.stk 0, c.stk 4, c.stk 5)
    else (machine.step c).bind (observe n)

theorem zero_with_suffix :
    observe 12 (atLabel 0 (encodeNat 0 ++ [true,false]) [] [] [] [] [false]) =
      some (true,[true,false],[],[false]) := by decide +kernel

theorem exact_fit :
    observe 64 (atLabel 0 (encodeNat 3 ++ [true,false,false]) [] [] [] [] [false,true]) =
      some (true,[true,false,false],[true,true,true],[false,true]) := by decide +kernel

theorem one_too_many :
    observe 64 (atLabel 0 (encodeNat 4 ++ [true,false,false]) [] [] [] [] [true]) =
      some (false,[],[],[true]) := by decide +kernel

theorem truncated_header :
    observe 16 (atLabel 0 [true,false,true] [] [] [] [] [true]) =
      some (false,[],[],[true]) := by decide +kernel

theorem noncanonical_header :
    observe 16 (atLabel 0 (word [false] ++ [true]) [] [] [] [] []) =
      some (false,[true],[],[]) := by decide +kernel

/-- A bounded run even for this 81-digit count, before any element call. -/
theorem huge_short (ctx : Bits) :
    Nonempty (Run (atLabel 0 (encodeNat (2^80) ++ [true,false,true]) [] [] [] [] ctx)
      (outcome (encodeNat (2^80) ++ [true,false,true]) ctx)
      (8*((encodeNat (2^80) ++ [true,false,true]).length+1)^2)) ∧
      (outcome (encodeNat (2^80) ++ [true,false,true]) ctx).l = some 10 := by
  refine ⟨⟨precheck_run _ _⟩, ?_⟩
  exact too_large _ _ _ (by decide +kernel)

end UAVProof.TreeBudgetCountGuardExamples
