import LeanCompletion.UAV.TreeBudgetLeWordsTM2

namespace UAVProof.TreeBudgetLeWordsExamples
open TreeBudgetBinaryCodec TreeBudgetLeWordsTM2

def run : ℕ → machine.Cfg → machine.Cfg
  | 0, c => c
  | n + 1, c => match machine.step c with
    | none => c
    | some d => run n d

def observe (xs ys : Bits) : Bits × Bits × Bits × Bits :=
  let c : TreeBudgetFrameRoutineTM2.Configuration (Fin 4) Unit :=
    run (xs.length + ys.length + 1) (cfg none true xs ys)
  (c.stk 0, c.stk 1, c.stk 2, c.stk 3)

theorem zeros : observe [] [] = ([], [], [], [true]) := by decide +kernel
theorem positive_above_zero : observe [true] [] = ([], [], [], [false]) := by decide +kernel
theorem zero_below_positive : observe [] [false, true] = ([], [], [], [true]) := by decide +kernel
theorem equal_words : observe [true, false, true] [true, false, true] =
    ([], [], [], [true]) := by decide +kernel
theorem equal_with_padding : observe [true, false, false] [true] =
    ([], [], [], [true]) := by decide +kernel
theorem high_bit_overrides_low_less : observe [false, true] [true] =
    ([], [], [], [false]) := by decide +kernel
theorem high_bit_overrides_low_greater : observe [true] [false, true] =
    ([], [], [], [true]) := by decide +kernel
theorem long_zero_padding : observe [false, false, false, false] [] =
    ([], [], [], [true]) := by decide +kernel
theorem strict_greater_same_length : observe [true, true, true] [false, true, true] =
    ([], [], [], [false]) := by decide +kernel
theorem strict_less_same_length : observe [false, true, true] [true, true, true] =
    ([], [], [], [true]) := by decide +kernel

end UAVProof.TreeBudgetLeWordsExamples
