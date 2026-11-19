import LeanCompletion.UAV.TreeBudgetAddWordsTM2

namespace UAVProof.TreeBudgetAddWordsExamples
open TreeBudgetBinaryCodec TreeBudgetAddWordsTM2

def run : ℕ → machine.Cfg → machine.Cfg
  | 0, c => c
  | n + 1, c => match machine.step c with
    | none => c
    | some d => run n d

def observe (xs ys : Bits) : Bits × Bits × Bits × Bits :=
  let c : TreeBudgetFrameRoutineTM2.Configuration (Fin 4) (Fin 3) :=
    run (2 * (xs.length + ys.length) + 4) (cfg 0 none false xs ys [] [])
  (c.stk 0, c.stk 1, c.stk 2, c.stk 3)

theorem zero_plus_zero : observe [] [] = ([], [], [], []) := by decide +kernel
theorem carry_chain : observe [true, true, true] [true] =
    ([], [], [], [false, false, false, true]) := by decide +kernel
theorem unequal_lengths_left : observe [false, true, true] [true] =
    ([], [], [], [true, true, true]) := by decide +kernel
theorem unequal_lengths_right : observe [true] [false, true, true] =
    ([], [], [], [true, true, true]) := by decide +kernel
theorem zero_left : observe [] [false, true] = ([], [], [], [false, true]) := by decide +kernel
theorem zero_right : observe [true, false, true] [] =
    ([], [], [], [true, false, true]) := by decide +kernel
theorem padded_zero : observe [false, false] [false] =
    ([], [], [], [false, false]) := by decide +kernel
theorem both_carries : observe [true, true] [true, true] =
    ([], [], [], [false, true, true]) := by decide +kernel

end UAVProof.TreeBudgetAddWordsExamples
