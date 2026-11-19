import LeanCompletion.UAV.TreeBudgetIntTM2

namespace UAVProof.TreeBudgetIntExamples
open TreeBudgetBinaryCodec TreeBudgetIntTM2

def run : ℕ → machine.Cfg → machine.Cfg
  | 0, c => c
  | n + 1, c => match machine.step c with
    | none => c
    | some d => run n d

def observe (xs context : Bits) : Option (ℤ × Bits) × Bits × Bits :=
  let c : TreeBudgetFrameRoutineTM2.Configuration (Fin 5) (Fin 7) :=
    run (2 * xs.length + 2) (start xs context)
  (readResult c, c.stk 1, c.stk 4)

theorem zero : observe (encodeInt 0) [] = (some (0, []), [], []) := by decide +kernel
theorem positive_suffix : observe (encodeInt 6 ++ [true, false]) [false, true] =
    (some (6, [true, false]), [], [false, true]) := by decide +kernel
theorem negative_suffix : observe (encodeInt (-5) ++ [false, true]) [true] =
    (some (-5, [false, true]), [], [true]) := by decide +kernel
theorem reject_negative_zero : observe (true :: encodeNat 0 ++ [true]) [false] =
    (none, [], [false]) := by decide +kernel
theorem reject_empty : observe [] [true, false] = (none, [], [true, false]) := by decide +kernel
theorem reject_sign_only : observe [true] [false, true] = (none, [], [false, true]) := by decide +kernel
theorem reject_missing_payload : observe [false, true] [true] = (none, [], [true]) := by decide +kernel
theorem reject_missing_terminator : observe [true, true, false] [false] =
    (none, [], [false]) := by decide +kernel
theorem reject_positive_high_zero : observe (false :: word [true, false]) [] =
    (none, [], []) := by decide +kernel
theorem reject_negative_high_zero : observe (true :: word [true, false]) [true] =
    (none, [], [true]) := by decide +kernel

end UAVProof.TreeBudgetIntExamples
