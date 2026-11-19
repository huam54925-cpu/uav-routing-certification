import LeanCompletion.UAV.TreeBudgetWeightedRuns

namespace UAVProof.TreeBudgetWeightedExamples
open TreeBudgetBinaryCodec TreeBudgetWeightedTM2

def run : ℕ → Cfg → Option (ℕ × Bits)
  | 0, _ => none
  | n+1, c => if c.l = some 5 then some (value (c.stk 2), c.stk 5) else
      (machine.step c).bind (run n)

theorem padded_operands :
    run 160 (cfg 0 false [true,true,false] [false,true,false] [true,false] [] [] [false,true]) =
      some (7,[false,true]) := by decide +kernel

theorem long_carry :
    run 240 (cfg 0 false [true,true] [true,true,true] [true,true,true] [] [] [true]) =
      some (28,[true]) := by decide +kernel

theorem sparse_multiplier :
    run 160 (cfg 0 false [false,false,true] [true,true] [] [] [] []) =
      some (12,[]) := by decide +kernel

theorem empty_multiplier :
    run 12 (cfg 0 false [] [true,true] [true,false,true] [] [] []) =
      some (5,[]) := by decide +kernel

theorem zero_multiplicand :
    run 64 (cfg 0 false [true,false,true] [] [false,true] [] [] [true]) =
      some (2,[true]) := by decide +kernel

end UAVProof.TreeBudgetWeightedExamples
