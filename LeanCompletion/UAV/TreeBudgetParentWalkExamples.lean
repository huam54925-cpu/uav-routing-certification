import LeanCompletion.UAV.TreeBudgetParentWalkTotal

namespace UAVProof.TreeBudgetParentWalkExamples
open TreeBudgetBinaryCodec TreeBudgetParentWalkTM2

def sample : ℕ → Cfg → Option (Option Bits × Bits)
  | 0, _ => none
  | n+1, c => match machine.step c with
    | some d => sample n d
    | none => some (if c.var.2 then some (c.stk src) else none, c.stk (.inl (.inl 5)))

def address (i : ℕ) (xs : List ℕ) := encodeNat i ++ xs.flatMap encodeNat

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem two_hops :
    sample 500 (cfg 7 (address 3 [0,0,1,2]) [] [] [] [true,false] [true]) =
      some (some (address 1 [0,0,1,2]), [true]) := by rfl

theorem cycle :
    sample 400 (cfg 7 (address 0 [1,0]) [] [] [] [true,true,false] []) =
      some (some (address 1 [1,0]), []) := by rfl

theorem bad_later_index :
    sample 300 (cfg 7 (address 0 [9,0]) [] [] [] [true,false] [false]) =
      some (none,[false]) := by rfl

theorem malformed_address :
    sample 45 (cfg 7 [true] [] [] [] [true] [false,true]) =
      some (none,[false,true]) := by rfl

theorem empty_count :
    sample 2 (cfg 7 [true] [] [] [] [] [false]) = some (some [true],[false]) := by rfl

end UAVProof.TreeBudgetParentWalkExamples
