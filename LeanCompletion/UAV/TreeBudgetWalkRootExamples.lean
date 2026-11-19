import LeanCompletion.UAV.TreeBudgetWalkRootTM2
import LeanCompletion.UAV.TreeBudgetParentWalkExamples

namespace UAVProof.TreeBudgetWalkRootExamples
open TreeBudgetBinaryCodec TreeBudgetWalkRootTM2
open TreeBudgetParentWalkExamples (address)

def observe : ℕ → Cfg → Option Bool
  | 0,_ => none
  | n+1,c => match machine.step c with
    | none => some c.var.2
    | some d => observe n d

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem reaches_root : observe 500 (start [false,true] (address 2 [0,0,1]) (encodeNat 0) []) = some true := by rfl
theorem misses_root : observe 500 (start [false,true] (address 2 [0,2,1]) (encodeNat 0) []) = some false := by rfl
theorem wrong_fixed_point : observe 200 (start [false] (address 0 [1,0]) (encodeNat 0) []) = some false := by rfl
theorem bad_query : observe 45 (start [false] [true] (encodeNat 0) []) = some false := by rfl

end UAVProof.TreeBudgetWalkRootExamples
