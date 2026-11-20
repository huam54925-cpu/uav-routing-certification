import LeanCompletion.UAV.TreeBudgetRootFlowTM2
import LeanCompletion.UAV.TreeBudgetRootFlowSpec

/-! Kernel reductions of the actual composed TM2, beginning with raw bits. -/
namespace UAVProof.TreeBudgetRootFlowExamples
open TreeBudgetBinaryCodec TreeBudgetRootFlowTM2

def observe : ℕ → Cfg → Option (Bool × Bits × Bits × Bits)
  | 0,_ => none
  | fuel+1,c => match machine.step c with
    | none => some (c.var.2,c.stk suffix,c.stk context,c.stk demands)
    | some d => observe fuel d
def acceptsWithin : ℕ → Cfg → Option (Bool × Bits)
  | 0,_ => none
  | fuel+1,c => match machine.step c with
    | none => some (c.var.2,c.stk context)
    | some d => acceptsWithin fuel d
def input (m n r : ℕ) (p h : List ℕ) (t : Bits) := TreeBudgetRootFlowSpec.encode ⟨m,n,r,p,h,t⟩

set_option maxRecDepth 200000
set_option maxHeartbeats 32000000

theorem exclude_root_and_grandchild : observe 40000
    (start (input 2 3 1 [1,1,0] [2,2^80,7] [true]) [false,true]) =
      some (true,[true],[false,true],[2,2^80,7].flatMap encodeNat) := by rfl

theorem root_flow_mismatch : observe 40000
    (start (input 9 3 1 [1,1,0] [2,2^80,7] [true]) [false,true]) =
      some (false,[true],[false,true],[2,2^80,7].flatMap encodeNat) := by rfl

theorem full_carry : observe 40000
    (start (input 256 3 0 [0,0,0] [0,255,1] [true,false]) [true]) =
      some (true,[true,false],[true],[0,255,1].flatMap encodeNat) := by rfl

theorem singleton_large_root : observe 40000
    (start (input 0 1 0 [0] [2^80] []) [false]) =
      some (true,[],[false],[2^80].flatMap encodeNat) := by rfl

/-- A malformed fee prefix is left for the next stage; it is not instance EOF. -/
theorem malformed_fee_tail_preserved : observe 10000
    (start (input 1 2 0 [0,0] [91,1] [true]) [true,false]) =
      some (true,[true],[true,false],[91,1].flatMap encodeNat) := by rfl

theorem short_h : observe 10000 (start (input 0 2 0 [0,0] [0] [true,false]) [true]) =
    some (false,[true,false],[true],[0].flatMap encodeNat) := by rfl

theorem long_h : observe 10000 (start (input 1 2 0 [0,0] [0,1,0] [false]) [true]) =
    some (false,[false],[true],[0,1,0].flatMap encodeNat) := by rfl

def rawH (h : Bits) := TreeBudgetParentPrefix.encode ⟨0,1,0,[0],h⟩

theorem huge_h_count_short_suffix : acceptsWithin 10000
    (start (rawH (encodeNat (2^80) ++ [false])) [true,false])=some (false,[true,false]) := by rfl
theorem truncated_h_field : acceptsWithin 5000
    (start (rawH (encodeNat 1 ++ [true])) [false])=some (false,[false]) := by rfl
theorem noncanonical_h_field : acceptsWithin 5000
    (start (rawH (encodeNat 1 ++ [true,false,false])) [true])=some (false,[true]) := by rfl
theorem invalid_tree_rejected : acceptsWithin 20000
    (start (input 0 4 0 [0,0,3,2] [0,0,0,0] [true]) [false,true])=some (false,[false,true]) := by rfl

def scanFlag : ℕ → TreeBudgetRootFlowScanTM2.Cfg → Option Bool
  | 0,_ => none
  | fuel+1,c => match TreeBudgetRootFlowScanTM2.machine.step c with
    | none => some c.var.2
    | some d => scanFlag fuel d

/-- Equal values with different actual word lengths must compare equal. -/
theorem padded_accumulator_equality : scanFlag 100
    (TreeBudgetRootFlowScanTM2.cfg (TreeBudgetRootFlowScanTM2.entry .finalA)
      {u:=[true,false],m:=[true]})=some true := by rfl

end UAVProof.TreeBudgetRootFlowExamples
