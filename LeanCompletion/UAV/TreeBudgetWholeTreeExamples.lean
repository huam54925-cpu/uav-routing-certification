import LeanCompletion.UAV.TreeBudgetWholeTreeTM2

/-! Kernel reductions of the actual transition function, including a failure
after two successful vertex calls. -/
namespace UAVProof.TreeBudgetWholeTreeExamples
open TreeBudgetBinaryCodec TreeBudgetWholeTreeTM2

def rawStart (parents : List ℕ) (root : ℕ) (ctx : Bits) : Cfg :=
  cfg (entry .count) {body := parents.flatMap encodeNat,root := encodeNat root,ctx := ctx}

def observe : ℕ → Cfg → Option (Bool × Bits × Bits × Bits × ℕ)
  | 0,_ => none
  | fuel+1,c => match machine.step c with
    | none => some (c.var.2,c.stk tableSave,c.stk rootSave,c.stk context,value (c.stk index))
    | some d => observe fuel d

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem singleton : observe 500 (rawStart [0] 0 [false,true]) =
    some (true,[0].flatMap encodeNat,encodeNat 0,[false,true],1) := by rfl

theorem nonzero_root : observe 6000 (rawStart [2,2,2] 2 [true,false]) =
    some (true,[2,2,2].flatMap encodeNat,encodeNat 2,[true,false],3) := by rfl

theorem root_not_fixed : observe 1000 (rawStart [1,0] 0 [false]) =
    some (false,[1,0].flatMap encodeNat,encodeNat 0,[false],0) := by rfl

/-- Vertices 0 and 1 have already passed before vertex 2 exposes the cycle. -/
theorem late_disjoint_cycle : observe 12000 (rawStart [0,0,3,2] 0 [true,true,false]) =
    some (false,[0,0,3,2].flatMap encodeNat,encodeNat 0,[true,true,false],2) := by rfl

end UAVProof.TreeBudgetWholeTreeExamples
