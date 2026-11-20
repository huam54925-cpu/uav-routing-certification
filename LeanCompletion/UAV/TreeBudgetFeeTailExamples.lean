import LeanCompletion.UAV.TreeBudgetFeeTailTM2

namespace UAVProof.A4FeeTailChecks
open TreeBudgetBinaryCodec A4FeeTailSpec A4FeeTailMachine

def f : Fields := ⟨[-2,0],[4,3],-3,6⟩
def xraw : RawInput := ⟨2,0,[0,0],[7,1],f.nums,f.dens,f.budgetNum,f.budgetDen⟩
def ctx : Bits := [true,false,true]

def outputs (out : Cfg) : List Bits := [.nums,.dens,.bnum,.bden].map
  (fun (k : FeeField) => out.stk (.inr (.result k)))

def snapshot (out : Cfg) := (out.var.2,out.stk context,outputs out)

set_option maxRecDepth 150000
set_option maxHeartbeats 32000000

theorem saved_outputs : (observe 500 (prepared 2 [0,0] (wire f) ctx)).map snapshot =
    some (true,ctx,[f.nums.flatMap encodeInt, f.dens.flatMap encodeNat,
      encodeInt f.budgetNum, encodeNat f.budgetDen]) := by rfl

theorem rejects_zero_denominator :
    (observe 500 (prepared 2 [0,0] (wire {f with dens := [2,0]}) ctx)).map
      (fun c => (c.var.2,c.stk context)) = some (false,ctx) := by rfl

theorem rejects_trailing :
    (observe 500 (prepared 2 [0,0] (wire f ++ [false]) ctx)).map
      (fun c => (c.var.2,c.stk context)) = some (false,ctx) := by rfl

theorem raw_start_accepts :
    (observe 20000 (start (TreeBudgetSparseVerifier.encodeSpecified 1 xraw) ctx)).map snapshot =
    some (true,ctx,[f.nums.flatMap encodeInt,f.dens.flatMap encodeNat,
      encodeInt f.budgetNum,encodeNat f.budgetDen]) := by rfl

/-- An extra instance bit is rejected even when the certificate context is valid and nonempty. -/
theorem raw_start_rejects_trailing :
    (observe 20000 (start (TreeBudgetSparseVerifier.encodeSpecified 1 xraw ++ [false]) ctx)).map
      (fun c => (c.var.2,c.stk context)) = some (false,ctx) := by rfl

theorem standard_init_accepts :
    (observe 20000 (Turing.initList machine (TreeBudgetSparseVerifier.encodeSpecified 1 xraw))).map
      (fun c => (c.var.2,c.stk context)) = some (true,[]) := by rfl

theorem raw_start_wrong_routes :
    (observe 20000 (start (TreeBudgetSparseVerifier.encodeSpecified 0 xraw) ctx)).map
      (fun c => (c.var.2,c.stk context)) = some (false,ctx) := by rfl


end UAVProof.A4FeeTailChecks
