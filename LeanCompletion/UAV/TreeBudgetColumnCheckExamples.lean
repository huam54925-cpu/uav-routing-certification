import LeanCompletion.UAV.TreeBudgetColumnCheckTM2

namespace UAVProof.A4ColumnCheckExamples
open TreeBudgetBinaryCodec TreeBudgetSparseCodec A4ColumnCheck Turing

def run : ℕ → Cfg → Option Cfg
  | 0,_ => none
  | fuel+1,c => match machine.step c with
    | none => some c
    | some d => run fuel d

def input (r : ℕ) (H : List ℕ) (xs : RawCertificate) : Input :=
  ⟨xs.flatMap encodeEntry,List.replicate xs.length true,r.bits,H.flatMap encodeNat,[true,false,true]⟩

def result (r : ℕ) (H : List ℕ) (xs : RawCertificate) :=
  (run 100000 (start (input r H xs))).map (fun c => c.var.2)

set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

theorem root_demand_is_ignored : result 0 [1024] []=some true := by rfl
theorem correct_nonroot_columns : result 0 [7,1,1] [(1,[0,1,0]),(1,[0,0,1])]=some true := by rfl
theorem right_count_wrong_columns : result 0 [0,1,1] [(2,[0,1,0])]=some false := by rfl
theorem repeated_rows_keep_weights : result 0 [0,5] [(2,[0,1]),(3,[0,1])]=some true := by rfl
theorem middle_root_is_skipped : result 1 [2,1024,7] [(1,[2,0,7])]=some true := by rfl
theorem empty_certificate_bad_column : result 0 [0,1] []=some false := by rfl

theorem originals_are_preserved :
    (run 100000 (start (input 0 [0,5] [(2,[0,1]),(3,[0,1])]))).map
      (fun c => (c.var.2,c.stk (wr .body),c.stk (wr .tokens),c.stk (wr .targets),c.stk (wr .ctx)))=
      some (true,[(2,[0,1]),(3,[0,1])].flatMap encodeEntry,[true,true],
        [0,5].flatMap encodeNat,[true,false,true]) := by rfl

end UAVProof.A4ColumnCheckExamples
