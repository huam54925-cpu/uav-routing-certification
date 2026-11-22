import LeanCompletion.UAV.TreeBudgetVerifierTM2
import LeanCompletion.UAV.TreeBudgetPairedParserExamples

namespace UAVProof.A4VerifierChecks
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetSparseVerifier TreeBudgetSparseNPBridge
open Turing

def run : ℕ → A4Verifier.Cfg → Option A4Verifier.Cfg
  | 0,_ => none
  | fuel+1,c => match A4Verifier.machine.step c with
    | none => some c
    | some d => run fuel d

def result (x y : Bits) :=
  (run 20000 (initList A4Verifier.machine (pairWire (x,y)))).map (fun out => (out.l.isNone,out.var.2))

def chain : RawInput := ⟨3,0,[0,0,1],[0,1,1],[0,5,-12],[1,1,1],-2,1⟩
def star : RawInput := ⟨3,0,[0,0,0],[0,1,1],[0,0,0],[1,1,1],0,1⟩

set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

theorem negative_later_term_recovers :
    result (encodeSpecified 1 chain) (encodeRaw [(1,[0,1,1])])=some (true,true) := by rfl

theorem valid_rows_counts_and_columns :
    result (encodeSpecified 2 star) (encodeRaw [(1,[0,1,0]),(1,[0,0,1])])=some (true,true) := by rfl

theorem right_total_wrong_columns :
    result (encodeSpecified 2 star) (encodeRaw [(2,[0,1,0])])=some (true,false) := by rfl

theorem valid_empty_certificate :
    result A4PairedParserChecks.rootInput (encodeRaw [])=some (true,true) := by rfl

theorem zero_count_row_checked :
    result A4PairedParserChecks.rootInput (encodeRaw [(0,[0])])=some (true,false) := by rfl

theorem truncated_certificate_rejected :
    result (encodeSpecified 2 star) (encodeNat 2++encodeEntry (1,[0,1,0])++[true])=some (true,false) := by rfl

end UAVProof.A4VerifierChecks
