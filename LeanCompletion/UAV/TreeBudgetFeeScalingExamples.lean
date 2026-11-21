import LeanCompletion.UAV.TreeBudgetFeeScalingEntry
import LeanCompletion.UAV.TreeBudgetPairedParserExamples

namespace UAVProof.A4FeeScalingChecks
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetSparseVerifier
open TreeBudgetSparseNPBridge Turing A4FeeScaling A4FeeScaling.Entry

def run : ℕ → Entry.Cfg → Option Entry.Cfg
  | 0,_ => none
  | fuel+1,c => match machine.step c with
    | none => some c
    | some d => run fuel d
def runWire (s : Bits) := run 100000 (initList machine s)
def outputs (x y : Bits) := (runWire (pairWire (x,y))).map
  (fun c => (c.var.2,c.stk (wr .fees),c.stk (wr .budget)))
def result (x y : Bits) := (runWire (pairWire (x,y))).map (fun c => c.var.2)

def repeatedDenominators : RawInput := ⟨3,2,[2,2,2],[1,1,0],[-2,0,3],[2,3,2],-2,4⟩
def carryInput : RawInput := ⟨2,0,[0,0],[0,1],[255,257],[255,1],1,1⟩
def positiveRoot : RawInput := ⟨1,0,[0],[0],[5],[2],3,7⟩

set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

theorem two_vertices_exact :
    outputs A4PairedParserChecks.twoInput (encodeRaw A4PairedParserChecks.records)=
      some (true,[-36,0].flatMap encodeInt,encodeInt (-36)) := by rfl

theorem repeated_denominators_exact :
    outputs (encodeSpecified 2 repeatedDenominators) (encodeRaw [(0,[0,0,0])])=
      some (true,[-48,0,72].flatMap encodeInt,encodeInt (-24)) := by rfl

theorem carries_exact :
    outputs (encodeSpecified 1 carryInput) (encodeRaw [])=
      some (true,[255,65535].flatMap encodeInt,encodeInt 255) := by rfl

theorem positive_root_exact :
    outputs (encodeSpecified 0 positiveRoot) (encodeRaw [])=
      some (true,[35].flatMap encodeInt,encodeInt 6) := by rfl

theorem zero_fields_exact :
    outputs A4PairedParserChecks.rootInput (encodeRaw [])=
      some (true,[0].flatMap encodeInt,encodeInt 0) := by rfl

theorem saved_order_and_counts :
    (runWire (pairWire (A4PairedParserChecks.twoInput,encodeRaw A4PairedParserChecks.records))).map
      (fun c => (A4PairedParserChecks.instanceWords (view c),
        A4PairedParserChecks.certificateWords (view c)))=
    some ([Nat.bits 1,Nat.bits 2,Nat.bits 0,[0,0].flatMap encodeNat,[7,1].flatMap encodeNat,
      [-2,0].flatMap encodeInt,[4,3].flatMap encodeNat,encodeInt (-3),encodeNat 6,[]],
      [Nat.bits 2,[true,true],A4PairedParserChecks.records.flatMap encodeEntry,[]]) := by rfl

theorem zero_count_row_retained :
    (runWire (pairWire (A4PairedParserChecks.rootInput,A4PairedParserChecks.zeroRow))).map
      (fun c => (c.var.2,A4PairedParserChecks.certificateWords (view c)))=
      some (true,[Nat.bits 1,[true],[(0,[0])].flatMap encodeEntry,[]]) := by rfl

theorem truncated_second_record_rejected :
    result A4PairedParserChecks.twoInput
      (encodeNat 2++encodeEntry (7,[3,0])++encodeNat 0++[true])=some false := by rfl

theorem invalid_instance_rejected :
    result (encodeSpecified 1 A4PairedParserChecks.rootOnly) (encodeRaw [])=some false := by rfl

theorem truncated_outer_rejected :
    (runWire [true]).map (fun c => c.var.2)=some false := by rfl

end UAVProof.A4FeeScalingChecks
