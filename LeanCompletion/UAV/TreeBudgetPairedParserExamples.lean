import LeanCompletion.UAV.TreeBudgetPairedParserTM2

namespace UAVProof.A4PairedParserChecks
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetSparseVerifier
open TreeBudgetSparseNPBridge A4PairedParser Turing

def run : ℕ → Cfg → Option Cfg
  | 0, _ => none
  | fuel+1, c => match machine.step c with
    | none => some c
    | some d => run fuel d

def runWire (s : Bits) := run 20000 (initList machine s)
def result (x y : Bits) := (runWire (pairWire (x,y))).map (fun c => c.var.2)

def rootOnly : RawInput := ⟨1,0,[0],[0],[0],[1],0,1⟩
def rootInput := encodeSpecified 0 rootOnly
def zeroRow := encodeRaw [(0,[0])]
def twoVertices : RawInput := ⟨2,0,[0,0],[7,1],[-2,0],[4,3],-3,6⟩
def twoInput := encodeSpecified 1 twoVertices
def records : RawCertificate := [(7,[3,0]),(2,[3,0])]

def instanceWords (c : Cfg) : List Bits :=
  [c.stk (ik (.inl (.inl (.inr (.inr 0))))),
   c.stk (ik A4FeeTailMachine.dimension),
   c.stk (ik (.inl (.inl TreeBudgetParentPrefixTM2.parsedRoot))),
   c.stk (ik A4FeeTailMachine.parents),
   c.stk (ik (.inl TreeBudgetRootFlowTM2.demands)),
   c.stk (ik (.inr (.result .nums))),c.stk (ik (.inr (.result .dens))),
   c.stk (ik (.inr (.result .bnum))),c.stk (ik (.inr (.result .bden))),
   c.stk (ik A4FeeTailMachine.src)]

def certificateWords (c : Cfg) : List Bits :=
  [c.stk (ck (.inr .dim)),c.stk (ck A4CertRecords.savedCount),
   c.stk (ck A4CertRecords.savedBody),c.stk (ck A4CertRecords.cursor)]

set_option maxRecDepth 150000
set_option maxHeartbeats 64000000

theorem empty_records_accept : result rootInput (encodeRaw [])=some true := by rfl
theorem zero_count_row_parses : result rootInput zeroRow=some true := by rfl
theorem empty_records_verify : verify rootInput (encodeRaw [])=true := by decide +kernel
theorem zero_count_row_fails_semantics : verify rootInput zeroRow=false := by decide +kernel

theorem saved_both_banks :
    (runWire (pairWire (twoInput,encodeRaw records))).map
      (fun c => (c.var.2,instanceWords c,certificateWords c)) =
    some (true,
      [Nat.bits 1,Nat.bits 2,Nat.bits 0,[0,0].flatMap encodeNat,[7,1].flatMap encodeNat,
        [-2,0].flatMap encodeInt,[4,3].flatMap encodeNat,encodeInt (-3),encodeNat 6,[]],
      [Nat.bits 2,[true,true],records.flatMap encodeEntry,[]]) := by rfl

theorem wrong_row_size_rejects : result twoInput (encodeRaw [(7,[3])])=some false := by rfl
theorem second_record_cut_rejects :
    result twoInput (encodeNat 2 ++ encodeEntry (7,[3,0]) ++ encodeNat 0 ++ [true])=
      some false := by rfl
theorem certificate_trailing_rejects : result rootInput (encodeRaw [] ++ [false])=some false := by rfl
theorem instance_trailing_rejects : result (rootInput ++ [false]) (encodeRaw [])=some false := by rfl
theorem instance_failure_keeps_certificate :
    (runWire (pairWire (encodeSpecified 1 rootOnly,zeroRow))).map
      (fun c => (c.var.2,c.stk (ck A4CertRecords.savedBody)))=some (false,zeroRow) := by rfl
theorem truncated_outer_rejects : (runWire [true]).map (fun c => c.var.2)=some false := by rfl
theorem empty_instance_rejects : result [] (encodeRaw [])=some false := by rfl

end UAVProof.A4PairedParserChecks
