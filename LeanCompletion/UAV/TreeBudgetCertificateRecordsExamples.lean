import LeanCompletion.UAV.TreeBudgetCertificateRecordsTM2

namespace UAVProof.A4CertRecords
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open Turing StateTransition Turing.TM2.Stmt

set_option synthInstance.maxSize 2048
set_option maxRecDepth 10000

def run : ℕ → Cfg → Option Cfg
  | 0,_ => none
  | fuel+1,c => match machine.step c with
    | none => some c
    | some d => run fuel d

def result (n : ℕ) (y ctx : Bits) (fuel : ℕ) :=
  (run fuel (start n y ctx)).map fun c =>
    (c.var.2,c.stk ctxStack,c.stk (.inr .dim),
      if c.var.2 then some (c.stk savedCount,c.stk savedBody,c.stk cursor) else none)

def accepted (n : ℕ) (y : Bits) :=
  (run 20000 (start n y [true,false])).map fun c => c.var.2

set_option maxRecDepth 150000
set_option maxHeartbeats 32000000

theorem empty_good : accepted 6 (encodeRaw []) = some true := by rfl
theorem empty_trailing : accepted 6 (encodeRaw [] ++ [false]) = some false := by rfl
theorem count_is_not_multiplicity : accepted 1 (encodeRaw [(2^90,[0])]) = some true := by rfl
theorem count_too_large : accepted 1 (encodeNat (2^90) ++ [true,false,true]) = some false := by rfl
theorem second_cut : accepted 2 (encodeNat 2 ++ encodeEntry (7,[3,0]) ++ encodeNat 0 ++ [true]) =
    some false := by rfl
theorem short_row : accepted 2 (encodeRaw [(0,[1])]) = some false := by rfl
theorem long_row : accepted 1 (encodeRaw [(0,[1,0])]) = some false := by rfl
theorem zero_dim_nonempty : accepted 0 (encodeRaw [(4,[]),(0,[])]) = some true := by rfl

def ordered : RawCertificate := [(2,[3,0]),(0,[0,1]),(2,[3,0])]
theorem saved_in_order : result 2 (encodeRaw ordered) [false,true] 3000 =
    some (true,[false,true],(2 : ℕ).bits,
      some (List.replicate 3 true,ordered.flatMap encodeEntry,[])) := by rfl

theorem same_row_different_counts : result 2 (encodeRaw [(7,[3,0]),(2,[3,0])]) [true,false] 3000 =
    some (true,[true,false],(2 : ℕ).bits,
      some (List.replicate 2 true,[(7,[3,0]),(2,[3,0])].flatMap encodeEntry,[])) := by rfl

end UAVProof.A4CertRecords
