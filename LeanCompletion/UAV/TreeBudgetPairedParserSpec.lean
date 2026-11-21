import LeanCompletion.UAV.TreeBudgetInstanceSpec
import LeanCompletion.UAV.TreeBudgetCertificateRecordsTM2
import LeanCompletion.UAV.TreeBudgetSparseNPBridge

/-! The paired entrance checks syntax and instance validity. Row feasibility is
a later stage, including for records whose multiplicity is zero. -/
namespace UAVProof.A4PairedParser
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetSparseVerifier

def accepted (x y : Bits) : Bool :=
  (parseInstance x).any fun I => (TreeBudgetSparseCodec.decodeCertificate I.data.n y).isSome

def wireAccepted (s : Bits) : Bool := (parseWord s).any fun p => accepted p.1 p.2

theorem wireAccepted_pair (x y : Bits) :
    wireAccepted (TreeBudgetSparseNPBridge.pairWire (x,y)) = accepted x y := by
  simp [wireAccepted,TreeBudgetSparseNPBridge.pairWire,parseWord_append]

/-- Recover the actual saved dimension from the full instance parser, with
its occupied-word bound. No dimension is supplied by the caller. -/
theorem parsed_fields (x : Bits) (I : Instance) (hI : parseInstance x=some I) :
    ∃ a f, TreeBudgetRootFlowSpec.parse x=some a ∧
      TreeBudgetRootFlowSpec.accepted x=true ∧ A4FeeTailSpec.read a.vertices a.rest=some f ∧
      a.vertices=I.data.n ∧ I.data.n.bits.length ≤ x.length := by
  have h : A4FeeTailSpec.accepted x=true := by
    rw [A4FeeTailSpec.accepted_eq_parseInstance,hI]; rfl
  have hh : TreeBudgetRootFlowSpec.accepted x=true ∧
      (TreeBudgetRootFlowSpec.parse x).any
        (fun a => (A4FeeTailSpec.read a.vertices a.rest).isSome)=true := by
    simpa only [A4FeeTailSpec.accepted,Bool.and_eq_true] using h
  obtain ⟨hr,hf⟩ := hh
  obtain ⟨a,ha⟩ := A4FeeTailSpec.root_parse_of_accept x hr
  change (TreeBudgetRootFlowSpec.parse x).any _=true at hf
  simp only [ha,Option.any_some] at hf
  obtain ⟨f,hf⟩ := Option.isSome_iff_exists.mp hf
  obtain ⟨hn,hh,_⟩ := A4FeeTailSpec.root_contract x a ha hr
  have hd := A4FeeTailSpec.parseInstance_finish x a f ha hf hn hh
  rw [hI] at hd
  have raw := (decodeSpecified_fields _ _ I hd.symm).2
  have dim : I.data.n=a.vertices := (decodeRaw_fields _ _ raw).1
  refine ⟨a,f,ha,hr,hf,dim.symm,?_⟩
  rw [dim]
  exact (A4FeeTailSpec.fee_input_bounds x a ha hr).2.1

/-- Eliminate the independent dimension parameter using the parsed input. -/
theorem recordBound_cubic (l w d : ℕ) (hd : d ≤ l) :
    A4CertRecords.recordBound w d ≤ 72*(l+w+1)^3 := by
  have hw : w+1 ≤ l+w+1 := by omega
  have hwd : w+d+1 ≤ l+w+1 := by omega
  have sq := Nat.pow_le_pow_left hw 2
  have prod := Nat.mul_le_mul hw hwd
  have cubic := Nat.mul_le_mul (show w ≤ l+w by omega) sq
  unfold A4CertRecords.recordBound
  nlinarith only [sq,prod,cubic]

def pairBound (n : ℕ) : ℕ := 65614*(n+1)^4

theorem combined_bound (l w d : ℕ) (hd : d ≤ l) :
    (3*l+2) + 65536*(l+1)^4 + 1 + (2*d+2) +
      A4CertRecords.recordBound w d + 1 ≤ pairBound (l+w) := by
  have p4 := Nat.pow_le_pow_left (show l+1 ≤ l+w+1 by omega) 4
  have p34 := Nat.pow_le_pow_right (show 1 ≤ l+w+1 by omega) (by decide : 3 ≤ 4)
  have p14 := Nat.pow_le_pow_right (show 1 ≤ l+w+1 by omega) (by decide : 1 ≤ 4)
  have q := recordBound_cubic l w d hd
  simp only [pow_one] at p14
  unfold pairBound
  nlinarith only [p4,p34,p14,q,hd]

end UAVProof.A4PairedParser
