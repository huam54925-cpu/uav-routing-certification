import LeanCompletion.UAV.TreeBudgetFeeScalingEntry
import LeanCompletion.UAV.TreeBudgetFeeScalingCore

namespace UAVProof.A4FeeScaling.Entry
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open TreeBudgetSparseVerifier TreeBudgetSparseNPBridge TreeBudgetVectorChecker
open Turing StateTransition
set_option synthInstance.maxSize 8192
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def Scaled (I : Instance) (out : Cfg) : Prop :=
  out.stk (wr .fees)=(scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator).toList.flatMap encodeInt ∧
  out.stk (wr .budget)=encodeInt (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator)

theorem saved_fields (x y : Bits) (p : A4PairedParser.Cfg) (I : Instance)
    (hi : parseInstance x=some I) (hs : A4PairedParser.Saved x y p) :
    Fields p.stk (rows I.data.numerators I.data.denominators)
      I.data.budgetNumerator I.data.budgetDenominator := by
  obtain ⟨a,f,ha,hr,hf,_,_⟩ := A4PairedParser.parsed_fields x I hi
  obtain ⟨hnum,hden,hbn,hbd⟩ := parsed_fee_fields x I hi a f ha hr hf
  have h := hs.1 a f ha hr hf
  simpa only [Fields,rows_fst,rows_snd,← hnum,← hden,← hbn,← hbd,
    A4PairedParser.instanceView] using
    (show p.stk (A4PairedParser.ik (.inr (.result .nums)))=f.nums.flatMap encodeInt ∧
      p.stk (A4PairedParser.ik (.inr (.result .dens)))=f.dens.flatMap encodeNat ∧
      p.stk (A4PairedParser.ik (.inr (.result .bnum)))=encodeInt f.budgetNum ∧
      p.stk (A4PairedParser.ik (.inr (.result .bden)))=encodeNat f.budgetDen from
      ⟨h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.1⟩)

theorem output_scaled (saved : A4PairedParser.K → Bits) (I : Instance) :
    Scaled I (halted (none,true) (store (outputData saved
      (rows I.data.numerators I.data.denominators) I.data.budgetNumerator I.data.budgetDenominator))) := by
  constructor
  · simp [Scaled,halted,store,outputData,backwardState,
      formula_scaleFees _ _ _ I.data.positive]
  · have h := budget_scaleBudget I.data.numerators I.data.denominators
      I.data.budgetNumerator I.data.budgetDenominator I.data.budgetPositive
    simpa [halted,store,outputData,backwardState,prefixEnd_value,value] using congrArg encodeInt h

/-- Start at the actual paired-parser return. The two bridge steps are counted;
every stack of the paired parser is preserved, including zero-count records. -/
theorem from_paired_success (x y : Bits) (p : A4PairedParser.Cfg) (I : Instance)
    (hi : parseInstance x=some I) (hb : p.var.2=true)
    (hs : A4PairedParser.Saved x y p) :
    ∃ out, Nonempty (Run (after p) out (coreBound x.length+2)) ∧
      out.l=none ∧ out.var.2=true ∧ Scaled I out ∧
      (∀ k, out.stk (old k)=p.stk k) ∧ A4PairedParser.Saved x y (view out) := by
  have fields := saved_fields x y p I hi hs
  obtain ⟨hn,hm,hnums,hdens,hbn,hbd⟩ := instance_bounds x I hi
  have core := core_run p.stk (rows I.data.numerators I.data.denominators)
    I.data.budgetNumerator I.data.budgetDenominator x.length fields hn hm
    (by simpa only [rows_fst] using hnums) (by simpa only [rows_snd] using hdens) hbn hbd
  have call := call_run sw L.scaling .done (fun _ => [])
    (TreeBudgetRegisterTM2.program instr) program (fun _ => rfl) core
  have run := seq (seq (once (true_step p hb)) call)
    (once (return_step (outputData p.stk (rows I.data.numerators I.data.denominators)
      I.data.budgetNumerator I.data.budgetDenominator)))
  refine ⟨_,⟨weaken run (by omega)⟩,
    rfl,rfl,output_scaled p.stk I,(fun _ => rfl),?_⟩
  exact hs

def totalBound (N : ℕ) := 131072*(N+2)^4

theorem total_bound (l w : ℕ) :
    A4PairedParser.pairBound (l+w)+(coreBound l+2) ≤ totalBound (l+w) := by
  have a := Nat.pow_le_pow_left (show l+w+1 ≤ l+w+2 by omega) 4
  have b := Nat.pow_le_pow_left (show l+2 ≤ l+w+2 by omega) 3
  have c := Nat.pow_le_pow_right (show 1 ≤ l+w+2 by omega) (by decide : 3≤4)
  have d := Nat.one_le_pow 4 (l+w+2) (by omega)
  unfold A4PairedParser.pairBound coreBound totalBound
  nlinarith only [a,b,c,d]

/-- Raw paired input with the same acceptance condition as the parser;
successful output additionally contains canonical scaled fees and budget. -/
theorem scaled_from_init (x y : Bits) :
    ∃ out, Nonempty (Run (initList machine (pairWire (x,y))) out (totalBound (x.length+y.length))) ∧
      out.l=none ∧ out.var.2=A4PairedParser.accepted x y ∧
      A4PairedParser.Saved x y (view out) ∧
      (∀ I, parseInstance x=some I → A4PairedParser.accepted x y=true → Scaled I out) := by
  obtain ⟨p,⟨pre⟩,pl,pv,ps⟩ := A4PairedParser.paired_from_init x y
  have call := call_run pw L.paired .afterPaired (fun _ => [])
    A4PairedParser.program program (fun _ => rfl) pre
  rw [paired_return p pl,← init_eq] at call
  cases hb : p.var.2 with
  | false =>
    have run := seq call (once (false_step p hb))
    refine ⟨_,⟨weaken run ?_⟩,rfl,?_,ps,?_⟩
    · have ht := total_bound x.length y.length; omega
    · exact hb.symm.trans pv
    · intro I hi ht; rw [← pv,hb] at ht; cases ht
  | true =>
    have good : A4PairedParser.accepted x y=true := pv.symm.trans hb
    have someI : (parseInstance x).isSome=true := by
      cases h : parseInstance x <;> simp_all [A4PairedParser.accepted]
    obtain ⟨I,hi⟩ := Option.isSome_iff_exists.mp someI
    obtain ⟨out,⟨run⟩,hl,hv,scaled,keep,saved⟩ := from_paired_success x y p I hi hb ps
    refine ⟨out,⟨weaken (seq call run) (total_bound x.length y.length)⟩,hl,
      hv.trans good.symm,saved,?_⟩
    intro J hj _
    have h : I=J := Option.some.inj (hi.symm.trans hj)
    subst J
    exact scaled

/-- Arbitrary raw outer frames, including truncated framing. -/
theorem scaled_wire_from_init (s : Bits) :
    ∃ out, Nonempty (Run (initList machine s) out (totalBound s.length)) ∧
      out.l=none ∧ out.var.2=A4PairedParser.wireAccepted s ∧
      ∀ x y, parseWord s=some (x,y) →
        A4PairedParser.Saved x y (view out) ∧
        (∀ I, parseInstance x=some I → A4PairedParser.accepted x y=true → Scaled I out) := by
  cases hp : parseWord s with
  | none =>
    obtain ⟨p,⟨pre⟩,pl,pv,_⟩ := A4PairedParser.wire_from_init s
    have hb : p.var.2=false := by simpa [A4PairedParser.wireAccepted,hp] using pv
    have call := call_run pw L.paired .afterPaired (fun _ => [])
      A4PairedParser.program program (fun _ => rfl) pre
    rw [paired_return p pl,← init_eq] at call
    have run := seq call (once (false_step p hb))
    refine ⟨_,⟨weaken run ?_⟩,rfl,?_,?_⟩
    · have ht := total_bound s.length 0; simp only [Nat.add_zero] at ht; omega
    · simp [halted,A4PairedParser.wireAccepted,hp]
    · intro x y h; simp at h
  | some pair =>
    obtain ⟨x,y⟩ := pair
    have he := parseWord_consumed s x y hp
    obtain ⟨out,⟨run⟩,hl,hv,hs,hscaled⟩ := scaled_from_init x y
    have hlen : x.length+y.length ≤ s.length := by
      rw [he,List.length_append,word_length]; omega
    refine ⟨out,⟨weaken (by simpa only [pairWire,← he] using run) ?_⟩,hl,?_,?_⟩
    · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
    · simpa [A4PairedParser.wireAccepted,hp] using hv
    · intro u v huv
      have h := Option.some.inj huv
      cases h
      exact ⟨hs,hscaled⟩

end UAVProof.A4FeeScaling.Entry
