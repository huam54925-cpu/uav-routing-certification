import LeanCompletion.UAV.TreeBudgetPairedParserRuns

namespace UAVProof.A4PairedParser
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open TreeBudgetSparseNPBridge TreeBudgetSparseVerifier Turing StateTransition

set_option synthInstance.maxSize 4096
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Raw framed input, no preloaded dimension or saved instance fields.
The bound includes splitting, both subprograms, dimension copying and returns. -/
theorem paired_from_init (x y : Bits) :
    ∃ out, Nonempty (Run (initList machine (pairWire (x,y))) out (pairBound (x.length+y.length))) ∧
      out.l=none ∧ out.var.2=accepted x y ∧ Saved x y out := by
  obtain ⟨p,⟨pre⟩,pl,pv,pc,ps⟩ := A4FeeTailMachine.instance_from_init x
  have icall := call_run iw L.instanceCall .afterInstance (base y)
    A4FeeTailMachine.program program (fun _ => rfl) pre
  rw [instance_return p y pl] at icall
  have front := seq (split_run x y) icall
  cases hi : parseInstance x with
  | none =>
    have hb : p.var.2=false := by simpa only [hi,Option.isSome_none] using pv
    have run := seq front (once (instance_false p y hb))
    refine ⟨_,⟨weaken run ?_⟩,rfl,?_,?_,pc,?_⟩
    · have h := combined_bound x.length y.length 0 (Nat.zero_le _)
      omega
    · simp [stopped,accepted,hi]
    · intro a f ha hr hf
      exact ps a f ha hr hf
    · intro I hI
      simp [hi] at hI
  | some I =>
    obtain ⟨a,f,ha,hr,hf,hd,hbound⟩ := parsed_fields x I hi
    have hn : p.stk A4FeeTailMachine.dimension=I.data.n.bits := by
      simpa only [hd] using (ps a f ha hr hf).2.1
    have hb : p.var.2=true := by simpa only [hi,Option.isSome_some] using pv
    have loadRun := dimension_run p.stk I.data.n y hn
    obtain ⟨q,⟨qr⟩,ql,qv,_,qd,qs⟩ := A4CertRecords.records_polynomial I.data.n y []
    have ccall := call_run cw L.recordsCall .afterRecords (store p.stk (certBase y))
      A4CertRecords.program program (fun _ => rfl) qr
    have run := seq (seq (seq (seq front (once (instance_true p y hb))) loadRun) ccall)
      (once (records_return p.stk y q ql))
    refine ⟨_,⟨weaken run (combined_bound _ _ _ hbound)⟩,rfl,?_,?_,pc,?_⟩
    · simpa only [stopped,accepted,hi,Option.any_some] using qv
    · intro a' f' ha' hr' hf'
      exact ps a' f' ha' hr' hf'
    · intro J hJ
      have he : I=J := Option.some.inj (hi.symm.trans hJ)
      subst J
      exact ⟨hn,qd,qs⟩

/-- Totality also covers malformed outer frames, with a bound depending only
on the actual raw tape. Successful frames retain the paired output contract. -/
theorem wire_from_init (s : Bits) :
    ∃ out, Nonempty (Run (initList machine s) out (pairBound s.length)) ∧
      out.l=none ∧ out.var.2=wireAccepted s ∧
      ∀ x y, parseWord s=some (x,y) → Saved x y out := by
  cases hp : parseWord s with
  | none =>
    have a := split_truncated s hp
    have b := once (bad_step (tapes framePorts (fun _ => []) [] [] []) (none,true))
    have run := seq a b
    refine ⟨_,⟨weaken run ?_⟩,rfl,?_,?_⟩
    · have h := Nat.pow_le_pow_right (show 1 ≤ s.length+1 by omega) (by decide : 1 ≤ 4)
      simp only [pow_one] at h
      unfold pairBound
      omega
    · simp [stopped,wireAccepted,hp]
    · intro x y h
      simp at h
  | some pair =>
    obtain ⟨x,y⟩ := pair
    have he := parseWord_consumed s x y hp
    obtain ⟨out,⟨run⟩,hl,hv,hs⟩ := paired_from_init x y
    have len : x.length+y.length ≤ s.length := by
      rw [he,List.length_append,word_length]; omega
    refine ⟨out,⟨weaken (by simpa only [pairWire,← he] using run) ?_⟩,hl,?_,?_⟩
    · exact Nat.mul_le_mul_left 65614 (Nat.pow_le_pow_left (by omega) 4)
    · simpa only [wireAccepted,hp,Option.any_some] using hv
    · intro u v huv
      have eq := Option.some.inj huv
      cases eq
      exact hs

end UAVProof.A4PairedParser
