import LeanCompletion.UAV.TreeBudgetFeeTailFields

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition

/-- Reading a complete frame charges exactly its consumed bits, independently of the tail. -/
def word_run_framed (f : FeeField) (base : K → Bits) (bs s a : Bits) (ok : Bool) (v : State) :
    Run (streamCfg (.marker f ok) base (word bs ++ s) a v)
      (wordEnd f base ok (word bs ++ s) a) (word bs).length := by
  induction bs generalizing a ok v with
  | nil =>
    apply once
    simp [machine,FinTM2.step,TM2.step,streamCfg,program,readBit,TM2.stepAux,go,word,wordEnd]
    congr 2
    funext k
    by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;> simp_all [streamStore,Function.update_apply,src]
  | cons b bs ih =>
    have first : machine.step (streamCfg (.marker f ok) base (word (b::bs) ++ s) a v)=
        some (streamCfg (.digit f) base (b::(word bs ++ s)) (true::a) (some true,true)) := by
      simp [machine,FinTM2.step,TM2.step,streamCfg,program,readBit,TM2.stepAux,go,word]
      congr 2
      funext k
      by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;> simp_all [streamStore,Function.update_apply,src]
    have second : machine.step (streamCfg (.digit f) base (b::(word bs ++ s)) (true::a) (some true,true))=
        some (streamCfg (.marker f b) base (word bs ++ s) (b::true::a) (some b,true)) := by
      cases b <;> simp [machine,FinTM2.step,TM2.step,streamCfg,program,readBit,TM2.stepAux,go]
      all_goals
        congr 2
        funext k
        by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;> simp_all [streamStore,Function.update_apply,src]
    convert seq (seq (once first) (once second)) (ih (b::true::a) b (some b,true)) using 1 <;>
      simp [word,wordEnd] <;> omega

def word_run_success (f : FeeField) (base : K → Bits) (ok : Bool) (s a : Bits) (v : State)
    (w t : Bits) (h : readWord ok s=some (w,t)) :
    Run (streamCfg (.marker f ok) base s a v) (wordEnd f base ok s a) w.length := by
  cases hp : parseWord s with
  | none => simp [readWord,hp] at h
  | some pair =>
    obtain ⟨bs,u⟩ := pair
    cases hl : lastDigit bs ok with
    | false => simp [readWord,hp,hl] at h
    | true =>
      have eq : (word bs,u)=(w,t) := by simpa [readWord,hp,hl] using h
      cases eq
      have he := parseWord_consumed s bs t hp
      subst s
      exact word_run_framed f base bs t a ok v

def signed_run_success (f : FeeField) (base : K → Bits) (s a : Bits) (v : State)
    (w t : Bits) (h : readSigned s=some (w,t)) :
    Run (streamCfg (.sign f) base s a v) (signedEnd f base s a) w.length := by
  cases s with
  | nil => simp [readSigned] at h
  | cons b s =>
    cases hr : readWord (!b) s with
    | none => simp [readSigned,hr] at h
    | some pair =>
      obtain ⟨bs,u⟩ := pair
      have eq : (b::bs,u)=(w,t) := by simpa [readSigned,hr] using h
      cases eq
      have first : machine.step (streamCfg (.sign f) base (b::s) a v)=
          some (streamCfg (.marker f (!b)) base s (b::a) (some b,true)) := by
        cases b <;> simp [machine,FinTM2.step,TM2.step,streamCfg,program,readBit,TM2.stepAux,go]
        all_goals
          congr 2
          funext k
          by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;> simp_all [streamStore,Function.update_apply,src]
      simpa [signedEnd,Nat.add_comm] using
        seq (once first) (word_run_success f base (!b) s (b::a) (some b,true) bs t hr)

end UAVProof.A4FeeTailMachine
