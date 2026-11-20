import LeanCompletion.UAV.TreeBudgetFeeTailTM2
import LeanCompletion.UAV.TreeBudgetCanonicalDigits

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetCanonicalDigits Turing StateTransition

abbrev Run (a b : Cfg) (n : ℕ) := EvalsToInTime machine.step a (some b) n
def seq {a b c : Cfg} {x y : ℕ} (h : Run a b x) (g : Run b c y) : Run a c (x+y) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans machine.step x y a b (some c) h g

def streamStore (base : K → Bits) (s a : Bits) : K → Bits :=
  Function.update (Function.update base src s) (.inr .rev) a
def streamCfg (l : L) (base : K → Bits) (s a : Bits) (v : State) : Cfg :=
  ⟨some l,v,streamStore base s a⟩
@[simp] theorem stream_src (base : K → Bits) (s a : Bits) : streamStore base s a src=s := by
  simp [streamStore,src]
@[simp] theorem stream_rev (base : K → Bits) (s a : Bits) : streamStore base s a (.inr .rev)=a := by
  simp [streamStore]
@[simp] theorem stream_update_src (base : K → Bits) (s a t : Bits) :
    Function.update (streamStore base s a) src t=streamStore base t a := by
  funext k
  by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
    simp_all [streamStore,Function.update_apply,src]
@[simp] theorem stream_update_rev (base : K → Bits) (s a b : Bits) :
    Function.update (streamStore base s a) (.inr .rev) b=streamStore base s b := by
  simp [streamStore]

def wordEnd (f : FeeField) (base : K → Bits) : Bool → Bits → Bits → Cfg
  | _,[],a => streamCfg .bad base [] a (none,true)
  | ok,false::s,a => streamCfg (if ok then doneField f else .bad) base s (false::a) (some false,true)
  | _,true::[],a => streamCfg .bad base [] (true::a) (none,true)
  | _,true::b::s,a => wordEnd f base b s (b::true::a)

def word_run (f : FeeField) (base : K → Bits) (ok : Bool) (s a : Bits) (v : State) :
    Run (streamCfg (.marker f ok) base s a v) (wordEnd f base ok s a) (s.length+1) := by
  cases s with
  | nil =>
    apply once
    simp [machine,FinTM2.step,TM2.step,streamCfg,program,readBit,TM2.stepAux,go,wordEnd]
    congr 2
    funext k
    by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
      simp_all [streamStore,Function.update_apply,src]
  | cons bit s =>
    cases bit with
    | false =>
      apply weaken (once ?_) (by simp)
      simp [machine,FinTM2.step,TM2.step,streamCfg,program,readBit,TM2.stepAux,go,wordEnd]
      congr 2
      funext k
      by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
        simp_all [streamStore,Function.update_apply,src]
    | true =>
      have first : machine.step (streamCfg (.marker f ok) base (true::s) a v)=
          some (streamCfg (.digit f) base s (true::a) (some true,true)) := by
        simp [machine,FinTM2.step,TM2.step,streamCfg,program,readBit,TM2.stepAux,go]
        congr 2
        funext k
        by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
          simp_all [streamStore,Function.update_apply,src]
      cases s with
      | nil =>
        have second : machine.step (streamCfg (.digit f) base [] (true::a) (some true,true))=
            some (wordEnd f base ok [true] a) := by
          simp [machine,FinTM2.step,TM2.step,streamCfg,program,readBit,TM2.stepAux,go,wordEnd]
          congr 2
          funext k
          by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
            simp_all [streamStore,Function.update_apply,src]
        exact seq (once first) (once second)
      | cons b s =>
        have second : machine.step (streamCfg (.digit f) base (b::s) (true::a) (some true,true))=
            some (streamCfg (.marker f b) base s (b::true::a) (some b,true)) := by
          cases b <;> simp [machine,FinTM2.step,TM2.step,streamCfg,program,readBit,TM2.stepAux,go]
          all_goals
            congr 2
            funext k
            by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
              simp_all [streamStore,Function.update_apply,src]
        simpa [wordEnd,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          seq (seq (once first) (once second)) (word_run f base b s (b::true::a) (some b,true))
termination_by structural s

theorem wordEnd_framed (f : FeeField) (base : K → Bits) (bs s a : Bits) (ok : Bool) :
    wordEnd f base ok (word bs ++ s) a =
      streamCfg (if lastDigit bs ok then doneField f else .bad) base s ((word bs).reverse++a) (some false,true) := by
  induction bs generalizing a ok with
  | nil => simp [word,wordEnd,lastDigit]; rfl
  | cons b bs ih => simpa [word,wordEnd,lastDigit,List.reverse_append,List.append_assoc] using ih (b::true::a) b

theorem wordEnd_truncated (f : FeeField) (base : K → Bits) (s a : Bits) (ok : Bool)
    (h : parseWord s=none) : (wordEnd f base ok s a).l=some .bad := by
  induction s using parseWord.induct generalizing ok a with
  | case1 => rfl
  | case2 s => simp [parseWord] at h
  | case3 => rfl
  | case4 b s ih =>
    have ht : parseWord s=none := by cases hp : parseWord s <;> simp_all [parseWord]
    exact ih (b::true::a) b ht

theorem wordEnd_kept (f : FeeField) (base : K → Bits) (s a : Bits) (ok : Bool) (k : K)
    (hs : k≠src) (ha : k≠.inr .rev) : (wordEnd f base ok s a).stk k=base k := by
  induction s using parseWord.induct generalizing ok a with
  | case1 => simp [wordEnd,streamCfg,streamStore,hs,ha]
  | case2 s => simp [wordEnd,streamCfg,streamStore,hs,ha]
  | case3 => simp [wordEnd,streamCfg,streamStore,hs,ha]
  | case4 b s ih => exact ih (b::true::a) b

theorem wordEnd_length (f : FeeField) (base : K → Bits) (s a : Bits) (ok : Bool) :
    ((wordEnd f base ok s a).stk src).length+
      ((wordEnd f base ok s a).stk (.inr .rev)).length ≤ s.length+a.length := by
  induction s using parseWord.induct generalizing ok a with
  | case1 => simp [wordEnd,streamCfg]
  | case2 s => simp [wordEnd,streamCfg]; omega
  | case3 => simp [wordEnd,streamCfg]
  | case4 b s ih => simpa [wordEnd,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (b::true::a) b

def readWord (ok : Bool) (s : Bits) : Option (Bits × Bits) := do
  let (bs,t) ← parseWord s
  if lastDigit bs ok then some (word bs,t) else none

theorem wordEnd_read (f : FeeField) (base : K → Bits) (s a : Bits) (ok : Bool) :
    match readWord ok s with
    | none => (wordEnd f base ok s a).l=some .bad
    | some (w,t) => wordEnd f base ok s a=
        streamCfg (doneField f) base t (w.reverse++a) (some false,true) := by
  cases hp : parseWord s with
  | none => simpa [readWord,hp] using wordEnd_truncated f base s a ok hp
  | some pair =>
    obtain ⟨bs,t⟩ := pair
    have he := parseWord_consumed s bs t hp
    subst s
    cases h : lastDigit bs ok <;> simp [readWord,parseWord_append,h,wordEnd_framed,streamCfg]

theorem readWord_true (s : Bits) : readWord true s=(parseNat s).map (fun e => (encodeNat e.1,e.2)) := by
  cases hp : parseWord s with
  | none => simp [readWord,parseNat,hp]
  | some pair =>
    obtain ⟨bs,t⟩ := pair
    cases hl : lastDigit bs true with
    | false => simp [readWord,parseNat,hp,canonical_iff_last,hl]
    | true =>
      have hc := canonical_of_last bs hl
      simp [readWord,parseNat,hp,hl,hc,encodeNat]

theorem lastDigit_false (bs : Bits) : lastDigit bs false=true ↔ lastDigit bs true=true ∧ 0<value bs := by
  cases bs with
  | nil => simp [lastDigit,value]
  | cons b bs =>
    have hsame := lastDigit_seed (b::bs) false true (by simp)
    rw [hsame]
    constructor
    · intro h
      have hc := canonical_of_last (b::bs) h
      have hn : value (b::bs)≠0 := by intro hz; rw [hz,Nat.zero_bits] at hc; contradiction
      exact ⟨h,by omega⟩
    · exact And.left

theorem readWord_false (s : Bits) : readWord false s=
    (parseNat s).bind (fun e => if 0<e.1 then some (encodeNat e.1,e.2) else none) := by
  cases hp : parseWord s with
  | none => simp [readWord,parseNat,hp]
  | some pair =>
    obtain ⟨bs,t⟩ := pair
    cases hl : lastDigit bs true with
    | false =>
      have hf : lastDigit bs false=false := by
        apply Bool.eq_false_iff.mpr
        intro h; have := (lastDigit_false bs).mp h; simp [hl] at this
      simp [readWord,parseNat,hp,canonical_iff_last,hl,hf]
    | true =>
      have hc := canonical_of_last bs hl
      have hf : (lastDigit bs false=true) ↔ 0<value bs := by simp [lastDigit_false,hl]
      simp [readWord,parseNat,hp,hl,hc,encodeNat,hf]

def signedEnd (f : FeeField) (base : K → Bits) (s a : Bits) : Cfg := match s with
  | [] => streamCfg .bad base [] a (none,true)
  | b::s => wordEnd f base (!b) s (b::a)

def signed_run (f : FeeField) (base : K → Bits) (s a : Bits) (v : State) :
    Run (streamCfg (.sign f) base s a v) (signedEnd f base s a) (s.length+2) := by
  cases s with
  | nil =>
    apply weaken (once ?_) (by simp)
    simp [machine,FinTM2.step,TM2.step,streamCfg,program,readBit,TM2.stepAux,go,signedEnd]
    congr 2
    funext k
    by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
      simp_all [streamStore,Function.update_apply,src]
  | cons b s =>
    have first : machine.step (streamCfg (.sign f) base (b::s) a v)=
        some (streamCfg (.marker f (!b)) base s (b::a) (some b,true)) := by
      cases b <;> simp [machine,FinTM2.step,TM2.step,streamCfg,program,readBit,TM2.stepAux,go]
      all_goals
        congr 2
        funext k
        by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
          simp_all [streamStore,Function.update_apply,src]
    exact weaken (seq (once first) (word_run f base (!b) s (b::a) (some b,true))) (by simp; omega)

def readSigned : Bits → Option (Bits × Bits)
  | [] => none
  | b::s => (readWord (!b) s).map (fun e => (b::e.1,e.2))

theorem signedEnd_read (f : FeeField) (base : K → Bits) (s a : Bits) :
    match readSigned s with
    | none => (signedEnd f base s a).l=some .bad
    | some (w,t) => signedEnd f base s a=
        streamCfg (doneField f) base t (w.reverse++a) (some false,true) := by
  cases s with
  | nil => rfl
  | cons b s =>
    have hh := wordEnd_read f base s (b::a) (!b)
    cases hr : readWord (!b) s with
    | none => simpa [readSigned,signedEnd,hr] using hh
    | some pair =>
      obtain ⟨w,t⟩ := pair
      simpa [readSigned,signedEnd,hr,List.reverse_cons,List.append_assoc] using hh

theorem signedEnd_kept (f : FeeField) (base : K → Bits) (s a : Bits) (k : K)
    (hs : k≠src) (ha : k≠.inr .rev) : (signedEnd f base s a).stk k=base k := by
  cases s with
  | nil => simp [signedEnd,streamCfg,streamStore,hs,ha]
  | cons b s => exact wordEnd_kept _ _ _ _ _ _ hs ha

theorem signedEnd_length (f : FeeField) (base : K → Bits) (s a : Bits) :
    ((signedEnd f base s a).stk src).length+
      ((signedEnd f base s a).stk (.inr .rev)).length ≤ s.length+a.length := by
  cases s with
  | nil => simp [signedEnd,streamCfg]
  | cons b s => simpa [signedEnd,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using wordEnd_length f base s (b::a) (!b)

end UAVProof.A4FeeTailMachine
