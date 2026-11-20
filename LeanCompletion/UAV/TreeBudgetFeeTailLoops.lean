import LeanCompletion.UAV.TreeBudgetFeeTailFields

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition

def groupField (g : Bool) : FeeField := if g then .dens else .nums
def groupRead (g : Bool) : Parser Bits := if g then readWord false else readSigned
def groupEnd (g : Bool) (base : K → Bits) (s a : Bits) : Cfg :=
  if g then wordEnd .dens base false s a else signedEnd .nums base s a
def groupEntry (g : Bool) : L := if g then .marker .dens false else .sign .nums

def group_run (g : Bool) (base : K → Bits) (s a : Bits) (v : State) :
    Run (streamCfg (groupEntry g) base s a v) (groupEnd g base s a) (s.length+2) := by
  cases g
  · exact signed_run _ _ _ _ _
  · exact weaken (word_run _ _ _ _ _ _) (by omega)

theorem group_read (g : Bool) (base : K → Bits) (s a : Bits) :
    match groupRead g s with
    | none => (groupEnd g base s a).l=some .bad
    | some (w,t) => groupEnd g base s a=
        streamCfg (.more g) base t (w.reverse++a) (some false,true) := by
  cases g
  · exact signedEnd_read _ _ _ _
  · exact wordEnd_read _ _ _ _ _

theorem group_kept (g : Bool) (base : K → Bits) (s a : Bits) (k : K)
    (hs : k≠src) (ha : k≠.inr .rev) : (groupEnd g base s a).stk k=base k := by
  cases g
  · exact signedEnd_kept _ _ _ _ _ hs ha
  · exact wordEnd_kept _ _ _ _ _ _ hs ha

theorem group_length (g : Bool) (base : K → Bits) (s a : Bits) :
    ((groupEnd g base s a).stk src).length+
      ((groupEnd g base s a).stk (.inr .rev)).length ≤ s.length+a.length := by
  cases g
  · exact signedEnd_length _ _ _ _
  · exact wordEnd_length _ _ _ _ _

theorem readWord_consumed (ok : Bool) (s w t : Bits) (h : readWord ok s=some (w,t)) : s=w++t := by
  simp only [readWord,bind,Option.bind_eq_some_iff] at h
  obtain ⟨⟨bs,u⟩,hp,h⟩ := h
  dsimp only at h
  split at h
  · cases h
    exact parseWord_consumed _ _ _ hp
  · contradiction

theorem readSigned_consumed (s w t : Bits) (h : readSigned s=some (w,t)) : s=w++t := by
  cases s with
  | nil => simp [readSigned] at h
  | cons b s =>
    simp only [readSigned,Option.map_eq_some_iff] at h
    obtain ⟨⟨v,u⟩,hp,h⟩ := h
    cases h
    rw [readWord_consumed _ _ _ _ hp]
    rfl

theorem group_consumed (g : Bool) (s w t : Bits) (h : groupRead g s=some (w,t)) : s=w++t := by
  cases g
  · exact readSigned_consumed _ _ _ h
  · exact readWord_consumed _ _ _ _ h

theorem groupMany_consumed (g : Bool) (n : ℕ) (s : Bits) (ws : List Bits) (t : Bits)
    (h : parseMany (groupRead g) n s=some (ws,t)) : s=ws.flatten++t := by
  induction n generalizing s ws with
  | zero =>
    simp only [parseMany,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    rfl
  | succ n ih =>
    simp only [parseMany,bind,Option.bind_eq_some_iff] at h
    obtain ⟨⟨w,u⟩,hw,⟨⟨vs,r⟩,ht,he⟩⟩ := h
    cases he
    rw [group_consumed g s w u hw,ih u vs ht]
    simp [List.append_assoc]

def tickBase (base : K → Bits) (n : ℕ) : K → Bits := Function.update base (.inr .ticks) (List.replicate n true)
def loopCfg (g : Bool) (base : K → Bits) (n : ℕ) (s a : Bits) (v : State) : Cfg :=
  streamCfg (.more g) (tickBase base n) s a v

def loopEnd (g : Bool) (base : K → Bits) : ℕ → Bits → Bits → Cfg
  | 0,s,a => streamCfg (.flush (groupField g)) (tickBase base 0) s a (none,true)
  | n+1,s,a => match groupRead g s with
    | none => groupEnd g (tickBase base n) s a
    | some (w,t) => loopEnd g base n t (w.reverse++a)

@[simp] theorem stream_ticks (base : K → Bits) (n : ℕ) (s a : Bits) :
    streamStore (tickBase base n) s a (.inr .ticks)=List.replicate n true := by
  simp [streamStore,tickBase,src]

@[simp] theorem update_ticks (base : K → Bits) (n : ℕ) (s a : Bits) (m : ℕ) :
    Function.update (streamStore (tickBase base n) s a) (.inr .ticks) (List.replicate m true)=
      streamStore (tickBase base m) s a := by
  funext k
  by_cases ht : k=Sum.inr Aux.ticks <;> by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
    simp_all [streamStore,tickBase,Function.update_apply,src]

def loop_run (g : Bool) (base : K → Bits) (n : ℕ) (s a : Bits) (v : State) :
    Run (loopCfg g base n s a v) (loopEnd g base n s a) ((n+1)*(s.length+3)) := by
  induction n generalizing s a v with
  | zero =>
    apply weaken (once ?_) (by simp)
    simp [machine,FinTM2.step,TM2.step,loopCfg,streamCfg,program,TM2.stepAux,go,loopEnd,groupField]
    congr 2
    funext k
    by_cases ht : k=Sum.inr Aux.ticks <;> by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
      simp_all [streamStore,tickBase,Function.update_apply,src]
  | succ n ih =>
    have first : machine.step (loopCfg g base (n+1) s a v)=
        some (streamCfg (groupEntry g) (tickBase base n) s a (some true,true)) := by
      simp [machine,FinTM2.step,TM2.step,loopCfg,streamCfg,program,TM2.stepAux,go,groupEntry,List.replicate_succ]
      congr 2
      funext k
      by_cases ht : k=Sum.inr Aux.ticks <;> by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
        simp_all [streamStore,tickBase,Function.update_apply,src]
    have run := seq (once first) (group_run g (tickBase base n) s a (some true,true))
    have contract := group_read g (tickBase base n) s a
    cases hp : groupRead g s with
    | none =>
      exact weaken (by simpa [loopEnd,hp] using run) (by nlinarith)
    | some pair =>
      obtain ⟨w,t⟩ := pair
      simp only [hp] at contract
      rw [contract] at run
      have next := ih t (w.reverse++a) (some false,true)
      have he := group_consumed g s w t hp
      have ht : t.length ≤ s.length := by rw [he,List.length_append]; omega
      exact weaken (by simpa [loopEnd,hp,loopCfg] using seq run next) (by nlinarith)

theorem loop_read (g : Bool) (base : K → Bits) (n : ℕ) (s a : Bits) :
    match parseMany (groupRead g) n s with
    | none => (loopEnd g base n s a).l=some .bad
    | some (ws,t) => loopEnd g base n s a=
        streamCfg (.flush (groupField g)) (tickBase base 0) t (ws.flatten.reverse++a) (none,true) := by
  induction n generalizing s a with
  | zero => simp [parseMany,loopEnd]
  | succ n ih =>
    have contract := group_read g (tickBase base n) s a
    cases hp : groupRead g s with
    | none => simpa [parseMany,loopEnd,hp] using contract
    | some pair =>
      obtain ⟨w,t⟩ := pair
      have next := ih t (w.reverse++a)
      cases ht : parseMany (groupRead g) n t with
      | none => simpa [parseMany,loopEnd,hp,ht] using next
      | some pair =>
        obtain ⟨ws,u⟩ := pair
        simpa [parseMany,loopEnd,hp,ht,List.reverse_append,List.append_assoc] using next

theorem loop_kept (g : Bool) (base : K → Bits) (n : ℕ) (s a : Bits) (k : K)
    (hs : k≠src) (ha : k≠.inr .rev) (ht : k≠.inr .ticks) :
    (loopEnd g base n s a).stk k=base k := by
  induction n generalizing s a with
  | zero => simp [loopEnd,streamCfg,streamStore,tickBase,hs,ha,ht]
  | succ n ih =>
    cases hp : groupRead g s with
    | none => simpa [loopEnd,hp,tickBase,ht] using group_kept g (tickBase base n) s a k hs ha
    | some pair => simpa [loopEnd,hp] using ih pair.2 (pair.1.reverse++a)

end UAVProof.A4FeeTailMachine
