import LeanCompletion.UAV.TreeBudgetSemanticRegisterTM2

namespace UAVProof.TreeBudgetSemanticRegisterTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open Turing StateTransition

variable {K Λ : Type} [DecidableEq K]

theorem tapes_update (p : Ports K) (s : K → Bits) (a b : Bits) (ht : s p.scratch=[]) :
    tapes p s a [] b=Function.update (Function.update s p.src a) p.dst b := by
  funext k
  by_cases hd : k=p.dst
  · subst k; simp
  · by_cases hs : k=p.src
    · subst k; simp [tapes,Function.update_apply,Ne.symm p.dst_ne_src]
    · by_cases hr : k=p.scratch <;> simp_all [tapes,Function.update_apply]

theorem tapes_self (p : Ports K) (s : K → Bits) (ht : s p.scratch=[]) :
    tapes p s (s p.src) [] (s p.dst)=s := by
  rw [tapes_update p s _ _ ht]
  simp

variable (I : Λ → Instr K Λ)

def copy_run (l next : Λ) (p : Ports K) (framed : Bool) (h : I l=.copy p framed next)
    (s : K → Bits) (ht : s p.scratch=[]) :
    Run I (cfg l s)
      (cfg next (Function.update s p.dst ((if framed then word (s p.src) else s p.src)++s p.dst)))
      (2*(s p.src).length+3) := by
  have a : TM2.step (program I) (cfg l s)=
      some (TreeBudgetStackRoutine.conf p s (.stack l .reverse) (s p.src) [] (s p.dst)) := by
    simp [program,h,cfg,TM2.step,TM2.stepAux,TreeBudgetStackRoutine.jump,
      TreeBudgetStackRoutine.conf,tapes_self p s ht]
  have b := TreeBudgetStackRoutine.copy_run p s (Label.stack l) (.pc next) framed (program I)
    (by intro ph; simp [program,h]) (s p.src) (s p.dst)
  have run := prepend a b
  simpa only [TreeBudgetStackRoutine.conf,tapes_update p s _ _ ht,Function.update_eq_self,
    show 2*(s p.src).length+2+1=2*(s p.src).length+3 by omega] using run

def clear_run (l next : Λ) (p : Ports K) (h : I l=.clear p next)
    (s : K → Bits) (ht : s p.scratch=[]) :
    Run I (cfg l s) (cfg next (Function.update s p.src [])) ((s p.src).length+2) := by
  have a : TM2.step (program I) (cfg l s)=
      some (TreeBudgetStackRoutine.conf p s (.stack l .clear) (s p.src) [] (s p.dst)) := by
    simp [program,h,cfg,TM2.step,TM2.stepAux,TreeBudgetStackRoutine.jump,
      TreeBudgetStackRoutine.conf,tapes_self p s ht]
  have b := TreeBudgetStackRoutine.clear_run p s (Label.stack l) (.pc next) false (program I)
    (by intro ph; simp [program,h]) (s p.src) [] (s p.dst)
  have he : tapes p s [] [] (s p.dst)=Function.update s p.src [] := by
    rw [tapes_update p s _ _ ht]
    apply Function.update_eq_self_iff.mpr
    simp [p.dst_ne_src]
  simp only [TreeBudgetStackRoutine.conf,he] at b
  exact weaken (prepend a b) (by omega)

def inc_run (l next : Λ) (p : Ports K) (h : I l=.inc p next)
    (s : K → Bits) (ht : s p.scratch=[]) :
    Run I (cfg l s)
      (cfg next (Function.update s p.src (TreeBudgetStackRoutine.increment (s p.src))))
      (2*(s p.src).length+3) := by
  have a : TM2.step (program I) (cfg l s)=
      some (TreeBudgetStackRoutine.conf p s (.stack l .carry) (s p.src) [] (s p.dst)) := by
    simp [program,h,cfg,TM2.step,TM2.stepAux,TreeBudgetStackRoutine.jump,
      TreeBudgetStackRoutine.conf,tapes_self p s ht]
  have b := TreeBudgetStackRoutine.increment_run p s (Label.stack l) (.pc next) false (program I)
    (by intro ph; simp [program,h]) (s p.src) [] (s p.dst)
  have he : tapes p s (TreeBudgetStackRoutine.increment (s p.src)) [] (s p.dst)=
      Function.update s p.src (TreeBudgetStackRoutine.increment (s p.src)) := by
    rw [tapes_update p s _ _ ht]
    apply Function.update_eq_self_iff.mpr
    simp [p.dst_ne_src]
  simpa only [List.reverse_nil,List.nil_append,List.length_nil,Nat.add_zero,
    TreeBudgetStackRoutine.conf,he,
    show 2*(s p.src).length+2+1=2*(s p.src).length+3 by omega] using prepend a b

def read_run (l next : Λ) (p : Ports K) (h : I l=.read p next)
    (s : K → Bits) (u t : Bits) (hs : s p.src=word u++t)
    (ht : s p.scratch=[]) (hd : s p.dst=[]) :
    Run I (cfg l s) (cfg next (Function.update (Function.update s p.src t) p.dst u))
      (3*u.length+3) := by
  have a : TM2.step (program I) (cfg l s)=
      some (TreeBudgetFrameRoutineTM2.cfg p s (.read l .marker) none true (word u++t) [] []) := by
    have he : tapes p s (word u++t) [] []=s := by
      simpa only [hs,hd] using tapes_self p s ht
    simp [program,h,cfg,TM2.step,TM2.stepAux,TreeBudgetStackRoutine.jump,
      TreeBudgetFrameRoutineTM2.cfg,he]
  have b := framed_run p s (Label.read l) (.pc next) .bad false (program I)
    (by intro ph; simp [program,h]) u t none true [] []
  have run := prepend a b
  simpa only [Bool.not_false,Bool.true_or,ite_true,List.reverse_nil,List.nil_append,
    List.append_nil,List.length_nil,Nat.add_zero,TreeBudgetFrameRoutineTM2.cfg,
    tapes_update p s _ _ ht,show 3*u.length+2+1=3*u.length+3 by omega] using run

def emit_run (l next : Λ) (p : Ports K) (sg : K) (h : I l=.emit p sg next)
    (s : K → Bits) (b : Bool) (tail : Bits) (hs : s sg=b::tail)
    (ht : s p.scratch=[]) (hn : sg≠p.src ∧ sg≠p.scratch ∧ sg≠p.dst) :
    Run I (cfg l s)
      (cfg next (Function.update (Function.update (Function.update s sg tail) p.src []) p.dst
        (encodeInt (TreeBudgetSignedWordTM2.signed b (value (s p.src)))++s p.dst)))
      (2*(s p.src).length+3) := by
  let t := Function.update s sg tail
  have hsrc : t p.src=s p.src := by simp [t,Ne.symm hn.1]
  have htmp : t p.scratch=[] := by simp [t,Ne.symm hn.2.1,ht]
  have hdst : t p.dst=s p.dst := by simp [t,Ne.symm hn.2.2]
  have a : TM2.step (program I) (cfg l s)=
      some (TreeBudgetFrameRoutineTM2.cfg p t (.emit l .reverse) none b (t p.src) [] (t p.dst)) := by
    simp [program,h,cfg,TM2.step,TM2.stepAux,hs,TreeBudgetFrameRoutineTM2.cfg,tapes_self p t htmp,t]
  have run := TreeBudgetSignedWordTM2.write_run p t (Label.emit l) (.pc next) (program I)
    (by intro ph; simp [program,h]) (t p.src) (t p.dst) b
  have allRun := prepend a run
  simpa only [TreeBudgetFrameRoutineTM2.cfg,tapes_update p t _ _ htmp,hsrc,hdst,
    show 2*(s p.src).length+2+1=2*(s p.src).length+3 by omega] using allRun

def mul_run (l next : Λ) (w : Wiring (Fin 6) K) (h : I l=.mul w next)
    (base : K → Bits) (u v ctx : Bits) :
    Run I (cfg l (bank w base (TreeBudgetWeightedTM2.cfg 0 false u v [] [] [] ctx).stk))
      (cfg next (bank w base (TreeBudgetWeightedTM2.stopped
        (TreeBudgetWeightedTM2.weighted u v []) ctx).stk))
      (16*(u.length+v.length+1)^2+3) := by
  let input := TreeBudgetWeightedTM2.cfg 0 false u v [] [] [] ctx
  have a : TM2.step (program I) (cfg l (bank w base input.stk))=
      some (embed w (Label.mul l) (.done next) base input) := by
    simp [program,h,cfg,TM2.step,TM2.stepAux,embed,input,TreeBudgetWeightedTM2.cfg]
  have run := call_run w (Label.mul l) (.done next) base TreeBudgetWeightedTM2.program
    (program I) (by intro ph; simp [program,h]) (TreeBudgetWeightedTM2.product_run u v ctx)
  have last : TM2.step (program I) (embed w (Label.mul l) (.done next) base
      (TreeBudgetWeightedTM2.stopped (TreeBudgetWeightedTM2.weighted u v []) ctx))=
      some (cfg next (bank w base (TreeBudgetWeightedTM2.stopped
        (TreeBudgetWeightedTM2.weighted u v []) ctx).stk)) := by
    simp [program,cfg,TM2.step,TM2.stepAux,embed,TreeBudgetWeightedTM2.stopped,
      TreeBudgetWeightedTM2.cfg,TreeBudgetStackRoutine.jump]
  exact weaken (seq I (prepend a run) (once last)) (by omega)

def bit_run (l next : Λ) (src dst : K) (h : I l=.bit src dst next)
    (s : K → Bits) (b : Bool) (t : Bits) (hs : s src=b::t) (hne : dst≠src) :
    Run I (cfg l s) (cfg next (Function.update (Function.update s src t) dst (b::s dst))) 1 := by
  apply once
  simp [program,h,cfg,TM2.step,TM2.stepAux,hs,hne,TreeBudgetStackRoutine.jump]

def push_run (l next : Λ) (dst : K) (b : Bool) (h : I l=.push dst b next) (s : K → Bits) :
    Run I (cfg l s) (cfg next (Function.update s dst (b::s dst))) 1 := by
  apply once
  simp [program,h,cfg,TM2.step,TM2.stepAux,TreeBudgetStackRoutine.jump]

def test_run (l empty more : Λ) (src : K) (h : I l=.test src empty more) (s : K → Bits) :
    Run I (cfg l s) (cfg (if (s src).isEmpty then empty else more) s) 1 := by
  apply once
  cases hs : s src <;> simp [program,h,cfg,TM2.step,TM2.stepAux,hs,TreeBudgetStackRoutine.jump]

def halt_run (l : Λ) (h : I l=.halt) (s : K → Bits) : Run I (cfg l s) (stopped s) 1 := by
  apply once
  simp [program,h,cfg,stopped,TM2.step,TM2.stepAux]

def weighted_run (l next : Λ) (w : Wiring (Fin 6) K) (h : I l=.weighted w next)
    (base : K → Bits) (u v a ctx : Bits) :
    Run I (cfg l (bank w base (TreeBudgetWeightedTM2.cfg 0 false u v a [] [] ctx).stk))
      (cfg next (bank w base (TreeBudgetWeightedTM2.stopped
        (TreeBudgetWeightedTM2.weighted u v a) ctx).stk))
      (16*(u.length+v.length+a.length+1)^2+3) := by
  let input := TreeBudgetWeightedTM2.cfg 0 false u v a [] [] ctx
  have first : TM2.step (program I) (cfg l (bank w base input.stk))=
      some (embed w (Label.weighted l) (.done next) base input) := by
    simp [program,h,cfg,TM2.step,TM2.stepAux,embed,input,TreeBudgetWeightedTM2.cfg]
  have run := call_run w (Label.weighted l) (.done next) base TreeBudgetWeightedTM2.program
    (program I) (by intro ph; simp [program,h]) (TreeBudgetWeightedTM2.update_halts u v a ctx)
  have last : TM2.step (program I) (embed w (Label.weighted l) (.done next) base
      (TreeBudgetWeightedTM2.stopped (TreeBudgetWeightedTM2.weighted u v a) ctx))=
      some (cfg next (bank w base (TreeBudgetWeightedTM2.stopped
        (TreeBudgetWeightedTM2.weighted u v a) ctx).stk)) := by
    simp [program,cfg,TM2.step,TM2.stepAux,embed,TreeBudgetWeightedTM2.stopped,
      TreeBudgetWeightedTM2.cfg,TreeBudgetStackRoutine.jump]
  exact weaken (seq I (prepend first run) (once last)) (by omega)

def add_run (l next : Λ) (w : Wiring (Fin 4) K) (h : I l=.add w next)
    (base : K → Bits) (u v : Bits) :
    Run I (cfg l (bank w base (TreeBudgetAddWordsTM2.cfg 0 none false u v [] []).stk))
      (cfg next (bank w base (TreeBudgetAddWordsTM2.done
        (TreeBudgetAddWordsTM2.addWords u v false)).stk))
      (2*(u.length+v.length)+6) := by
  let input := TreeBudgetAddWordsTM2.cfg 0 none false u v [] []
  have first : TM2.step (program I) (cfg l (bank w base input.stk))=
      some (embed w (Label.add l) (.done next) base input) := by
    simp [program,h,cfg,TM2.step,TM2.stepAux,embed,input,TreeBudgetAddWordsTM2.cfg]
  have run := call_run w (Label.add l) (.done next) base TreeBudgetAddWordsTM2.program
    (program I) (by intro ph; simp [program,h]) (TreeBudgetAddWordsTM2.addition_halts u v)
  have last : TM2.step (program I) (embed w (Label.add l) (.done next) base
      (TreeBudgetAddWordsTM2.done (TreeBudgetAddWordsTM2.addWords u v false)))=
      some (cfg next (bank w base (TreeBudgetAddWordsTM2.done
        (TreeBudgetAddWordsTM2.addWords u v false)).stk)) := by
    simp [program,cfg,TM2.step,TM2.stepAux,embed,TreeBudgetAddWordsTM2.done,
      TreeBudgetStackRoutine.jump]
  exact weaken (seq I (prepend first run) (once last)) (by omega)

/-- The lookup wrapper transports an exact natural-table invocation into any
selected register bank, counting the assembler dispatch and return as well. -/
def lookup_run (l next : Λ) (w : Wiring A4NaturalLookup.K K)
    (h : I l=.lookup w next) (base : K → Bits) (t i out : Bits) (n : ℕ)
    (sub : A4NaturalLookup.Run (A4NaturalLookup.start t i)
      (A4NaturalLookup.stopped t i out) n) :
    Run I (cfg l (bank w base (A4NaturalLookup.start t i).stk))
      (cfg next (bank w base (A4NaturalLookup.stopped t i out).stk)) (n+2) := by
  have first : TM2.step (program I)
      (cfg l (bank w base (A4NaturalLookup.start t i).stk))=
      some (embed w (Label.lookup l) (.done next) base (A4NaturalLookup.start t i)) := by
    simp [program,h,cfg,TM2.step,TM2.stepAux,embed,A4NaturalLookup.start,
      A4NaturalLookup.machine,TreeBudgetStackRoutine.jump]
  have run := call_run w (Label.lookup l) (.done next) base A4NaturalLookup.program
    (program I) (by intro ph; simp [program,h]) sub
  have last : TM2.step (program I)
      (embed w (Label.lookup l) (.done next) base (A4NaturalLookup.stopped t i out))=
      some (cfg next (bank w base (A4NaturalLookup.stopped t i out).stk)) := by
    simp [program,cfg,TM2.step,TM2.stepAux,embed,A4NaturalLookup.stopped,
      TreeBudgetStackRoutine.jump]
  exact weaken (seq I (prepend first run) (once last)) (by omega)

def entry_run (l next : Λ) (w : Wiring TreeBudgetEntryTM2.K K)
    (h : I l=.entry w next) (base : K → Bits) (s ctx tail : Bits)
    (e : TreeBudgetSparseCodec.RawEntry)
    (hp : TreeBudgetSparseCodec.parseEntry s=some (e,tail)) :
    Run I (cfg l (bank w base (TreeBudgetEntryTM2.start s ctx).stk))
      (cfg next (bank w base (TreeBudgetEntryTM2.returned e tail ctx).stk))
      (24*(s.length+1)^2+2) := by
  have first : TM2.step (program I)
      (cfg l (bank w base (TreeBudgetEntryTM2.start s ctx).stk))=
      some (embed w (Label.entry l) (.done next) base (TreeBudgetEntryTM2.start s ctx)) := by
    simp [program,h,cfg,TM2.step,TM2.stepAux,embed,TreeBudgetEntryTM2.start,
      TreeBudgetFrameRoutineTM2.cfg,TreeBudgetEntryTM2.machine,TreeBudgetStackRoutine.jump]
  have run := call_run w (Label.entry l) (.done next) base TreeBudgetEntryTM2.program
    (program I) (by intro ph; simp [program,h]) (TreeBudgetEntryTM2.entry_success_run s ctx e tail hp)
  have last : TM2.step (program I)
      (embed w (Label.entry l) (.done next) base (TreeBudgetEntryTM2.returned e tail ctx))=
      some (cfg next (bank w base (TreeBudgetEntryTM2.returned e tail ctx).stk)) := by
    simp [program,cfg,TM2.step,TM2.stepAux,embed,TreeBudgetEntryTM2.returned,
      TreeBudgetStackRoutine.jump]
  exact weaken (seq I (prepend first run) (once last)) (by omega)

theorem le_result (u v : Bits) :
    TreeBudgetLeWordsTM2.leWords u v true=decide (value u≤value v) := by
  rw [TreeBudgetLeWordsTM2.leWords_value]
  apply Bool.decide_congr
  simp only [and_true]
  omega

/-- Numeric comparison consumes only the selected four-register bank. Both
branches return with normalized control state and a completely empty bank. -/
def le_run (l yes no : Λ) (w : Wiring (Fin 4) K) (h : I l=.le w yes no)
    (base : K → Bits) (u v : Bits) :
    Run I (cfg l (bank w base (TreeBudgetLeWordsTM2.cfg none true u v).stk))
      (cfg (if value u≤value v then yes else no)
        (bank w base (TreeBudgetAddWordsTM2.tapes [] [] [] [])))
      (u.length+v.length+3) := by
  let input := TreeBudgetLeWordsTM2.cfg none true u v
  have first : TM2.step (program I) (cfg l (bank w base input.stk))=
      some (embed w (Label.le l) (.leDone l) base input) := by
    simp [program,h,cfg,TM2.step,TM2.stepAux,embed,input,TreeBudgetLeWordsTM2.cfg,
      TreeBudgetStackRoutine.jump]
  have sub := TreeBudgetLeWordsTM2.compare_run u v none true
  rw [le_result] at sub
  have run := call_run w (Label.le l) (.leDone l) base TreeBudgetLeWordsTM2.program
    (program I) (by intro ph; simp [program,h]) sub
  have last (b : Bool) : TM2.step (program I)
      (embed w (Label.le l) (.leDone l) base (TreeBudgetLeWordsTM2.done b))=
      some (cfg (if b then yes else no) (bank w base (TreeBudgetAddWordsTM2.tapes [] [] [] []))) := by
    cases b <;> simp [program,h,cfg,TM2.step,TM2.stepAux,embed,TreeBudgetLeWordsTM2.done,
      TreeBudgetStackRoutine.jump,bank_put,updated]
  have allRun := seq I (prepend first run) (once (last (decide (value u≤value v))))
  simpa only [decide_eq_true_eq] using weaken allRun (show u.length+v.length+1+1+1≤u.length+v.length+3 by omega)

def branch_run (l yes no : Λ) (src : K) (h : I l=.branch src yes no)
    (s : K → Bits) (b : Bool) (tail : Bits) (hs : s src=b::tail) :
    Run I (cfg l s) (cfg (if b then yes else no) s) 1 := by
  apply once
  cases b <;> simp [program,h,cfg,TM2.step,TM2.stepAux,hs,TreeBudgetStackRoutine.jump]

def branch_empty_run (l yes no : Λ) (src : K) (h : I l=.branch src yes no)
    (s : K → Bits) (hs : s src=[]) : Run I (cfg l s) (cfg no s) 1 := by
  apply once
  simp [program,h,cfg,TM2.step,TM2.stepAux,hs,TreeBudgetStackRoutine.jump]

def go_run (l next : Λ) (h : I l=.go next) (s : K → Bits) :
    Run I (cfg l s) (cfg next s) 1 := by
  apply once
  simp [program,h,cfg,TM2.step,TM2.stepAux,TreeBudgetStackRoutine.jump]

def fail_run (l : Λ) (h : I l=.fail) (s : K → Bits) :
    Run I (cfg l s) ⟨none,(none,false),s⟩ 1 := by
  apply once
  simp [program,h,cfg,reject,TM2.step,TM2.stepAux]

end UAVProof.TreeBudgetSemanticRegisterTM2
