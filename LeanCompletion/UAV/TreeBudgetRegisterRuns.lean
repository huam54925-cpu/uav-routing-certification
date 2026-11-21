import LeanCompletion.UAV.TreeBudgetRegisterTM2

namespace UAVProof.TreeBudgetRegisterTM2
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

end UAVProof.TreeBudgetRegisterTM2
