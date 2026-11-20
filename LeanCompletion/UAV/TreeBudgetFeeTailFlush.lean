import LeanCompletion.UAV.TreeBudgetFeeTailTM2

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition

def flushPorts (f : FeeField) : Ports K :=
  ⟨.inr .rev,.inr (.result f),.inr .tmp,by cases f <;> decide,by decide,by cases f <;> decide⟩
def flushCfg (f : FeeField) (base : K → Bits) (l : L) (a out : Bits) (v : State) : Cfg :=
  TreeBudgetFrameRoutineTM2.cfg (flushPorts f) base l v.1 v.2 a out (base (.inr .tmp))

@[simp] theorem flush_top (f : FeeField) (base : K → Bits) (a out : Bits) :
    tapes (flushPorts f) base a out (base (.inr .tmp)) (.inr .rev)=a := tapes_src _ _ _ _ _
@[simp] theorem flush_output (f : FeeField) (base : K → Bits) (a out : Bits) :
    tapes (flushPorts f) base a out (base (.inr .tmp)) (.inr (.result f))=out := tapes_scratch _ _ _ _ _
@[simp] theorem flush_pop (f : FeeField) (base : K → Bits) (a out b : Bits) :
    Function.update (tapes (flushPorts f) base a out (base (.inr .tmp))) (.inr .rev) b=
      tapes (flushPorts f) base b out (base (.inr .tmp)) := update_src _ _ _ _ _ _
@[simp] theorem flush_push (f : FeeField) (base : K → Bits) (a out b : Bits) :
    Function.update (tapes (flushPorts f) base a out (base (.inr .tmp))) (.inr (.result f)) b=
      tapes (flushPorts f) base a b (base (.inr .tmp)) := update_scratch _ _ _ _ _ _

def flush_run (f : FeeField) (base : K → Bits) (a out : Bits) (v : State) :
    EvalsToInTime machine.step (flushCfg f base (.flush f) a out v)
      (some (flushCfg f base (nextGroup f) [] (a.reverse++out) (none,true))) (a.length+1) := by
  induction a generalizing out v with
  | nil =>
    apply once
    simp [machine,FinTM2.step,TM2.step,flushCfg,TreeBudgetFrameRoutineTM2.cfg,program,TM2.stepAux,go]
    congr 2
    funext k
    by_cases hr : k=Sum.inr Aux.rev <;> by_cases ho : k=Sum.inr (Aux.result f) <;>
      simp_all [tapes,flushPorts,Function.update_apply]
  | cons b a ih =>
    have step : machine.step (flushCfg f base (.flush f) (b::a) out v)=
        some (flushCfg f base (.flush f) a (b::out) (some b,true)) := by
      simp [machine,FinTM2.step,TM2.step,flushCfg,TreeBudgetFrameRoutineTM2.cfg,program,TM2.stepAux,go]
      congr 2
      funext k
      by_cases hr : k=Sum.inr Aux.rev <;> by_cases ho : k=Sum.inr (Aux.result f) <;>
        simp_all [tapes,flushPorts,Function.update_apply]
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using prepend step (ih (b::out) (some b,true))


end UAVProof.A4FeeTailMachine
