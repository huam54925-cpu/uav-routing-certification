import LeanCompletion.UAV.TreeBudgetFeeTailLoops
import LeanCompletion.UAV.TreeBudgetFeeTailFieldTime

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition

def group_run_success (g : Bool) (base : K → Bits) (s a : Bits) (v : State)
    (w t : Bits) (h : groupRead g s=some (w,t)) :
    Run (streamCfg (groupEntry g) base s a v) (groupEnd g base s a) w.length := by
  cases g
  · exact signed_run_success _ _ _ _ _ _ _ h
  · exact word_run_success _ _ _ _ _ _ _ _ h

/-- Successful reads charge only the consumed field; a failed read charges the
remaining input. This telescopes to a linear bound, including all marker tests. -/
def loop_run_linear (g : Bool) (base : K → Bits) (n : ℕ) (s a : Bits) (v : State) :
    Run (loopCfg g base n s a v) (loopEnd g base n s a) (s.length+2*n+3) := by
  induction n generalizing s a v with
  | zero => simpa using loop_run g base 0 s a v
  | succ n ih =>
    have first : machine.step (loopCfg g base (n+1) s a v)=
        some (streamCfg (groupEntry g) (tickBase base n) s a (some true,true)) := by
      simp [machine,FinTM2.step,TM2.step,loopCfg,streamCfg,program,TM2.stepAux,go,groupEntry,List.replicate_succ]
      congr 2
      funext k
      by_cases ht : k=Sum.inr Aux.ticks <;> by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
        simp_all [streamStore,tickBase,Function.update_apply,src]
    cases hp : groupRead g s with
    | none =>
      have run := seq (once first) (group_run g (tickBase base n) s a (some true,true))
      exact weaken (by simpa [loopEnd,hp] using run) (by omega)
    | some pair =>
      obtain ⟨w,t⟩ := pair
      have run := seq (once first) (group_run_success g (tickBase base n) s a (some true,true) w t hp)
      have contract := group_read g (tickBase base n) s a
      simp only [hp] at contract
      rw [contract] at run
      have next := ih t (w.reverse++a) (some false,true)
      have he := congrArg List.length (group_consumed g s w t hp)
      simp only [List.length_append] at he
      exact weaken (by simpa [loopEnd,hp,loopCfg] using seq run next) (by omega)

end UAVProof.A4FeeTailMachine
