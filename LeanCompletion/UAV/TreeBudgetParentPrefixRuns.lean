import LeanCompletion.UAV.TreeBudgetParentPrefixTM2

namespace UAVProof.TreeBudgetParentPrefixTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call Turing StateTransition

local macro "layout" : tactic => `(tactic|
  (funext k
   rcases k with ((((i | b) | u) | v) | z) | w
   · fin_cases i <;> rfl
   · cases b <;> rfl
   · cases u <;> rfl
   · cases v <;> rfl
   · fin_cases z <;> rfl
   · rcases w with (i | u) | z
     · fin_cases i <;> rfl
     · cases u; rfl
     · fin_cases z <;> rfl))

theorem frame_layout (d : Data) (saved : Saved) (s t r : Bits) :
    tapes framePorts (store d saved) s t r = store {d with q:=s,tmp:=t,r:=r} saved := by layout

def field_run (d : Data) (saved : Saved) (x : ℕ) (xs : Bits)
    (hq : d.q=encodeNat x ++ xs) (ht : d.tmp=[]) (hr : d.r=[]) :
    Run (cfg (.frame .marker) d saved)
      (cfg (entry .parentBound) {d with q:=xs,r:=x.bits} saved) (2*d.q.length+2) := by
  have h := TreeBudgetNatRoutine.run framePorts (store d saved) L.frame (entry .parentBound)
    (.control .reject) program (fun _ => rfl) (encodeNat x ++ xs) []
  simp only [TreeBudgetNatRoutine.finish,parseNat_append,TreeBudgetFrameRoutineTM2.cfg,
    frame_layout,List.append_nil] at h
  have hs : {d with q:=encodeNat x ++ xs,tmp:=[],r:=[]} = d := by cases d; simp_all
  have he : {d with q:=xs,tmp:=[],r:=x.bits} = {d with q:=xs,r:=x.bits} := by rw [← ht]
  rw [hs,he,← hq] at h
  exact h

theorem compare_layout (d : Data) (saved : Saved) (r t i : Bits) :
    tapes comparePorts (store d saved) r t i = store {d with r:=r,t:=t,idx:=i} saved := by layout

def comparison (c : Check) (d : Data) := TreeBudgetCompareRoutine.words (equal c) d.r d.t (equal c)
def compared (c : Check) (d : Data) (saved : Saved) : Cfg :=
  if comparison c d then cfg (after c) {d with r:=[],t:=[]} saved
  else stop {d with r:=[],t:=[]} saved false

def compare_job (c : Check) (d : Data) (saved : Saved) :
    Run (cfg (.beginCompare c) d saved) (compared c d saved) (d.r.length+d.t.length+3) := by
  have first : machine.step (cfg (.beginCompare c) d saved) = some (cfg (.compare c) d saved (equal c)) := rfl
  have h := TreeBudgetCompareRoutine.run comparePorts (store d saved) (.compare c) (.compared c)
    (equal c) program rfl d.r d.t d.idx none (equal c)
  simp only [TreeBudgetFrameRoutineTM2.cfg,compare_layout] at h
  have last : machine.step (cfg (.compared c) {d with r:=[],t:=[]} saved (comparison c d)) =
      some (compared c d saved) := by
    cases hc : comparison c d <;>
      simp [machine,FinTM2.step,TM2.step,cfg,compared,hc,program,jump,TreeBudgetStackRoutine.jump,
        TM2.stepAux,stop]
  exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _ (prepend first h) (once last)) (by omega)

theorem strict_comparison (c : Check) (hc : c ≠ .dimension) (d : Data) :
    comparison c d = decide (value d.r < value d.t) := by
  have he : equal c = false := by cases c <;> simp_all [equal]
  simp [comparison,he,TreeBudgetCompareRoutine.words_lt,TreeBudgetLeWordsTM2.leWords_value]
theorem dimension_comparison (d : Data) : comparison .dimension d = decide (d.r=d.t) := by
  simp [comparison,equal,TreeBudgetCompareRoutine.words_eq]

theorem counter_layout (j : Job) (hj : j=.increment ∨ j=.clear) (d : Data) (saved : Saved) (s t r : Bits) :
    tapes (ports j) (store d saved) s t r = store {d with idx:=s,tmp:=t,root:=r} saved := by
  rcases hj with rfl | rfl <;> layout

def increment_job (d : Data) (saved : Saved) (ht : d.tmp=[]) :
    Run (cfg (entry .increment) d saved)
      (cfg (.control .loop) {d with idx:=TreeBudgetStackRoutine.increment d.idx} saved) (2*d.idx.length+2) := by
  have h := TreeBudgetStackRoutine.increment_run (ports .increment) (store d saved) (L.job .increment)
    (next .increment) false program (fun _ => rfl) d.idx [] d.root
  simp only [TreeBudgetStackRoutine.conf,counter_layout .increment (Or.inl rfl),List.reverse_nil,
    List.nil_append,List.length_nil,Nat.add_zero] at h
  rw [← ht] at h
  exact h

def clear_job (d : Data) (saved : Saved) :
    Run (cfg (entry .clear) d saved) (cfg treeEntry {d with idx:=[]} saved) (d.idx.length+1) := by
  have h := TreeBudgetStackRoutine.clear_run (ports .clear) (store d saved) (L.job .clear)
    (next .clear) false program (fun _ => rfl) d.idx d.tmp d.root
  simp only [TreeBudgetStackRoutine.conf,counter_layout .clear (Or.inr rfl)] at h
  exact h

theorem loop_empty (d : Data) (saved : Saved) (hq : d.q=[]) :
    machine.step (cfg (.control .loop) d saved) = some (cfg (entry .counterDigit) d saved) := by
  simp [machine,FinTM2.step,TM2.step,cfg,program,TM2.stepAux,store,banks,
    TreeBudgetWholeTreeTM2.store,TreeBudgetWalkRootTM2.start,TreeBudgetWalkRootTM2.called,
    embed,TreeBudgetParentWalkTM2.cfg,TreeBudgetParentWalkTM2.store,hq,jump,TreeBudgetStackRoutine.jump]

theorem loop_more (d : Data) (saved : Saved) (hq : d.q≠[]) :
    machine.step (cfg (.control .loop) d saved) = some (cfg (.frame .marker) d saved) := by
  cases he : d.q with
  | nil => exact (hq he).elim
  | cons b bs =>
    simp [machine,FinTM2.step,TM2.step,cfg,program,TM2.stepAux,store,banks,
      TreeBudgetWholeTreeTM2.store,TreeBudgetWalkRootTM2.start,TreeBudgetWalkRootTM2.called,
      embed,TreeBudgetParentWalkTM2.cfg,TreeBudgetParentWalkTM2.store,he,jump,TreeBudgetStackRoutine.jump]

end UAVProof.TreeBudgetParentPrefixTM2
