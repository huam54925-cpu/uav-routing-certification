import LeanCompletion.UAV.TreeBudgetFeeScalingTM2

namespace UAVProof.A4FeeScaling
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open Turing StateTransition

set_option synthInstance.maxSize 4096
set_option maxRecDepth 20000

theorem data_ext (a b : Data) (hs : a.saved=b.saved) (hw : a.work=b.work) (hm : a.mult=b.mult) : a=b := by
  cases a; cases b; cases hs; cases hw; cases hm; rfl

def copyData (l next : PC) (p : Ports K) (framed : Bool) (h : instr l=.copy p framed next)
    (d : Data) (ht : store d p.scratch=[]) :
    Run (cfg l d) (cfg next (put d p.dst
      ((if framed then word (store d p.src) else store d p.src)++store d p.dst)))
      (2*(store d p.src).length+3) := by
  simpa only [cfg,store_put] using
    TreeBudgetRegisterTM2.copy_run instr l next p framed h (store d) ht

def clearData (l next : PC) (p : Ports K) (h : instr l=.clear p next)
    (d : Data) (ht : store d p.scratch=[]) :
    Run (cfg l d) (cfg next (put d p.src [])) ((store d p.src).length+2) := by
  simpa only [cfg,store_put] using TreeBudgetRegisterTM2.clear_run instr l next p h (store d) ht

def readData (l next : PC) (p : Ports K) (h : instr l=.read p next)
    (d : Data) (u t : Bits) (hs : store d p.src=word u++t)
    (ht : store d p.scratch=[]) (hd : store d p.dst=[]) :
    Run (cfg l d) (cfg next (put (put d p.src t) p.dst u)) (3*u.length+3) := by
  simpa only [cfg,store_put] using
    TreeBudgetRegisterTM2.read_run instr l next p h (store d) u t hs ht hd

def emitData (l next : PC) (p : Ports K) (sg : K) (h : instr l=.emit p sg next)
    (d : Data) (b : Bool) (tail : Bits) (hs : store d sg=b::tail)
    (ht : store d p.scratch=[]) (hn : sg≠p.src ∧ sg≠p.scratch ∧ sg≠p.dst) :
    Run (cfg l d) (cfg next (put (put (put d sg tail) p.src []) p.dst
      (encodeInt (TreeBudgetSignedWordTM2.signed b (value (store d p.src)))++store d p.dst)))
      (2*(store d p.src).length+3) := by
  simpa only [cfg,store_put] using
    TreeBudgetRegisterTM2.emit_run instr l next p sg h (store d) b tail hs ht hn

def multiplied (d : Data) : Data := {d with mult:=fun i => match i.val with
  | 2 => mulWord (d.mult 0) (d.mult 1) | 5 => d.mult 5 | _ => []}

theorem mult_input (d : Data) (h₂ : d.mult 2=[]) (h₃ : d.mult 3=[]) (h₄ : d.mult 4=[]) :
    bank mw (store d) (TreeBudgetWeightedTM2.cfg 0 false (d.mult 0) (d.mult 1) [] [] [] (d.mult 5)).stk=
      store d := by
  funext k
  rcases k with k | i | r
  · rfl
  · fin_cases i <;> simp [bank,mw,store,TreeBudgetWeightedTM2.cfg,h₂,h₃,h₄]
  · rfl

theorem mult_output (d : Data) :
    bank mw (store d) (TreeBudgetWeightedTM2.stopped (mulWord (d.mult 0) (d.mult 1)) (d.mult 5)).stk=
      store (multiplied d) := by
  funext k
  rcases k with k | i | r
  · rfl
  · fin_cases i <;> rfl
  · rfl

def mulData (l next : PC) (h : instr l=.mul mw next) (d : Data)
    (h₂ : d.mult 2=[]) (h₃ : d.mult 3=[]) (h₄ : d.mult 4=[]) :
    Run (cfg l d) (cfg next (multiplied d))
      (16*((d.mult 0).length+(d.mult 1).length+1)^2+3) := by
  have run := TreeBudgetRegisterTM2.mul_run instr l next mw h (store d) (d.mult 0) (d.mult 1) (d.mult 5)
  change Run (TreeBudgetRegisterTM2.cfg l _)
    (TreeBudgetRegisterTM2.cfg next (bank mw (store d)
      (TreeBudgetWeightedTM2.stopped (mulWord (d.mult 0) (d.mult 1)) (d.mult 5)).stk)) _ at run
  rw [mult_input d h₂ h₃ h₄,mult_output] at run
  exact run

def bitData (l next : PC) (src dst : K) (h : instr l=.bit src dst next)
    (d : Data) (b : Bool) (t : Bits) (hs : store d src=b::t) (hne : dst≠src) :
    Run (cfg l d) (cfg next (put (put d src t) dst (b::store d dst))) 1 := by
  simpa only [cfg,store_put] using
    TreeBudgetRegisterTM2.bit_run instr l next src dst h (store d) b t hs hne

def pushData (l next : PC) (dst : K) (b : Bool) (h : instr l=.push dst b next) (d : Data) :
    Run (cfg l d) (cfg next (put d dst (b::store d dst))) 1 := by
  simpa only [cfg,store_put] using TreeBudgetRegisterTM2.push_run instr l next dst b h (store d)

def testData (l empty more : PC) (src : K) (h : instr l=.test src empty more) (d : Data) :
    Run (cfg l d) (cfg (if (store d src).isEmpty then empty else more) d) 1 :=
  TreeBudgetRegisterTM2.test_run instr l empty more src h (store d)

def haltData (d : Data) :
    Run (cfg .done d) (TreeBudgetRegisterTM2.stopped (store d)) 1 :=
  TreeBudgetRegisterTM2.halt_run instr .done rfl (store d)

end UAVProof.A4FeeScaling
