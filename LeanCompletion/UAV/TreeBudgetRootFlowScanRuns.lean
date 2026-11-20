import LeanCompletion.UAV.TreeBudgetRootFlowScanTM2

namespace UAVProof.TreeBudgetRootFlowScanTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call Turing StateTransition

def frameSource (h : Bool) (d : Data) := if h then d.hw else d.pw
def frameDest (h : Bool) (d : Data) := if h then d.b else d.x
def frameSet (h : Bool) (d : Data) (s t z : Bits) : Data :=
  if h then {d with hw:=s,tmp:=t,b:=z} else {d with pw:=s,tmp:=t,x:=z}
theorem frame_layout (h : Bool) (d : Data) (s t z : Bits) :
    tapes (framePorts h) (store d) s t z=store (frameSet h d s t z) := by
  cases h <;> funext k <;> cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

def field_run (h : Bool) (d : Data) (x : ℕ) (tail : Bits)
    (hs : frameSource h d=encodeNat x ++ tail) (ht : d.tmp=[]) (hz : frameDest h d=[]) :
    Run (cfg (.frame h .marker) d) (cfg (frameNext h) (frameSet h d tail [] x.bits))
      (2*(frameSource h d).length+2) := by
  have he : frameSet h d (encodeNat x ++ tail) [] []=d := by
    cases h <;> cases d <;> simp_all [frameSource,frameDest,frameSet]
  have run := TreeBudgetNatRoutine.run (framePorts h) (store d) (L.frame h) (frameNext h)
    (.control .reject) program (fun _ => rfl) (encodeNat x ++ tail) []
  simp only [TreeBudgetNatRoutine.finish,parseNat_append,TreeBudgetFrameRoutineTM2.cfg,
    frame_layout,List.append_nil,he] at run
  rw [← hs] at run
  exact run

theorem compare_layout (d : Data) (x y i : Bits) :
    tapes comparePorts (store d) x y i=store {d with x:=x,y:=y,idx:=i} := by
  funext k; cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

def comparison (c : Check) (d : Data) := TreeBudgetCompareRoutine.words (equal c) d.x d.y true
def compared (c : Check) (d : Data) : Cfg :=
  let d' := {d with x:=[],y:=[]}
  match c with
  | .parent => cfg (if comparison c d then entry .index else entry .clearH) d'
  | .index => cfg (if comparison c d then entry .clearH else entry .operand) d'
  | .le => if comparison c d then cfg (entry .reverseM) d' else stop d' false
  | .ge => stop d' (comparison c d)

def compare_job (c : Check) (d : Data) :
    Run (cfg (.compare c) d) (compared c d) (d.x.length+d.y.length+2) := by
  have run := TreeBudgetCompareRoutine.run comparePorts (store d) (.compare c) (.compared c)
    (equal c) program rfl d.x d.y d.idx none true
  simp only [TreeBudgetFrameRoutineTM2.cfg,compare_layout] at run
  have last : machine.step (cfg (.compared c) {d with x:=[],y:=[]} (comparison c d))=some (compared c d) := by
    cases c <;> cases he : comparison _ d <;>
      simp [machine,FinTM2.step,TM2.step,cfg,program,TM2.stepAux,compared,he,stop,jump,TreeBudgetStackRoutine.jump]
  exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _ run (once last)) (by omega)

theorem comparison_eq (c : Check) (hc : equal c=true) (d : Data) : comparison c d=decide (d.x=d.y) := by
  simp [comparison,hc,TreeBudgetCompareRoutine.words_eq]
theorem comparison_le (c : Check) (hc : equal c=false) (d : Data) : comparison c d=decide (value d.x≤value d.y) := by
  simp only [comparison,hc,TreeBudgetCompareRoutine.words_lt,TreeBudgetLeWordsTM2.leWords_value, and_true]
  apply Bool.decide_congr
  omega
theorem bits_eq (a b : ℕ) : decide (a.bits=b.bits)=decide (a=b) := by
  apply Bool.decide_congr
  constructor
  · intro h; simpa using congrArg value h
  · exact congrArg Nat.bits

def addition_job (d : Data) (ha : d.a=[]) (hc : d.c=[]) (ht : d.tmp=[]) :
    Run (cfg (entry .operand) d)
      (cfg (entry .increment) {d with a:=[],b:=[],c:=[],u:=TreeBudgetAddWordsTM2.addWords d.u d.b false})
      (5*d.u.length+2*d.b.length+9) := by
  let d₁ : Data := {d with a:=d.u}
  let d₂ : Data := {d₁ with u:=[]}
  have copy : Run (cfg (entry .operand) d) (cfg (entry .clearAcc) d₁) (2*d.u.length+2) := by
    simpa [copied,source,dest,replace,ha,ht,d₁] using copy_job .operand d ht
  have clear : Run (cfg (entry .clearAcc) d₁) (cfg (.control .add) d₂) (d.u.length+1) := clear_job .clearAcc d₁
  have seed : machine.step (cfg (.control .add) d₂)=some (cfg (.adder 0) d₂ false) := rfl
  have add := call_run L.adder (.control .returned) (saved d)
    TreeBudgetAddWordsTM2.program program (fun _ => rfl) (TreeBudgetAddWordsTM2.addition_halts d.u d.b)
  have init : embed L.adder (.control .returned) (saved d) (TreeBudgetAddWordsTM2.cfg 0 none false d.u d.b [] [])=
      cfg (.adder 0) d₂ false := by
    simp [embed,TreeBudgetAddWordsTM2.cfg,cfg,store,d₂,d₁,hc]
    rfl
  have endEq : embed L.adder (.control .returned) (saved d)
      (TreeBudgetAddWordsTM2.done (TreeBudgetAddWordsTM2.addWords d.u d.b false))=
      cfg (.control .returned) {d with a:=[],b:=[],c:=[],u:=TreeBudgetAddWordsTM2.addWords d.u d.b false} false := rfl
  rw [init,endEq] at add
  have last : machine.step (cfg (.control .returned)
      {d with a:=[],b:=[],c:=[],u:=TreeBudgetAddWordsTM2.addWords d.u d.b false} false)=
      some (cfg (entry .increment) {d with a:=[],b:=[],c:=[],u:=TreeBudgetAddWordsTM2.addWords d.u d.b false}) := rfl
  exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _
    (EvalsToInTime.trans machine.step _ _ _ _ _
      (EvalsToInTime.trans machine.step _ _ _ _ _
        (EvalsToInTime.trans machine.step _ _ _ _ _ copy clear) (once seed)) add) (once last)) (by omega)

def testEnd (d : Data) : Cfg := if d.pw=[] then
  if d.hw=[] then cfg (entry .finalA) d else stop d false
  else if d.hw=[] then stop d false else cfg (.frame false .marker) d
theorem test_step (d : Data) : machine.step (cfg (.control .loop) d)=some (testEnd d) := by
  cases hp : d.pw <;> cases hh : d.hw <;>
    simp [machine,FinTM2.step,TM2.step,cfg,program,TM2.stepAux,store,saved,banks,hp,hh,
      testEnd,stop,jump,TreeBudgetStackRoutine.jump]

def work (d : Data) (i : ℕ) (ps hs : List ℕ) (u : Bits) : Data :=
  {d with
    a:=[],b:=[],c:=[],u:=u,pw:=(ps.flatMap encodeNat),hw:=(hs.flatMap encodeNat),
    idx:=i.bits,x:=[],y:=[],tmp:=[]}

def setup_run (p h : List ℕ) (r m : ℕ) : Run (start p h r m)
    (cfg (.control .loop) (work (initial p h r m) 0 p h []))
    (2*(p.flatMap encodeNat).length+2*(h.flatMap encodeNat).length+4) := by
  have hp := copy_job .parents (initial p h r m) rfl
  have hh := copy_job .demands (copied .parents (initial p h r m)) rfl
  exact weaken (by simpa [start,work,initial,copied,source,dest,replace] using
    EvalsToInTime.trans machine.step _ _ _ _ _ hp hh) (by simp only [List.length_flatMap]; omega)

end UAVProof.TreeBudgetRootFlowScanTM2
