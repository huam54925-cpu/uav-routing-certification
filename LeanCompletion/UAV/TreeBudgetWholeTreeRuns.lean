import LeanCompletion.UAV.TreeBudgetWholeTreeTM2

namespace UAVProof.TreeBudgetWholeTreeTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call TreeBudgetParentArray
open Turing StateTransition

def rootReady {n : ℕ} (P : ParentArray n) (ctx : Bits) : Data :=
  {ready P ctx 0 n with q := TreeBudgetParentWalkTM2.query P P.root,r := encodeNat P.root.val}
def vertexReady {n : ℕ} (P : ParentArray n) (ctx : Bits) (v : Fin n) (left : ℕ) : Data :=
  {ready P ctx v.val left with
    q := TreeBudgetParentWalkTM2.query P v
    r := encodeNat P.root.val
    t := List.replicate n true}

def prepare_root {n : ℕ} (P : ParentArray n) (ctx : Bits) :
    Run (start P ctx) (cfg (ctl .rootCall) (rootReady P ctx))
      (4*(TreeBudgetParentWalkTM2.body P).length+2*n+4*(encodeNat P.root.val).length+10) := by
  let d := initial P ctx
  have a := count_job d (TreeBudgetParentWalkTM2.table P) rfl rfl
  have b := copy_job .queue {d with tokens := List.replicate n true} rfl
  have c := copy_job .rootTable (ready P ctx 0 n) rfl
  have e := copy_job .rootIndex {ready P ctx 0 n with q := d.body} rfl
  have f := copy_job .rootCode {ready P ctx 0 n with q := TreeBudgetParentWalkTM2.query P P.root} rfl
  simp only [TreeBudgetParentWalkTM2.table,Vector.length_toList,List.length_map,d,initial,List.append_nil] at a
  simp [copied,replace,source,dest,framed,next,entry,ready,initial,d] at b c e f
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ a b
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq c
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq e
  apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ seq f)
  omega

theorem test_step {n : ℕ} (P : ParentArray n) (ctx : Bits) (i left : ℕ) :
    machine.step (cfg (ctl .test) (ready P ctx i (left+1))) =
      some (cfg (entry .table) (ready P ctx i left)) := by
  simp only [machine,FinTM2.step,TM2.step,cfg,ctl,program,TM2.stepAux,TreeBudgetStackRoutine.scan,
    jump,TreeBudgetStackRoutine.jump,store,banks,saved,ready,initial,List.replicate_succ,
    Sum.elim_inr,List.head?_cons,List.tail_cons,Option.isNone_some,cond_false]
  congr 2
  funext k
  rcases k with (((j | b) | u) | v) | z
  all_goals first
    | fin_cases j <;> rfl | cases b <;> rfl | cases u <;> rfl | cases v <;> rfl | fin_cases z <;> rfl

def prepare_vertex {n : ℕ} (P : ParentArray n) (ctx : Bits) (v : Fin n) (left : ℕ) :
    Run (cfg (ctl .test) (ready P ctx v.val (left+1)))
      (cfg (ctl .call) (vertexReady P ctx v left))
      (2*(TreeBudgetParentWalkTM2.body P).length+2*v.val.bits.length+2*n+
        2*(encodeNat P.root.val).length+9) := by
  let d := ready P ctx v.val left
  have a := once (test_step P ctx v.val left)
  have b := copy_job .table d rfl
  have c := copy_job .index {d with q := d.body} rfl
  have e := copy_job .ticks {d with q := TreeBudgetParentWalkTM2.query P v} rfl
  have f := copy_job .root {d with q := TreeBudgetParentWalkTM2.query P v,t := d.tokens} rfl
  simp [copied,replace,source,dest,framed,next,entry,ready,initial,d] at b c e f
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ a b
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq c
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq e
  apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ seq f)
  omega

def called (root : Bool) (d : Data) (c : TreeBudgetWalkRootTM2.Cfg) : Cfg :=
  embed (callLabel root) (returnLabel root) (saved d) c

def endpoint_run (root : Bool) (d : Data) :
    Run (cfg (callEntry root) d)
      (called root d (TreeBudgetWalkRootTM2.finish d.t d.q d.r []))
      (d.t.length*(32*(2*d.q.length+1)^2)+d.r.length+3) :=
  call_run (callLabel root) (returnLabel root) (saved d) TreeBudgetWalkRootTM2.program program
    (fun _ => rfl) (TreeBudgetWalkRootTM2.root_run d.t d.q d.r [])

theorem call_step (d : Data) : machine.step (cfg (ctl .call) d) =
    some (cfg (callEntry false) d) := rfl

theorem root_call_step (d : Data) : machine.step (cfg (ctl .rootCall) d) =
    some (cfg (callEntry true) {d with t := true::d.t}) := by
  simp only [machine,FinTM2.step,TM2.step,cfg,ctl,program,TM2.stepAux,jump,TreeBudgetStackRoutine.jump]
  congr 2
  funext k
  rcases k with (((j | b) | u) | v) | z
  all_goals first
    | fin_cases j <;> rfl | cases b <;> rfl | cases u <;> rfl | cases v <;> rfl | fin_cases z <;> rfl

theorem reject_step (root : Bool) (d : Data) (c : TreeBudgetWalkRootTM2.Cfg)
    (hc : c.l = none) (hf : c.var.2 = false) :
    machine.step (called root d c) = some {called root d c with l := none} := by
  cases root <;> simp [machine,FinTM2.step,TM2.step,called,embed,hc,hf,returnLabel,ctl,program,TM2.stepAux] <;> rfl

theorem successful_return {n : ℕ} (P : ParentArray n) (v : Fin n)
    (ticks : Bits) (root : Bool) (d : Data)
    (h : (TreeBudgetWalkRootTM2.finish ticks (TreeBudgetParentWalkTM2.query P v)
      (encodeNat P.root.val) []).var.2 = true) :
    called root d (TreeBudgetWalkRootTM2.finish ticks (TreeBudgetParentWalkTM2.query P v)
      (encodeNat P.root.val) []) =
      cfg (returnLabel root) {d with q := TreeBudgetParentWalkTM2.body P,r := [],t := []} := by
  rw [TreeBudgetWalkRootTM2.successful_layout P ticks [] v h]
  rfl

theorem return_step (root : Bool) (d : Data) :
    machine.step (cfg (returnLabel root) d) =
      some (cfg (entry (if root then .rootClear else .clear)) d) := by cases root <;> rfl

def recycle_vertex {n : ℕ} (P : ParentArray n) (ctx : Bits) (i left : ℕ) :
    Run (cfg (returnLabel false) {ready P ctx i left with q := TreeBudgetParentWalkTM2.body P})
      (cfg (ctl .test) (ready P ctx (i+1) left))
      ((TreeBudgetParentWalkTM2.body P).length+2*i.bits.length+4) := by
  let d := ready P ctx i left
  have a := once (return_step false {d with q := TreeBudgetParentWalkTM2.body P})
  have b := clear_job .clear {d with q := TreeBudgetParentWalkTM2.body P}
  have c := increment_job d rfl
  simp only [replace,source,dest,next] at b
  simp only [d,ready,TreeBudgetStackRoutine.increment_bits] at c
  apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _
    (EvalsToInTime.trans machine.step _ _ _ _ _ a b) c)
  omega

end UAVProof.TreeBudgetWholeTreeTM2
