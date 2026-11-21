import LeanCompletion.UAV.TreeBudgetRowsCheckTM2
import LeanCompletion.UAV.TreeBudgetColumnAccumulator

namespace UAVProof.A4RowsCheck
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def source (j : Job) (d : Data) : Bits := match j with
  | .copyBody => d.body | .copyMarkers => d.markers | .copyRow | .clearEntryRow => d.entryRow
  | .copySum | .clearSum => d.sum | .clearRow => d.rowSaved (A4RowCheck.reg 2)
  | .totalLeft | .totalRight => d.total | .routesRight | .routesLeft => d.routes
def dest (j : Job) (d : Data) : Bits := match j with
  | .copyBody => d.cursor | .copyMarkers => d.todo | .copyRow => d.rowSaved (A4RowCheck.reg 2)
  | .copySum => d.total | .totalLeft | .routesLeft => d.cmp0
  | .routesRight | .totalRight => d.cmp1 | _ => d.spare
def replace (j : Job) (d : Data) (s t z : Bits) : Data := match j with
  | .copyBody => {d with body := s,scratch := t,cursor := z}
  | .copyMarkers => {d with markers := s,scratch := t,todo := z}
  | .copyRow => {d with entryRow := s,scratch := t,rowSaved := Function.update d.rowSaved (A4RowCheck.reg 2) z}
  | .clearEntryRow => {d with entryRow := s,scratch := t,spare := z}
  | .copySum => {d with sum := s,scratch := t,total := z}
  | .clearSum => {d with sum := s,scratch := t,spare := z}
  | .clearRow => {d with scratch := t,spare := z,rowSaved := Function.update d.rowSaved (A4RowCheck.reg 2) s}
  | .totalLeft => {d with total := s,scratch := t,cmp0 := z}
  | .routesRight => {d with routes := s,scratch := t,cmp1 := z}
  | .routesLeft => {d with routes := s,scratch := t,cmp0 := z}
  | .totalRight => {d with total := s,scratch := t,cmp1 := z}

theorem replace_original (j : Job) (d : Data) :
    replace j d (source j d) d.scratch (dest j d)=d := by
  cases j <;> simp [replace,source,dest,Function.update_eq_self]

theorem tapes_replace (j : Job) (d : Data) (s t z : Bits) :
    tapes (ports j) (store d) s t z=store (replace j d s t z) := by
  cases j <;> funext k <;> rcases k with ((i|u)|r)|a
  all_goals first
    | (fin_cases i <;> rfl)
    | (cases u; rfl)
    | (cases a <;> rfl)
    | (rcases r with r|r
       · rfl
       · fin_cases r <;> simp [tapes,ports,store,replace,A4RowCheck.reg,rs,es,ax])

theorem conf_replace (j : Job) (d : Data) (l : L) (s t z : Bits) :
    TreeBudgetStackRoutine.conf (ports j) (store d) l s t z=
      cfg l (replace j d s t z) := by
  simp only [TreeBudgetStackRoutine.conf,cfg,tapes_replace]

def copied (j : Job) (d : Data) : Data :=
  replace j d (source j d) [] (source j d++dest j d)
def cleared (j : Job) (d : Data) : Data := replace j d [] d.scratch (dest j d)

def copy_job (j : Job) (d : Data) (ht : d.scratch=[]) :
    Run (cfg (.job j .reverse) d) (cfg (next j) (copied j d))
      (2*(source j d).length+2) := by
  have h := TreeBudgetStackRoutine.copy_run (ports j) (store d) (L.job j) (next j)
    false program (fun _ => rfl) (source j d) (dest j d)
  rw [conf_replace,conf_replace,← ht,replace_original] at h
  simpa only [copied,ht,machine,FinTM2.step] using h

def clear_job (j : Job) (d : Data) :
    Run (cfg (.job j .clear) d) (cfg (next j) (cleared j d)) ((source j d).length+1) := by
  have h := TreeBudgetStackRoutine.clear_run (ports j) (store d) (L.job j) (next j)
    false program (fun _ => rfl) (source j d) d.scratch (dest j d)
  rw [conf_replace,conf_replace,replace_original] at h
  exact h

def parsed (d : Data) (e : TreeBudgetSparseCodec.RawEntry) (tail : Bits) : Data :=
  {d with cursor := tail,entryRow := e.2.flatMap encodeNat,mult := e.1.bits}

theorem entry_initial_bank (d : Data) (hr : d.entryRow=[]) (hm : d.mult=[]) :
    bank ew (store d) (TreeBudgetEntryTM2.start d.cursor []).stk=store d := by
  funext k
  rcases k with ((i|u)|r)|a
  · fin_cases i <;> simp [bank,ew,store,TreeBudgetEntryTM2.start,TreeBudgetEntryTM2.base,
      cfg,TreeBudgetFrameRoutineTM2.cfg,tapes,TreeBudgetEntryTM2.ports,hr]
  · cases u; simpa [bank,ew,store,TreeBudgetEntryTM2.start,TreeBudgetEntryTM2.base,
      TreeBudgetFrameRoutineTM2.cfg,tapes,TreeBudgetEntryTM2.ports] using hm.symm
  · rfl
  · rfl

theorem entry_returned_bank (d : Data) (e : TreeBudgetSparseCodec.RawEntry) (tail : Bits) :
    bank ew (store d) (TreeBudgetEntryTM2.returned e tail []).stk=store (parsed d e tail) := by
  funext k
  rcases k with ((i|u)|r)|a
  · fin_cases i <;> rfl
  · cases u; rfl
  · rfl
  · rfl

def entry_success (d : Data) (e : TreeBudgetSparseCodec.RawEntry) (tail : Bits)
    (hp : TreeBudgetSparseCodec.parseEntry d.cursor=some (e,tail))
    (hr : d.entryRow=[]) (hm : d.mult=[]) :
    Run (cfg (.entryCall TreeBudgetEntryTM2.machine.main) d)
      (cfg (.job .copyRow .reverse) (parsed d e tail)) (24*(d.cursor.length+1)^2+1) := by
  have sub := call_run ew L.entryCall .entryDone (store d) TreeBudgetEntryTM2.program
    program (fun _ => rfl) (TreeBudgetEntryTM2.entry_success_run d.cursor [] e tail hp)
  have first : embed ew L.entryCall .entryDone (store d) (TreeBudgetEntryTM2.start d.cursor [])=
      cfg (.entryCall TreeBudgetEntryTM2.machine.main) d := by
    change (⟨some (.entryCall TreeBudgetEntryTM2.machine.main),(none,true),
      bank ew (store d) (TreeBudgetEntryTM2.start d.cursor []).stk⟩ : Cfg)=
        cfg (.entryCall TreeBudgetEntryTM2.machine.main) d
    rw [entry_initial_bank d hr hm]
    rfl
  have last : embed ew L.entryCall .entryDone (store d) (TreeBudgetEntryTM2.returned e tail [])=
      cfg .entryDone (parsed d e tail) := by
    change (⟨some L.entryDone,(none,true),
      bank ew (store d) (TreeBudgetEntryTM2.returned e tail []).stk⟩ : Cfg)=
        cfg .entryDone (parsed d e tail)
    rw [entry_returned_bank d e tail]
    rfl
  rw [first,last] at sub
  exact seq sub (once rfl)

theorem row_bank (d : Data) : bank rw (store d) d.rowSaved=store d := by
  funext k
  rcases k with (i|r)|a <;> rfl

/-- The complete row contract is transported without inspecting its result.
The false branch is taken for zero-count records as for every other record. -/
def row_result (d : Data) (b : Bool) (t : ℕ)
    (sub : EvalsToInTime A4RowCheck.machine.step
      ⟨some A4RowCheck.machine.main,(none,true),d.rowSaved⟩
      (some ⟨none,(none,b),d.rowSaved⟩) t) :
    Run (cfg .rowStart d) (if b then cfg .addStart d else stop false d) (t+2) := by
  have call := call_run rw L.rowCall .rowDone (store d)
    (TreeBudgetSemanticRegisterTM2.program A4RowCheck.instructions) program
    (fun _ => rfl) sub
  simp only [embed,row_bank] at call
  dsimp only [Option.elim] at call
  have first : machine.step (cfg .rowStart d)=
      some ⟨some (.rowCall A4RowCheck.machine.main),(none,true),store d⟩ := by
    rfl
  have last : machine.step ⟨some L.rowDone,(none,b),store d⟩=
      some (if b then cfg .addStart d else stop false d) := by
    cases b <;> simp [machine,FinTM2.step,cfg,stop,program,TM2.step,TM2.stepAux,jump,
      reject,TreeBudgetStackRoutine.jump]
  exact weaken (seq (prepend first call) (once last)) (by omega)

def added (d : Data) : Data :=
  {d with total := [],mult := [],spare := [],sum := TreeBudgetAddWordsTM2.addWords d.total d.mult false}

theorem add_initial_bank (d : Data) (hs : d.sum=[]) (hp : d.spare=[]) :
    bank aw (store d) (TreeBudgetAddWordsTM2.cfg 0 none false d.total d.mult [] []).stk=store d := by
  funext k
  rcases k with ((i|u)|r)|a
  · fin_cases i <;> rfl
  · cases u; rfl
  · rfl
  · cases a <;> simp [bank,aw,addGet,store,TreeBudgetAddWordsTM2.cfg,
      TreeBudgetAddWordsTM2.tapes,hs,hp]

theorem add_returned_bank (d : Data) :
    bank aw (store d) (TreeBudgetAddWordsTM2.done
      (TreeBudgetAddWordsTM2.addWords d.total d.mult false)).stk=store (added d) := by
  funext k
  rcases k with ((i|u)|r)|a
  · fin_cases i <;> rfl
  · cases u; rfl
  · rfl
  · cases a <;> rfl

def add_result (d : Data) (hs : d.sum=[]) (hp : d.spare=[]) :
    Run (cfg .addStart d) (cfg (.job .copySum .reverse) (added d))
      (2*(d.total.length+d.mult.length)+6) := by
  have sub := call_run aw L.addCall .addDone (store d) TreeBudgetAddWordsTM2.program
    program (fun _ => rfl) (TreeBudgetAddWordsTM2.addition_halts d.total d.mult)
  have first : machine.step (cfg .addStart d)=some
      (embed aw L.addCall .addDone (store d)
        (TreeBudgetAddWordsTM2.cfg 0 none false d.total d.mult [] [])) := by
    rw [show (embed aw L.addCall .addDone (store d)
        (TreeBudgetAddWordsTM2.cfg 0 none false d.total d.mult [] []))=
        ⟨some (.addCall 0),(none,false),store d⟩ by
      change (⟨some (.addCall 0),(none,false),bank aw (store d)
        (TreeBudgetAddWordsTM2.cfg 0 none false d.total d.mult [] []).stk⟩ : Cfg)=
          ⟨some (.addCall 0),(none,false),store d⟩
      rw [add_initial_bank d hs hp]]
    simp [machine,FinTM2.step,cfg,program,TM2.step,TM2.stepAux]
  have last : machine.step (embed aw L.addCall .addDone (store d)
      (TreeBudgetAddWordsTM2.done (TreeBudgetAddWordsTM2.addWords d.total d.mult false)))=
      some (cfg (.job .copySum .reverse) (added d)) := by
    change machine.step ⟨some L.addDone,(none,false),bank aw (store d)
      (TreeBudgetAddWordsTM2.done (TreeBudgetAddWordsTM2.addWords d.total d.mult false)).stk⟩=_
    exact (congrArg (fun s : K → Bits =>
      machine.step (⟨some L.addDone,(none,false),s⟩ : Cfg))
      (add_returned_bank d)).trans rfl
  exact weaken (seq (prepend first sub) (once last)) (by omega)

def compared (d : Data) : Data := {d with cmp0 := [],cmp1 := [],cmp2 := [],cmp3 := []}
def compareReturned (d : Data) (b : Bool) : Data :=
  {d with cmp0 := [],cmp1 := [],cmp2 := [],cmp3 := [b]}

theorem compare_initial_bank (d : Data) (h2 : d.cmp2=[]) (h3 : d.cmp3=[]) :
    bank cw (store d) (TreeBudgetLeWordsTM2.cfg none true d.cmp0 d.cmp1).stk=store d := by
  funext k
  cases k with
  | inl r => rcases r with (i|u)|r <;> rfl
  | inr a => cases a <;> simp [bank,cw,cmpGet,store,TreeBudgetLeWordsTM2.cfg,
      TreeBudgetAddWordsTM2.tapes,h2,h3]

theorem compare_returned_bank (d : Data) (b : Bool) :
    bank cw (store d) (TreeBudgetLeWordsTM2.done b).stk=store (compareReturned d b) := by
  funext k
  cases k with
  | inl r => rcases r with (i|u)|r <;> rfl
  | inr a => cases a <;> rfl

theorem compare_pop (d : Data) (b : Bool) :
    Function.update (store (compareReturned d b)) (ax .cmp3) []=store (compared d) := by
  funext k
  cases k with
  | inl r => rcases r with (i|u)|r <;> rfl
  | inr a => cases a <;> rfl

theorem le_words_result (u v : Bits) :
    TreeBudgetLeWordsTM2.leWords u v true=decide (value u≤value v) := by
  rw [TreeBudgetLeWordsTM2.leWords_value]
  apply Bool.decide_congr
  simp only [and_true]
  omega

def compare_result (rev : Bool) (d : Data) (h2 : d.cmp2=[]) (h3 : d.cmp3=[]) :
    Run (cfg (.compareCall rev ()) d)
      (if value d.cmp0≤value d.cmp1 then
        cfg (if rev then .good else .job .routesLeft .reverse) (compared d)
       else stop false (compared d)) (d.cmp0.length+d.cmp1.length+2) := by
  have core := TreeBudgetLeWordsTM2.compare_run d.cmp0 d.cmp1 none true
  rw [le_words_result] at core
  have sub := call_run cw (L.compareCall rev) (.compareDone rev) (store d)
    TreeBudgetLeWordsTM2.program program (fun _ => rfl) core
  have first : embed cw (L.compareCall rev) (.compareDone rev) (store d)
      (TreeBudgetLeWordsTM2.cfg none true d.cmp0 d.cmp1)=cfg (.compareCall rev ()) d := by
    change (⟨some (.compareCall rev ()),(none,true),bank cw (store d)
      (TreeBudgetLeWordsTM2.cfg none true d.cmp0 d.cmp1).stk⟩ : Cfg)=
        cfg (.compareCall rev ()) d
    rw [compare_initial_bank d h2 h3]
    rfl
  rw [first] at sub
  have last : machine.step (embed cw (L.compareCall rev) (.compareDone rev) (store d)
      (TreeBudgetLeWordsTM2.done (decide (value d.cmp0≤value d.cmp1))))=
      some (if value d.cmp0≤value d.cmp1 then
        cfg (if rev then .good else .job .routesLeft .reverse) (compared d)
       else stop false (compared d)) := by
    change machine.step ⟨some (.compareDone rev),(none,true),bank cw (store d)
      (TreeBudgetLeWordsTM2.done (decide (value d.cmp0≤value d.cmp1))).stk⟩=_
    apply (congrArg (fun s : K → Bits =>
      machine.step (⟨some (.compareDone rev),(none,true),s⟩ : Cfg))
      (compare_returned_bank d (decide (value d.cmp0≤value d.cmp1)))).trans
    by_cases h : value d.cmp0≤value d.cmp1 <;>
      simp [machine,FinTM2.step,program,TM2.step,TM2.stepAux,cfg,stop,jump,reject,
        TreeBudgetStackRoutine.jump,store,compareReturned,ax,h,compare_pop]
    all_goals
      congr 2
      exact compare_pop d _
  exact weaken (seq sub (once last)) (by omega)

end UAVProof.A4RowsCheck
