import LeanCompletion.UAV.TreeBudgetPairedParserTM2

namespace UAVProof.A4PairedParser
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open TreeBudgetSparseNPBridge Turing StateTransition

set_option synthInstance.maxSize 4096
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem instance_bank (y : Bits) (i : A4FeeTailMachine.K → Bits) :
    bank iw (base y) i=store i (certBase y) := by
  funext k; rcases k with i | c | u <;> rfl

theorem records_bank (i : A4FeeTailMachine.K → Bits) (y : Bits)
    (c : A4CertRecords.K → Bits) :
    bank cw (store i (certBase y)) c=store i c := by
  funext k; rcases k with i | c | u <;> rfl

theorem init_eq (s : Bits) : initList machine s=
    cfg framePorts (fun _ => []) (.frame .marker) none true s [] [] := by
  simp only [initList,machine,cfg]
  congr 1
  funext k
  rcases k with i | c | u
  · simp [tapes,framePorts,scratch,ik,ck]
  · by_cases h : c=A4CertRecords.savedBody <;> simp [tapes,framePorts,scratch,ik,ck,h]
  · cases u; rfl

theorem split_layout (x y : Bits) :
    cfg framePorts (fun _ => []) (.instanceCall A4FeeTailMachine.machine.main) none true y [] x =
      embed iw L.instanceCall .afterInstance (base y) (initList A4FeeTailMachine.machine x) := by
  simp only [cfg,embed,initList,instance_bank]
  congr 1
  funext k
  rcases k with i | c | u
  · by_cases h : i=A4FeeTailMachine.machine.k₀
    · subst i; rfl
    · simp [tapes,framePorts,store,scratch,ik,ck,h]
      exact dif_neg h
  · by_cases h : c=A4CertRecords.savedBody <;>
      simp [tapes,framePorts,store,scratch,ik,ck,certBase,A4CertRecords.start,h]
  · cases u; rfl

def split_run (x y : Bits) : Run (initList machine (pairWire (x,y)))
    (embed iw L.instanceCall .afterInstance (base y) (initList A4FeeTailMachine.machine x))
      (3*x.length+2) := by
  have h := framed_run framePorts (fun _ => []) L.frame
    (.instanceCall A4FeeTailMachine.machine.main) .bad false program (fun _ => rfl)
    x y none true [] []
  rw [init_eq]
  simpa only [Bool.not_false,Bool.true_or,ite_true,List.reverse_nil,List.nil_append,
    List.append_nil,List.length_nil,Nat.add_zero,split_layout,pairWire] using h

theorem instance_return (p : A4FeeTailMachine.Cfg) (y : Bits) (hl : p.l=none) :
    embed iw L.instanceCall .afterInstance (base y) p=afterInstance p y := by
  simp [embed,hl,instance_bank,afterInstance]

theorem instance_true (p : A4FeeTailMachine.Cfg) (y : Bits) (hb : p.var.2=true) :
    machine.step (afterInstance p y)=
      some ⟨some (.dimension .reverse),(none,true),store p.stk (certBase y)⟩ := by
  simp [machine,FinTM2.step,TM2.step,afterInstance,program,hb,TM2.stepAux,
    TreeBudgetStackRoutine.jump]
  rfl

theorem instance_false (p : A4FeeTailMachine.Cfg) (y : Bits) (hb : p.var.2=false) :
    machine.step (afterInstance p y)=some (stopped (none,false) (store p.stk (certBase y))) := by
  simp [machine,FinTM2.step,TM2.step,afterInstance,program,hb,TM2.stepAux,stopped]

theorem dimension_layout (i : A4FeeTailMachine.K → Bits) (n : ℕ) (y : Bits)
    (hn : i A4FeeTailMachine.dimension=n.bits) :
    tapes dimPorts (store i (certBase y)) n.bits [] []=store i (certBase y) ∧
    tapes dimPorts (store i (certBase y)) n.bits [] n.bits=
      store i (A4CertRecords.start n y []).stk := by
  have eq (v : Bits) : tapes dimPorts (store i (certBase y)) n.bits [] v=
      Function.update (store i (certBase y)) (ck (.inr .dim)) v := by
    rw [← hn]
    exact TreeBudgetRootFlowTM2.restored dimPorts (store i (certBase y)) v rfl
  constructor
  · rw [eq]
    apply Function.update_eq_self_iff.mpr
    rfl
  · rw [eq]
    funext k
    rcases k with j | c | u
    · simp [ck,store]
    · by_cases hd : c = .inr .dim <;>
        simp [Function.update_apply,ck,store,certBase,A4CertRecords.start,hd]
    · cases u; rfl

def dimension_run (i : A4FeeTailMachine.K → Bits) (n : ℕ) (y : Bits)
    (hn : i A4FeeTailMachine.dimension=n.bits) :
    Run ⟨some (.dimension .reverse),(none,true),store i (certBase y)⟩
      (embed cw L.recordsCall .afterRecords (store i (certBase y)) (A4CertRecords.start n y []))
      (2*n.bits.length+2) := by
  have h := TreeBudgetStackRoutine.copy_run dimPorts (store i (certBase y)) L.dimension
    (.recordsCall A4CertRecords.machine.main) false program (fun _ => rfl) n.bits []
  obtain ⟨h₀,h₁⟩ := dimension_layout i n y hn
  simp only [Bool.false_eq_true,ite_false,List.append_nil,TreeBudgetStackRoutine.conf,h₀,h₁] at h
  simpa only [embed,A4CertRecords.start,Option.elim_some,records_bank] using h

theorem records_return (i : A4FeeTailMachine.K → Bits) (y : Bits)
    (p : A4CertRecords.Cfg) (hl : p.l=none) :
    machine.step (embed cw L.recordsCall .afterRecords (store i (certBase y)) p)=
      some (stopped p.var (store i p.stk)) := by
  simp [machine,FinTM2.step,TM2.step,embed,hl,program,TM2.stepAux,stopped,records_bank]

def split_truncated (s : Bits) (h : parseWord s=none) :
    Run (initList machine s) (cfg framePorts (fun _ => []) .bad none true [] [] [])
      (2*s.length+2) := by
  have hr := truncated_run framePorts (fun _ => []) L.frame
    (.instanceCall A4FeeTailMachine.machine.main) .bad false program (fun _ => rfl)
    s h none true [] []
  rw [init_eq]
  simpa only [List.length_nil,Nat.add_zero] using hr

theorem bad_step (stk : K → Bits) (v : State) :
    machine.step ⟨some .bad,v,stk⟩=some (stopped (none,false) stk) := by rfl

end UAVProof.A4PairedParser
