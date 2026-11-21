import LeanCompletion.UAV.TreeBudgetFeeScalingTM2

namespace UAVProof.A4FeeScaling.Entry
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open Turing StateTransition Turing.TM2.Stmt
set_option synthInstance.maxSize 8192
set_option maxRecDepth 50000

inductive L
  | paired (l : A4PairedParser.L)
  | afterPaired
  | scaling (l : TreeBudgetRegisterTM2.Label PC)
  | done
  deriving DecidableEq, Fintype

abbrev Cfg := Configuration K L
def pw : Wiring A4PairedParser.K K :=
  ⟨old,(fun k => match k with | .inl i => some i | _ => none),
    by intro i; rfl, by intro k i h; rcases k with k | k <;> simpa using h⟩
def sw : Wiring K K := ⟨id,some,by intro k; rfl,by intro k i h; simpa using h⟩

def program : L → Statement K L
  | .paired l => compile pw L.paired .afterPaired (A4PairedParser.program l)
  | .afterPaired => branch Prod.snd
      (TreeBudgetStackRoutine.jump (.scaling (.pc .copyNums)))
      (load (fun _ => (none,false)) halt)
  | .scaling l => compile sw L.scaling .done (TreeBudgetRegisterTM2.program instr l)
  | .done => halt

def machine : FinTM2 where
  K := K
  k₀ := old A4PairedParser.machine.k₀
  k₁ := wr .fees
  Γ _ := Bool
  Λ := L
  main := .paired A4PairedParser.machine.main
  σ := State
  initialState := (none,true)
  m := program

def after (p : A4PairedParser.Cfg) : Cfg :=
  ⟨some .afterPaired,p.var,store {saved:=p.stk}⟩
def halted (v : State) (s : K → Bits) : Cfg := ⟨none,v,s⟩
def view (p : Cfg) : A4PairedParser.Cfg := ⟨none,p.var,fun k => p.stk (old k)⟩
abbrev Run (a b : Cfg) (t : ℕ) := EvalsToInTime machine.step a (some b) t
def seq {a b c : Cfg} {u v : ℕ} (h : Run a b u) (g : Run b c v) : Run a c (u+v) := by
  simpa only [Nat.add_comm] using EvalsToInTime.trans machine.step u v a b (some c) h g

theorem paired_bank (s : A4PairedParser.K → Bits) : bank pw (fun _ => []) s=store {saved:=s} := by
  funext k; rcases k with k | k | k <;> rfl
theorem scale_bank (base s : K → Bits) : bank sw base s=s := by
  funext k; rfl

theorem init_eq (s : Bits) : initList machine s=
    embed pw L.paired .afterPaired (fun _ => []) (initList A4PairedParser.machine s) := by
  simp only [initList,machine,embed,Option.elim_some,paired_bank]
  congr 1
  funext k
  rcases k with k | k
  · by_cases h : k=A4PairedParser.machine.k₀
    · subst k; rfl
    · simp [store,old,h]
      exact dif_neg h
  · rcases k with k | k <;> rfl

theorem paired_return (p : A4PairedParser.Cfg) (hl : p.l=none) :
    embed pw L.paired .afterPaired (fun _ => []) p=after p := by
  simp [embed,hl,paired_bank,after]

theorem true_step (p : A4PairedParser.Cfg) (hb : p.var.2=true) :
    machine.step (after p)=some
      (embed sw L.scaling .done (fun _ => []) (cfg .copyNums {saved:=p.stk})) := by
  simp [machine,FinTM2.step,TM2.step,program,after,TM2.stepAux,hb,
    TreeBudgetStackRoutine.jump,embed,cfg,TreeBudgetRegisterTM2.cfg,scale_bank]

theorem false_step (p : A4PairedParser.Cfg) (hb : p.var.2=false) :
    machine.step (after p)=some (halted (none,false) (store {saved:=p.stk})) := by
  simp [machine,FinTM2.step,TM2.step,program,after,TM2.stepAux,hb,halted]

theorem return_step (d : Data) :
    machine.step (embed sw L.scaling .done (fun _ => [])
      (TreeBudgetRegisterTM2.stopped (store d)))=some (halted (none,true) (store d)) := by
  simp [machine,FinTM2.step,TM2.step,program,TM2.stepAux,halted,embed,
    TreeBudgetRegisterTM2.stopped,scale_bank]

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool; infer_instance

end UAVProof.A4FeeScaling.Entry
