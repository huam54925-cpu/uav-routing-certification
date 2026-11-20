import LeanCompletion.UAV.TreeBudgetFeeTailTM2

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition

theorem root_bank (p : TreeBudgetRootFlowTM2.K → Bits) :
    bank prefixW (fun _ => []) p=TreeBudgetTM2Call.banks p (fun _ => []) := by
  funext k; cases k <;> rfl

def afterRoot (p : TreeBudgetRootFlowTM2.K → Bits) : Cfg :=
  ⟨some (.dimension false .reverse),(none,true),TreeBudgetTM2Call.banks p (fun _ => [])⟩

theorem prefix_true_step (out : TreeBudgetRootFlowTM2.Cfg) (hl : out.l=none) (hb : out.var.2=true) :
    machine.step (embed prefixW L.prefix .afterPrefix (fun _ => []) out)=some (afterRoot out.stk) := by
  simp [machine,FinTM2.step,TM2.step,embed,hl,program,TM2.stepAux,hb,
    TreeBudgetStackRoutine.jump,afterRoot,root_bank]

theorem prefix_false_step (out : TreeBudgetRootFlowTM2.Cfg) (hl : out.l=none) (hb : out.var.2=false) :
    machine.step (embed prefixW L.prefix .afterPrefix (fun _ => []) out)=
      some ⟨some .bad,out.var,TreeBudgetTM2Call.banks out.stk (fun _ => [])⟩ := by
  simp [machine,FinTM2.step,TM2.step,embed,hl,program,TM2.stepAux,hb,go,root_bank]
  rfl

theorem init_eq (s : Bits) : initList machine s=start s [] := by
  rw [start,← TreeBudgetRootFlowTM2.init_eq]
  simp only [initList,machine,embed]
  congr 1
  funext k
  cases k with
  | inr k => rfl
  | inl k =>
    rcases k with k | k | k
    · rcases k with ((((i | b) | u) | v) | z) | w
      · fin_cases i <;> rfl
      · cases b <;> rfl
      · cases u; rfl
      · cases v; rfl
      · fin_cases z <;> rfl
      · rcases w with (i | u) | z
        · fin_cases i <;> rfl
        · cases u; rfl
        · fin_cases z <;> rfl
    · fin_cases k <;> rfl
    · cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl

end UAVProof.A4FeeTailMachine
