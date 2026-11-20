import LeanCompletion.UAV.TreeBudgetFeeTailTotal
import LeanCompletion.UAV.TreeBudgetInstanceSpec
import LeanCompletion.UAV.TreeBudgetInstanceEntry

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
set_option synthInstance.maxSize 2048
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- All decoded instance fields remain on distinct output stacks in forward order. -/
def InstanceFields (a : TreeBudgetRootFlowSpec.Raw) (f : A4FeeTailSpec.Fields) (out : Cfg) : Prop :=
  out.stk (.inl (.inl (.inr (.inr 0))))=a.routes.bits ∧
  out.stk dimension=a.vertices.bits ∧
  out.stk (.inl (.inl TreeBudgetParentPrefixTM2.parsedRoot))=a.root.bits ∧
  out.stk parents=a.parents.flatMap encodeNat ∧
  out.stk (.inl TreeBudgetRootFlowTM2.demands)=a.demands.flatMap encodeNat ∧
  out.stk (.inr (.result .nums))=f.nums.flatMap encodeInt ∧
  out.stk (.inr (.result .dens))=f.dens.flatMap encodeNat ∧
  out.stk (.inr (.result .bnum))=encodeInt f.budgetNum ∧
  out.stk (.inr (.result .bden))=encodeNat f.budgetDen ∧ out.stk src=[]

def SavedInstance (s : Bits) (out : Cfg) : Prop := ∀ a f,
  TreeBudgetRootFlowSpec.parse s=some a → TreeBudgetRootFlowSpec.accepted s=true →
  A4FeeTailSpec.read a.vertices a.rest=some f → InstanceFields a f out

theorem instance_polynomial (s ctx : Bits) :
    ∃ out, Nonempty (Run (start s ctx) out (65536*(s.length+1)^4)) ∧ out.l=none ∧
      out.var.2=(TreeBudgetSparseVerifier.parseInstance s).isSome ∧
      out.stk context=ctx ∧ SavedInstance s out := by
  obtain ⟨p,⟨pre⟩,pl,pv,pk,ph⟩ := TreeBudgetRootFlowTM2.root_flow_polynomial s ctx
  have call := call_run prefixW L.prefix .afterPrefix (fun _ => [])
    TreeBudgetRootFlowTM2.program program (fun _ => rfl) pre
  have pow₂ : (s.length+1)^2 ≤ (s.length+1)^4 :=
    Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 4)
  have pos : 1 ≤ (s.length+1)^4 := Nat.one_le_pow 4 (s.length+1) (by omega)
  by_cases good : TreeBudgetRootFlowSpec.accepted s=true
  · obtain ⟨a,pa⟩ := A4FeeTailSpec.root_parse_of_accept s good
    obtain ⟨hn,_,hok⟩ := A4FeeTailSpec.root_contract s a pa good
    obtain ⟨pm,pn,pr,pp,pH,pt,pc⟩ := TreeBudgetRootFlowTM2.saved_fields s ctx p pk ph a pa hok
    obtain ⟨bP,bD,bn,bt⟩ := A4FeeTailSpec.fee_input_bounds s a pa good
    let base := TreeBudgetTM2Call.banks p.stk (fun _ : Aux => [])
    have hd : base dimension=a.vertices.bits := pn
    have hp : base parents=a.parents.flatMap encodeNat := pp
    have ht : base src=a.rest := pt
    obtain ⟨out,⟨fee⟩,hl,hv,hkeep,hsaved⟩ := fee_tail_run base a.vertices a.parents s.length
      hd hp hn (fun _ => rfl) bP bD bn (by simpa only [ht] using bt)
    have step := once (prefix_true_step p pl (pv.trans good))
    have allRun := seq (seq call step) fee
    refine ⟨out,⟨weaken allRun ?_⟩,hl,?_,?_,?_⟩
    · nlinarith only [pow₂,pos]
    · rw [← A4FeeTailSpec.accepted_eq_parseInstance]
      simpa [A4FeeTailSpec.accepted,good,pa,ht] using hv
    · exact (hkeep TreeBudgetRootFlowTM2.context (by decide)).trans pc
    · intro a' f pa' _ hf
      have ea : a'=a := by simpa only [pa,Option.some.injEq] using pa'.symm
      subst a'
      rw [← ht] at hf
      rw [hsaved f hf]
      simp only [InstanceFields,halted,feeStore,budgetStore,fieldStore,groupStore,wireWords,
        groupField,Bool.false_eq_true,ite_false,ite_true,Function.update_apply]
      simp [base,TreeBudgetTM2Call.banks,dimension,parents,src,pm,pn,pr,pp,pH]
  · have bad : TreeBudgetRootFlowSpec.accepted s=false := Bool.eq_false_iff.mpr good
    let c : Cfg := ⟨some .bad,p.var,TreeBudgetTM2Call.banks p.stk (fun _ => [])⟩
    have step : machine.step (embed prefixW L.prefix .afterPrefix (fun _ => []) p)=some c :=
      prefix_false_step p pl (pv.trans bad)
    have finalRun := seq (seq call (once step)) (bad_run c rfl)
    refine ⟨_,⟨weaken finalRun ?_⟩,rfl,?_,pk.1,?_⟩
    · nlinarith only [pos]
    · rw [← A4FeeTailSpec.accepted_eq_parseInstance]
      simp [halted,A4FeeTailSpec.accepted,bad]
    · intro a f pa ha hf
      simp [bad] at ha

/-- The standard raw input tape needs no preloaded fields or prepared suffix. -/
theorem instance_from_init (s : Bits) :
    ∃ out, Nonempty (EvalsToInTime machine.step (initList machine s) (some out)
      (65536*(s.length+1)^4)) ∧ out.l=none ∧
      out.var.2=(TreeBudgetSparseVerifier.parseInstance s).isSome ∧
      out.stk context=[] ∧ SavedInstance s out := by
  rw [init_eq]
  exact instance_polynomial s []

end UAVProof.A4FeeTailMachine
