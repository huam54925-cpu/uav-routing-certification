import LeanCompletion.UAV.TreeBudgetRowCheckCleanup
import LeanCompletion.UAV.TreeBudgetNaturalLookupRuns

namespace UAVProof.A4RowCheck
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetSemanticRegisterTM2
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

abbrev acc (i : Fin 3) : K := reg ⟨20+i.val,by omega⟩
abbrev tableReg (i : Fin 3) : K := reg ⟨2+i.val,by omega⟩
abbrev indexReg (b : Bool) : K := reg (if b then 5 else 15)
abbrev set (s : K → Bits) (i : Fin 35) (u : Bits) := Function.update s (reg i) u

theorem weighted_input (s : K → Bits) (i : Fin 3)
    (h₁ : s (reg 28)=[]) (h₂ : s (reg 29)=[]) :
    bank (mw i) s (TreeBudgetWeightedTM2.cfg 0 false
      (s (reg 26)) (s (reg 27)) (s (acc i)) [] [] (s (reg 30))).stk=s := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases i <;> fin_cases k <;>
      simp [bank,mw,mulGet,acc,reg,TreeBudgetWeightedTM2.cfg,h₁,h₂]

theorem weighted_output (s : K → Bits) (i : Fin 3) (out : Bits)
    (h₁ : s (reg 28)=[]) (h₂ : s (reg 29)=[]) :
    bank (mw i) s (TreeBudgetWeightedTM2.stopped out (s (reg 30))).stk=
      Function.update (set (set s 26 []) 27 []) (acc i) out := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases i <;> fin_cases k <;>
      simp [bank,mw,mulGet,acc,reg,set,TreeBudgetWeightedTM2.stopped,
        TreeBudgetWeightedTM2.cfg,h₁,h₂]

def weighted_block (l next : PC) (i : Fin 3) (hi : instructions l=.weighted (mw i) next)
    (s : K → Bits) (h₁ : s (reg 28)=[]) (h₂ : s (reg 29)=[]) :
    Run instructions (cfg l s)
      (cfg next (Function.update (set (set s 26 []) 27 []) (acc i)
        (TreeBudgetWeightedTM2.weighted (s (reg 26)) (s (reg 27)) (s (acc i)))))
      (16*((s (reg 26)).length+(s (reg 27)).length+(s (acc i)).length+1)^2+3) := by
  have run := weighted_run instructions l next (mw i) hi s
    (s (reg 26)) (s (reg 27)) (s (acc i)) (s (reg 30))
  rw [weighted_input s i h₁ h₂,weighted_output s i _ h₁ h₂] at run
  exact run

theorem compare_input (s : K → Bits) (h₁ : s (reg 33)=[]) (h₂ : s (reg 34)=[]) :
    bank cw s (TreeBudgetLeWordsTM2.cfg none true (s (reg 31)) (s (reg 32))).stk=s := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;>
      simp [bank,cw,cmpGet,reg,TreeBudgetLeWordsTM2.cfg,TreeBudgetAddWordsTM2.tapes,h₁,h₂]

theorem compare_output (s : K → Bits) (h₁ : s (reg 33)=[]) (h₂ : s (reg 34)=[]) :
    bank cw s (TreeBudgetAddWordsTM2.tapes [] [] [] [])=set (set s 31 []) 32 [] := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;>
      simp [bank,cw,cmpGet,reg,set,TreeBudgetAddWordsTM2.tapes,h₁,h₂]

def compare_block (l yes no : PC) (hi : instructions l=.le cw yes no)
    (s : K → Bits) (h₁ : s (reg 33)=[]) (h₂ : s (reg 34)=[]) :
    Run instructions (cfg l s)
      (cfg (if value (s (reg 31))≤value (s (reg 32)) then yes else no)
        (set (set s 31 []) 32 []))
      ((s (reg 31)).length+(s (reg 32)).length+3) := by
  have run := le_run instructions l yes no cw hi s (s (reg 31)) (s (reg 32))
  rw [compare_input s h₁ h₂,compare_output s h₁ h₂] at run
  exact run

theorem lookup_input (s : K → Bits) (i : Fin 3) (atRoot : Bool)
    (hc : ∀ k, s (.inl k)=[]) (h₁ : s (reg 25)=[]) (h₂ : s (reg 23)=[]) :
    bank (lw i atRoot) s (A4NaturalLookup.start
      (s (tableReg i)) (s (indexReg atRoot))).stk=s := by
  funext k
  cases k with
  | inl k =>
    rcases k with j|b
    · fin_cases j <;> simp [bank,lw,lookupGet,A4NaturalLookup.start,A4NaturalLookup.store,hc]
    · cases b <;> simp [bank,lw,lookupGet,A4NaturalLookup.start,A4NaturalLookup.store,hc]
  | inr k => fin_cases i <;> cases atRoot <;> fin_cases k <;>
      simp [bank,lw,lookupGet,A4NaturalLookup.start,A4NaturalLookup.store,
        tableReg,indexReg,reg,h₁,h₂]

theorem lookup_output (s : K → Bits) (i : Fin 3) (atRoot : Bool) (out : Bits)
    (hc : ∀ k, s (.inl k)=[]) (h₁ : s (reg 25)=[]) :
    bank (lw i atRoot) s (A4NaturalLookup.stopped
      (s (tableReg i)) (s (indexReg atRoot)) out).stk=set s 23 out := by
  funext k
  cases k with
  | inl k =>
    rcases k with j|b
    · fin_cases j <;> simp [bank,lw,lookupGet,A4NaturalLookup.stopped,A4NaturalLookup.store,set,reg,hc]
    · cases b <;> simp [bank,lw,lookupGet,A4NaturalLookup.stopped,A4NaturalLookup.store,set,reg,hc]
  | inr k => fin_cases i <;> cases atRoot <;> fin_cases k <;>
      simp [bank,lw,lookupGet,A4NaturalLookup.stopped,A4NaturalLookup.store,
        tableReg,indexReg,reg,set,h₁]

def lookup_block (l next : PC) (i : Fin 3) (atRoot : Bool)
    (hi : instructions l=.lookup (lw i atRoot) next)
    (s : K → Bits) (before after : List ℕ) (a : ℕ)
    (ht : s (tableReg i)=(before++a::after).flatMap encodeNat)
    (hn : s (indexReg atRoot)=before.length.bits)
    (hc : ∀ k, s (.inl k)=[]) (h₁ : s (reg 25)=[]) (h₂ : s (reg 23)=[]) :
    Run instructions (cfg l s) (cfg next (set s 23 a.bits))
      (256*((s (tableReg i)).length+(s (indexReg atRoot)).length+1)^2+2) := by
  have run := TreeBudgetSemanticRegisterTM2.lookup_run instructions l next (lw i atRoot) hi s
    ((before++a::after).flatMap encodeNat) before.length.bits a.bits _
    (A4NaturalLookup.lookup_run before after a)
  rw [← ht,← hn,lookup_input s i atRoot hc h₁ h₂,
    lookup_output s i atRoot a.bits hc h₁] at run
  exact run

end UAVProof.A4RowCheck
