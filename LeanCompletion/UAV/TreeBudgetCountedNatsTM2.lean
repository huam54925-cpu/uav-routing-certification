import LeanCompletion.UAV.TreeBudgetCountHeaderTM2
import LeanCompletion.UAV.TreeBudgetNatListRuns
import LeanCompletion.UAV.TreeBudgetNatListReadback

namespace UAVProof.TreeBudgetCountedNatsTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition

def linked : TreeBudgetNatListLoop.Linked TreeBudgetListGuardTM2.program where
  tick := rfl
  frame p := by cases p <;> rfl
  emit := rfl
  finish := rfl

theorem handoff (k : ℕ) (r ctx : Bits) :
    TreeBudgetListGuardTM2.atLabel 9 r [] [] [] (TreeBudgetListGuardTM2.marks k) ctx = TreeBudgetNatListLoop.conf 9 r [] (TreeBudgetListGuardTM2.marks k) [] ctx := by
  unfold TreeBudgetListGuardTM2.atLabel TreeBudgetNatListLoop.conf cfg
  congr 1
  funext i; fin_cases i <;> rfl

def result (s ctx : Bits) : TreeBudgetListGuardTM2.Cfg :=
  match parseNat s with
  | some (k,r) => if k ≤ r.length then TreeBudgetNatListLoop.loopEnd k r [] ctx else TreeBudgetListGuardTM2.outcome s ctx
  | none => TreeBudgetListGuardTM2.outcome s ctx

def list_run (s ctx : Bits) : TreeBudgetListGuardTM2.Run (TreeBudgetListGuardTM2.atLabel 0 s [] [] [] [] ctx)
    (result s ctx) (16*(s.length+1)^2) := by
  have head := TreeBudgetListGuardTM2.precheck_run s ctx
  cases hp : parseNat s with
  | none =>
    simp only [result, hp]
    exact weaken head (by nlinarith)
  | some pair =>
    obtain ⟨k,r⟩ := pair
    by_cases h : k ≤ r.length
    · have hg := TreeBudgetListGuardTM2.guard_contract r k.bits [] ctx
      simp [h] at hg
      simp only [TreeBudgetListGuardTM2.outcome, hp, hg, handoff] at head
      have hr := congrArg List.length (parseNat_canonical s r k hp)
      simp only [List.length_append] at hr
      have tail := TreeBudgetNatListLoop.loop_run linked k r [] ctx s.length (by simp; omega)
      simp only [result, hp, if_pos h]
      apply weaken (EvalsToInTime.trans TreeBudgetListGuardTM2.machine.step _ _ _ _ _ head tail)
      have hm := Nat.mul_le_mul_right (4*s.length+8) (show k+1 ≤ s.length+1 by omega)
      nlinarith
    · simp only [result, hp, if_neg h]
      exact weaken head (by nlinarith)

def readList (c : TreeBudgetListGuardTM2.Cfg) : Option (List ℕ × Bits) :=
  if c.l = some 17 then (TreeBudgetNatListLoop.fields (c.stk 2).length (c.stk 2)).map (fun ns => (ns,c.stk 0))
  else none

theorem refines (s ctx : Bits) :
    readList (result s ctx) = (TreeBudgetCostedParsing.parseNatsD s).value ∧
      (result s ctx).stk 5 = ctx := by
  rw [TreeBudgetCostedParsing.parseNatsD_value]
  cases hp : parseNat s with
  | none =>
    obtain ⟨hl,hc⟩ := TreeBudgetListGuardTM2.header_invalid s ctx hp
    simp [result, TreeBudgetListGuardTM2.outcome, hp, readList, parseNats, parseList, hl, hc]
  | some pair =>
    obtain ⟨k,r⟩ := pair
    by_cases h : k ≤ r.length
    · have ht := TreeBudgetNatListLoop.loop_contract k r [] ctx
      cases hm : parseMany parseNat k r with
      | none =>
        simp only [hm] at ht
        simp [result, hp, h, parseNats, parseList, hm, ht, readList]
      | some out =>
        obtain ⟨ns,t⟩ := out
        simp [hm] at ht
        simp [result, hp, h, parseNats, parseList, hm, ht, readList, TreeBudgetNatListLoop.conf, cfg,
          tapes, TreeBudgetNatListLoop.ports, TreeBudgetNatListLoop.base]
        simpa using TreeBudgetNatListLoop.fields_readback ns
    · have hg := TreeBudgetListGuardTM2.guard_contract r k.bits [] ctx
      simp [h] at hg
      simp [result, hp, h, parseNats, parseList, TreeBudgetListGuardTM2.outcome, readList, hg]

end UAVProof.TreeBudgetCountedNatsTM2
