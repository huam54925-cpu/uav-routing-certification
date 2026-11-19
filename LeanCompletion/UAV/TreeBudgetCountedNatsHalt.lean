import LeanCompletion.UAV.TreeBudgetCountedNatsTM2
import LeanCompletion.UAV.TreeBudgetListCleanup

namespace UAVProof.TreeBudgetCountedNatsTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
open TreeBudgetListCleanup (workCells)
open TreeBudgetListGuardTM2 (guardEnd atLabel)
open TreeBudgetNatListLoop (loopEnd)

theorem guard_space (r d saved ctx : Bits) :
    workCells (guardEnd r d saved ctx) ≤ r.length+d.length+saved.length := by
  induction r generalizing d saved with
  | nil =>
    cases hp : TreeBudgetListGuardTM2.predWord d with
    | none => simp [guardEnd, hp, workCells, atLabel, TreeBudgetListGuardTM2.layout, TreeBudgetListGuardTM2.marks]
    | some e =>
      have hs := TreeBudgetListGuardTM2.pred_spec d
      simp [hp] at hs
      simp [guardEnd, hp, workCells, atLabel, TreeBudgetListGuardTM2.layout, hs]
  | cons b r ih =>
    cases hp : TreeBudgetListGuardTM2.predWord d with
    | none =>
      simp [guardEnd, hp, workCells, atLabel, TreeBudgetListGuardTM2.layout, TreeBudgetListGuardTM2.marks]
    | some e =>
      have hs := TreeBudgetListGuardTM2.pred_spec d
      simp [hp] at hs
      rw [guardEnd, hp]
      have ht := ih e (b :: saved)
      simp only [List.length_cons, hs.2] at ht ⊢
      omega

theorem loop_space (k : ℕ) (r acc ctx : Bits) :
    workCells (loopEnd k r acc ctx) ≤ k+r.length+acc.length := by
  induction k generalizing r acc with
  | zero => simp [loopEnd, workCells, TreeBudgetNatListLoop.conf, cfg, tapes, TreeBudgetNatListLoop.ports, TreeBudgetNatListLoop.base]
  | succ k ih =>
    cases hp : parseNat r with
    | none =>
      simp [loopEnd, hp, workCells, TreeBudgetNatListLoop.conf, cfg, tapes, TreeBudgetNatListLoop.ports, TreeBudgetNatListLoop.base]
      omega
    | some out =>
      obtain ⟨n,t⟩ := out
      have he := congrArg List.length (parseNat_canonical r t n hp)
      simp only [List.length_append] at he
      have ht := ih t ((encodeNat n).reverse ++ acc)
      simp only [List.length_append, List.length_reverse] at ht
      simp only [loopEnd, hp]; omega

theorem result_space (s ctx : Bits) : workCells (result s ctx) ≤ 2*s.length := by
  cases hp : parseNat s with
  | none =>
    cases hw : parseWord s with
    | none => simp [result, hp, TreeBudgetListGuardTM2.outcome, TreeBudgetListGuardTM2.headerEnd, hw,
        workCells, atLabel, TreeBudgetListGuardTM2.layout]
    | some pair =>
      obtain ⟨bs,r⟩ := pair
      rw [parseWord_consumed s bs r hw, TreeBudgetCanonicalDigits.parseNat_framed] at hp
      cases hc : lastDigit bs true with
      | true => simp [hc] at hp
      | false =>
        have hn : parseNat s = none := by rw [parseWord_consumed s bs r hw, TreeBudgetCanonicalDigits.parseNat_framed]; simp [hc]
        simp [result, hn, TreeBudgetListGuardTM2.outcome, TreeBudgetListGuardTM2.headerEnd, hw, hc,
          workCells, atLabel, TreeBudgetListGuardTM2.layout]
  | some pair =>
    obtain ⟨k,r⟩ := pair
    have hl := congrArg List.length (parseNat_canonical s r k hp)
    simp only [List.length_append, encodeNat_length] at hl
    by_cases h : k ≤ r.length
    · simp only [result, hp, if_pos h]
      have hs := loop_space k r [] ctx
      simp only [List.length_nil, Nat.add_zero] at hs
      omega
    · simp only [result, hp, if_neg h, TreeBudgetListGuardTM2.outcome]
      have hs := guard_space r k.bits [] ctx
      simp only [Nat.size_eq_bits_len, List.length_nil, Nat.add_zero] at hs
      omega

theorem result_labels (s ctx : Bits) :
    ((result s ctx).l = some 10 ∨ (result s ctx).l = some 17) ∧ (result s ctx).var = (none,true) := by
  have hg (r d saved c : Bits) : ((guardEnd r d saved c).l = some 10 ∨
      (guardEnd r d saved c).l = some 9) ∧ (guardEnd r d saved c).var = (none,true) := by
    induction r generalizing d saved with
    | nil => cases hp : TreeBudgetListGuardTM2.predWord d <;> simp [guardEnd, hp, atLabel]
    | cons b r ih =>
      cases hp : TreeBudgetListGuardTM2.predWord d with
      | none => simp [guardEnd, hp, atLabel]
      | some e => rw [guardEnd, hp]; exact ih e (b :: saved)
  have he (k : ℕ) (r acc c : Bits) : ((loopEnd k r acc c).l = some 10 ∨
      (loopEnd k r acc c).l = some 17) ∧ (loopEnd k r acc c).var = (none,true) := by
    induction k generalizing r acc with
    | zero => simp [loopEnd, TreeBudgetNatListLoop.conf, cfg]
    | succ k ih =>
      cases hp : parseNat r with
      | none => simp [loopEnd, hp, TreeBudgetNatListLoop.conf, cfg]
      | some out => obtain ⟨n,t⟩ := out; simpa only [loopEnd, hp] using ih t ((encodeNat n).reverse ++ acc)
  cases hp : parseNat s with
  | none =>
    have hh := TreeBudgetListGuardTM2.header_invalid s ctx hp
    simp only [result, hp, TreeBudgetListGuardTM2.outcome, hh.1, true_or, true_and]
    unfold TreeBudgetListGuardTM2.headerEnd
    split <;> (try split) <;> rfl
  | some pair =>
    obtain ⟨k,r⟩ := pair
    by_cases h : k ≤ r.length
    · simpa only [result, hp, if_pos h] using he k r [] ctx
    · have hh := TreeBudgetListGuardTM2.guard_contract r k.bits [] ctx
      simp [h] at hh
      simp only [result, hp, if_neg h, TreeBudgetListGuardTM2.outcome, hh.1, true_or, true_and]
      exact (hg r k.bits [] ctx).2

def stopped (s ctx : Bits) : TreeBudgetListGuardTM2.Cfg :=
  let c := result s ctx
  if c.l = some 17 then { c with l := none } else TreeBudgetListCleanup.done (c.stk 0) (c.stk 5)

def list_halts (s ctx : Bits) : TreeBudgetListGuardTM2.Run
    (atLabel 0 s [] [] [] [] ctx) (stopped s ctx) (20*(s.length+1)^2) := by
  let c := result s ctx
  have hl := result_labels s ctx
  have hs := result_space s ctx
  have head := list_run s ctx
  by_cases h : (result s ctx).l = some 10
  · have hc : c = TreeBudgetListCleanup.cfg (c.stk 0) (c.stk 1) (c.stk 2) (c.stk 3)
        (c.stk 4) (c.stk 6) (c.stk 5) := by
      cases hc' : c with
      | mk l v stk =>
        change c.l = some 10 at h
        have hv : c.var = (none,true) := hl.2
        rw [hc'] at hv h
        dsimp at hv h
        subst l; subst v
        unfold TreeBudgetListCleanup.cfg
        congr 1
        funext i; fin_cases i <;> rfl
    have tail := TreeBudgetListCleanup.clean_run (M := TreeBudgetListGuardTM2.program) rfl (2*s.length)
      (c.stk 0) (c.stk 1) (c.stk 2) (c.stk 3) (c.stk 4) (c.stk 6) (c.stk 5) hs
    rw [← hc] at tail
    have run := EvalsToInTime.trans TreeBudgetListGuardTM2.machine.step _ _ _ _ _ head tail
    apply weaken (by simpa [stopped, h, c] using run)
    nlinarith
  · have h := hl.1.resolve_left h
    have last : TreeBudgetListGuardTM2.machine.step c = some { c with l := none } := by
      change c.l = some 17 at h
      cases hc : c with
      | mk l v stk =>
        rw [hc] at h; dsimp at h; subst l; rfl
    have run := EvalsToInTime.trans TreeBudgetListGuardTM2.machine.step _ _ _ _ _ head (once last)
    apply weaken (by simpa [stopped, h, c] using run)
    nlinarith

def readStopped (c : TreeBudgetListGuardTM2.Cfg) : Option (List ℕ × Bits) :=
  if c.var.2 then (TreeBudgetNatListLoop.fields (c.stk 2).length (c.stk 2)).map (fun ns => (ns,c.stk 0))
  else none

theorem halted_refines (s ctx : Bits) : readStopped (stopped s ctx) =
    (TreeBudgetCostedParsing.parseNatsD s).value ∧ (stopped s ctx).stk 5 = ctx := by
  have hr := refines s ctx
  have hl := result_labels s ctx
  rcases hl.1 with h | h <;>
    simpa [readStopped, stopped, readList, TreeBudgetListCleanup.done, TreeBudgetListCleanup.tapes, h, hl.2] using hr

theorem terminal (s ctx : Bits) : TreeBudgetListGuardTM2.machine.step (stopped s ctx) = none := by
  unfold stopped
  dsimp only
  split <;> rfl

def list_from_init (s : Bits) : TreeBudgetListGuardTM2.Run (initList TreeBudgetListGuardTM2.machine s)
    (stopped s []) (20*(s.length+1)^2) := by
  rw [TreeBudgetListGuardTM2.init_eq]
  exact list_halts s []

end UAVProof.TreeBudgetCountedNatsTM2
