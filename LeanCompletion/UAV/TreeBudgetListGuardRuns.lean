import LeanCompletion.UAV.TreeBudgetListGuardTM2

namespace UAVProof.TreeBudgetListGuardTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 StateTransition

def predWord : Bits → Option Bits
  | [] => none
  | true :: ds => some (false :: ds)
  | false :: ds => (predWord ds).map (true :: ·)

theorem pred_spec (d : Bits) : match predWord d with
    | none => value d = 0
    | some e => value d = value e + 1 ∧ e.length = d.length := by
  induction d with
  | nil => rfl
  | cons b ds ih =>
    cases b with
| true => simp [predWord, value, Nat.bit]
    | false =>
      cases hp : predWord ds with
      | none => simp [hp] at ih; simp [predWord, hp, value, Nat.bit, ih]
      | some e =>
        simp [hp] at ih
        simp [predWord, hp, value, Nat.bit, ih]; omega

abbrev marks (n : ℕ) := List.replicate n true
abbrev Run (a b : Cfg) (t : ℕ) := EvalsToInTime machine.step a (some b) t

def ones_run (n : ℕ) (r d s c : Bits) :
    Run (atLabel 5 r d (marks n) s [] c) (atLabel 6 r (marks n ++ d) [] s [] c) (n+1) := by
  induction n generalizing d with
  | zero => exact once (ones_empty r d s [] c)
  | succ n ih =>
    have h := prepend (ones_cons r d (marks n) s [] c) (ih (true :: d))
    have he : true :: marks n = marks (n+1) := (List.replicate_succ ..).symm
    rw [he] at h
    have ht : marks (n+1) ++ d = marks n ++ true :: d := by
      simp [marks, List.replicate_succ', List.append_assoc]
    rw [ht]
    exact h

def clear_run (n : ℕ) (r s c : Bits) :
    Run (atLabel 7 r [] (marks n) s [] c) (atLabel 8 r [] [] s [] c) (n+1) := by
  induction n with
  | zero => exact once (clear_empty r s [] c)
  | succ n ih => exact prepend (clear_cons r (marks n) s [] c) ih

def borrowed (r d s c : Bits) (z : ℕ) : Cfg :=
  match predWord d with
  | none => atLabel 8 r [] [] s [] c
  | some e => atLabel 6 r (marks z ++ e) [] s [] c

def borrow_run (r d s c : Bits) (z : ℕ) :
    Run (atLabel 4 r d (marks z) s [] c) (borrowed r d s c z) (2*d.length+z+2) := by
  induction d generalizing z with
  | nil => simpa [borrowed, predWord] using prepend (borrow_empty r (marks z) s [] c) (clear_run z r s c)
  | cons b ds ih =>
    cases b with
    | true =>
      have h := prepend (borrow_one r ds (marks z) s [] c) (ones_run z r (false :: ds) s c)
      exact weaken h (by simp)
    | false =>
      have h := prepend (borrow_zero r ds (marks z) s [] c) (ih (z+1))
      have he : borrowed r ds s c (z+1) = borrowed r (false :: ds) s c z := by
        cases hp : predWord ds <;> simp [borrowed, predWord, hp, marks, List.replicate_succ']
      rw [he] at h
      exact weaken h (by simp; omega)

def restore_run (s r tokens c : Bits) :
    Run (atLabel 8 r [] [] s tokens c)
      (atLabel 9 (s.reverse ++ r) [] [] [] (marks s.length ++ tokens) c) (s.length+1) := by
  induction s generalizing r tokens with
  | nil => exact once (restore_empty r tokens c)
  | cons b s ih =>
    have h := prepend (restore_cons r s tokens c b) (ih (b :: r) (true :: tokens))
    simpa [List.reverse_cons, List.append_assoc, marks, List.replicate_succ'] using h

def guardEnd (r d saved ctx : Bits) : Cfg :=
  match predWord d with
  | none => atLabel 9 (saved.reverse ++ r) [] [] [] (marks saved.length) ctx
  | some e => match r with
    | [] => atLabel 10 [] e [] saved [] ctx
    | b :: rs => guardEnd rs e (b :: saved) ctx
termination_by r.length

def guard_run (r d saved ctx : Bits) :
    Run (atLabel 4 r d [] saved [] ctx) (guardEnd r d saved ctx)
      ((r.length+1)*(2*d.length+4) + saved.length + 1) := by
  induction r generalizing d saved with
  | nil =>
    have head := borrow_run [] d saved ctx 0
    cases hp : predWord d with
    | none =>
      simp only [borrowed, hp] at head
      have tail := restore_run saved [] [] ctx
      simp only [List.append_nil] at tail
      rw [guardEnd, hp]
      simp only [List.append_nil]
      apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ head tail)
      simp; omega
    | some e =>
      simp [borrowed, hp, marks] at head
      rw [guardEnd, hp]
      apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ head (once (debit_empty e saved [] ctx)))
      simp; omega
  | cons b rs ih =>
    have head := borrow_run (b :: rs) d saved ctx 0
    cases hp : predWord d with
    | none =>
      simp only [borrowed, hp] at head
      have tail := restore_run saved (b :: rs) [] ctx
      simp only [List.append_nil] at tail
      rw [guardEnd, hp]
      apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ head tail)
      simp; nlinarith
    | some e =>
      have hs := pred_spec d
      simp only [hp] at hs
      simp [borrowed, hp, marks] at head
      have tail := prepend (debit_cons rs e saved [] ctx b) (ih e (b :: saved))
      rw [guardEnd, hp]
      apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ head tail)
      simp only [List.length_cons, hs.2]; nlinarith

/-- The success stack contains one token for each consumed position, including
those saved by the caller. The caller can pop one token per element. -/
theorem guard_contract (r d saved ctx : Bits) :
    if value d ≤ r.length then
      guardEnd r d saved ctx = atLabel 9 (saved.reverse ++ r) [] [] []
        (marks (saved.length + value d)) ctx
    else (guardEnd r d saved ctx).l = some 10 ∧ (guardEnd r d saved ctx).stk 5 = ctx := by
  have hs := pred_spec d
  cases hp : predWord d with
  | none => simp [hp] at hs; simp [guardEnd, hp, hs]
  | some e =>
    simp [hp] at hs
    cases r with
    | nil => simp [guardEnd, hp, hs, atLabel, layout]
    | cons b rs =>
      have ih := guard_contract rs e (b :: saved) ctx
      rw [guardEnd, hp]
      by_cases h : value e ≤ rs.length
      · simp [h] at ih
        rw [if_pos (show value d ≤ (b :: rs).length by simp [hs,h])]
        simpa [hs, List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using ih
      · simp [h] at ih
        simpa [hs, h] using ih
termination_by r.length

end UAVProof.TreeBudgetListGuardTM2
