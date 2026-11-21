import LeanCompletion.UAV.TreeBudgetCertificateRecordsTM2

/-! Transport just the count-guard prelude. Every transported step starts at
a label below 9; the caller owns the successful and failing return labels. -/
namespace UAVProof.A4CertRecords.Guard
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetCanonicalDigits
open TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetListGuardTM2 (atLabel predWord pred_spec marks borrowed guardEnd
  outcome headerEnd lab)

def outside (dim : Bits) (k : K) : Bits := if k = .inr .dim then dim else []

def lift (dim : Bits) (c : TreeBudgetListGuardTM2.Cfg) : Cfg :=
  embed gw L.guardCall .bad (outside dim) c

abbrev GRun (dim : Bits) (a b : TreeBudgetListGuardTM2.Cfg) (t : ℕ) :=
  EvalsToInTime machine.step (lift dim a) (some (lift dim b)) t

theorem lift_step (dim : Bits) {l : Fin 18} {v : State} {stk : Fin 7 → Bits}
    {b : TreeBudgetListGuardTM2.Cfg} (hl : l.val < 9)
    (h : TreeBudgetListGuardTM2.machine.step ⟨some l, v, stk⟩ = some b) :
    machine.step (lift dim ⟨some l, v, stk⟩) = some (lift dim b) := by
  have h9 : l ≠ 9 := by intro he; subst l; contradiction
  have h10 : l ≠ 10 := by intro he; subst l; contradiction
  have hs := statement_step gw L.guardCall .bad (outside dim)
    (TreeBudgetListGuardTM2.program l) v stk
  simp only [TreeBudgetListGuardTM2.machine, FinTM2.step, TM2.step] at h
  have h := Option.some.inj h
  subst b
  simpa only [machine, FinTM2.step, TM2.step, lift, embed, program,
    Option.elim_some, if_neg h9, if_neg h10] using congrArg some hs

def headerPorts : Ports K := ⟨gs 0, gs 1, gs 2, by decide, by decide, by decide⟩
def headerLabels (p : Phase) : L := .guardCall (lab p)
def headerBase (dim ctx : Bits) : K → Bits :=
  bank gw (outside dim) (TreeBudgetListGuardTM2.base ctx)

theorem header_cfg (dim ctx r t d : Bits) (l : Fin 18) :
    cfg headerPorts (headerBase dim ctx) (.guardCall l) none true r t d =
      lift dim (atLabel l r d t [] [] ctx) := by
  unfold cfg lift embed TreeBudgetListGuardTM2.atLabel
  congr 1
  funext k
  rcases k with (i | (i | u)) | a
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · cases u; rfl
  · cases a <;> rfl

theorem header_link (p : Phase) : program (headerLabels p) =
    code headerPorts headerLabels (.guardCall 4) (.guardCall 10) true p := by
  cases p <;> rfl

def header_run (dim s ctx : Bits) :
    GRun dim (atLabel 0 s [] [] [] [] ctx) (headerEnd s ctx) (2*s.length+2) := by
  cases hw : parseWord s with
  | none =>
    have run := truncated_run headerPorts (headerBase dim ctx) headerLabels
      (.guardCall 4) (.guardCall 10) true program header_link s hw none true [] []
    simpa [GRun, machine, FinTM2.step, headerLabels, lab, headerEnd, hw,
      header_cfg] using run
  | some pair =>
    obtain ⟨bs,r⟩ := pair
    have he := parseWord_consumed s bs r hw
    subst s
    have run := framed_run headerPorts (headerBase dim ctx) headerLabels
      (.guardCall 4) (.guardCall 10) true program header_link bs r none true [] []
    have hb : 3*bs.length+2 ≤ 2*(word bs ++ r).length+2 := by
      simp [word_length]; omega
    cases hc : lastDigit bs true <;>
      simpa [GRun, machine, FinTM2.step, headerLabels, lab, headerEnd,
        parseWord_append, hc, header_cfg] using weaken run hb

def ones_run (dim : Bits) (n : ℕ) (r d s c : Bits) :
    GRun dim (atLabel 5 r d (marks n) s [] c) (atLabel 6 r (marks n ++ d) [] s [] c) (n+1) := by
  induction n generalizing d with
  | zero => exact once (lift_step dim (l := 5) (by decide) (TreeBudgetListGuardTM2.ones_empty r d s [] c))
  | succ n ih =>
    have h := prepend (lift_step dim (l := 5) (by decide)
      (TreeBudgetListGuardTM2.ones_cons r d (marks n) s [] c)) (ih (true :: d))
    have he : true :: marks n = marks (n+1) := (List.replicate_succ ..).symm
    rw [he] at h
    have ht : marks (n+1) ++ d = marks n ++ true :: d := by
      simp [marks, List.replicate_succ', List.append_assoc]
    rw [ht]
    exact h

def clear_run (dim : Bits) (n : ℕ) (r s c : Bits) :
    GRun dim (atLabel 7 r [] (marks n) s [] c) (atLabel 8 r [] [] s [] c) (n+1) := by
  induction n with
  | zero => exact once (lift_step dim (l := 7) (by decide) (TreeBudgetListGuardTM2.clear_empty r s [] c))
  | succ n ih => exact prepend (lift_step dim (l := 7) (by decide)
      (TreeBudgetListGuardTM2.clear_cons r (marks n) s [] c)) ih

def borrow_run (dim : Bits) (r d s c : Bits) (z : ℕ) :
    GRun dim (atLabel 4 r d (marks z) s [] c) (borrowed r d s c z) (2*d.length+z+2) := by
  induction d generalizing z with
  | nil => simpa [borrowed, predWord] using prepend (lift_step dim (l := 4) (by decide)
      (TreeBudgetListGuardTM2.borrow_empty r (marks z) s [] c)) (clear_run dim z r s c)
  | cons b ds ih =>
    cases b with
    | true =>
      have h := prepend (lift_step dim (l := 4) (by decide)
        (TreeBudgetListGuardTM2.borrow_one r ds (marks z) s [] c)) (ones_run dim z r (false :: ds) s c)
      exact weaken h (by simp)
    | false =>
      have h := prepend (lift_step dim (l := 4) (by decide)
        (TreeBudgetListGuardTM2.borrow_zero r ds (marks z) s [] c)) (ih (z+1))
      have he : borrowed r ds s c (z+1) = borrowed r (false :: ds) s c z := by
        cases hp : predWord ds <;> simp [borrowed, predWord, hp, marks, List.replicate_succ']
      rw [he] at h
      exact weaken h (by simp; omega)

def restore_run (dim : Bits) (s r tokens c : Bits) :
    GRun dim (atLabel 8 r [] [] s tokens c)
      (atLabel 9 (s.reverse ++ r) [] [] [] (marks s.length ++ tokens) c) (s.length+1) := by
  induction s generalizing r tokens with
  | nil => exact once (lift_step dim (l := 8) (by decide) (TreeBudgetListGuardTM2.restore_empty r tokens c))
  | cons b s ih =>
    have h := prepend (lift_step dim (l := 8) (by decide) (TreeBudgetListGuardTM2.restore_cons r s tokens c b)) (ih (b :: r) (true :: tokens))
    simpa [List.reverse_cons, List.append_assoc, marks, List.replicate_succ'] using h

def guard_run (dim : Bits) (r d saved ctx : Bits) :
    GRun dim (atLabel 4 r d [] saved [] ctx) (guardEnd r d saved ctx)
      ((r.length+1)*(2*d.length+4) + saved.length + 1) := by
  induction r generalizing d saved with
  | nil =>
    have head := borrow_run dim [] d saved ctx 0
    cases hp : predWord d with
    | none =>
      simp only [borrowed, hp] at head
      have tail := restore_run dim saved [] [] ctx
      simp only [List.append_nil] at tail
      rw [guardEnd, hp]
      simp only [List.append_nil]
      apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ head tail)
      simp; omega
    | some e =>
      simp [borrowed, hp, marks] at head
      rw [guardEnd, hp]
      apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ head (once (lift_step dim (l := 6) (by decide) (TreeBudgetListGuardTM2.debit_empty e saved [] ctx))))
      simp; omega
  | cons b rs ih =>
    have head := borrow_run dim (b :: rs) d saved ctx 0
    cases hp : predWord d with
    | none =>
      simp only [borrowed, hp] at head
      have tail := restore_run dim saved (b :: rs) [] ctx
      simp only [List.append_nil] at tail
      rw [guardEnd, hp]
      apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ head tail)
      simp; nlinarith
    | some e =>
      have hs := pred_spec d
      simp only [hp] at hs
      simp [borrowed, hp, marks] at head
      have tail := prepend (lift_step dim (l := 6) (by decide) (TreeBudgetListGuardTM2.debit_cons rs e saved [] ctx b)) (ih e (b :: saved))
      rw [guardEnd, hp]
      apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ head tail)
      simp only [List.length_cons, hs.2]; nlinarith


def precheck_run (dim s ctx : Bits) :
    GRun dim (atLabel 0 s [] [] [] [] ctx) (outcome s ctx) (8*(s.length+1)^2) := by
  have head := header_run dim s ctx
  cases hp : parseNat s with
  | none =>
    simp only [outcome, hp]
    exact weaken head (by nlinarith)
  | some pair =>
    obtain ⟨k,r⟩ := pair
    rw [TreeBudgetListGuardTM2.header_valid s ctx r k hp] at head
    have hl := congrArg List.length (parseNat_canonical s r k hp)
    simp only [List.length_append, encodeNat_length] at hl
    simp only [outcome, hp]
    apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ head
      (guard_run dim r k.bits [] ctx))
    simp only [Nat.size_eq_bits_len, List.length_nil]
    have hm := Nat.mul_le_mul (show r.length+1 ≤ s.length+1 by omega)
      (show 2*k.size+4 ≤ 2*s.length+4 by omega)
    nlinarith

theorem start_eq (n : ℕ) (s ctx : Bits) :
    start n s ctx = lift n.bits (atLabel 0 s [] [] [] [] ctx) := by
  unfold start lift embed TreeBudgetListGuardTM2.atLabel
  congr 1
  funext k
  rcases k with (i | (i | u)) | a
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · cases u; rfl
  · cases a <;> rfl

end UAVProof.A4CertRecords.Guard
