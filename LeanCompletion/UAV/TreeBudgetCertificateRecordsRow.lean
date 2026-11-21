import LeanCompletion.UAV.TreeBudgetCertificateRecordsData

namespace UAVProof.A4CertRecords
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition

local macro "physical" : tactic => `(tactic|
  (simp [machine, FinTM2.step, TM2.step, cfg, stop, program, TM2.stepAux,
      jump, reject, TreeBudgetStackRoutine.jump, store]
   all_goals
     congr 2
     funext k
     rcases k with (i | (i | u)) | a
     · fin_cases i <;> rfl
     · fin_cases i <;> rfl
     · cases u; rfl
     · cases a <;> rfl))

theorem row_nil (d : Data) : machine.step (cfg .row {d with row := []}) =
    some (cfg (.job .copyDim .reverse) {d with row := []}) := by physical

theorem row_zero (d : Data) (tail : Bits) :
    machine.step (cfg .row {d with row := false :: tail}) =
      some (cfg (.job .incSize .carry) {d with row := tail}) := by physical

theorem row_pair (d : Data) (b : Bool) (tail : Bits) :
    machine.step (cfg .row {d with row := true :: b :: tail}) =
      some (cfg .row {d with row := tail}) := by physical

def row_field (d : Data) (bs tail : Bits) :
    Run (cfg .row {d with row := word bs ++ tail})
      (cfg (.job .incSize .carry) {d with row := tail}) (bs.length+1) := by
  induction bs with
  | nil => simpa [word] using once (row_zero d tail)
  | cons b bs ih =>
    simpa [word, List.append_assoc] using prepend (row_pair d b (word bs ++ tail)) ih

/-- Count canonical field terminators, skipping payload bits, from any index. -/
def row_fields (d : Data) (i W : ℕ) (xs : List ℕ) (ht : d.scratch = [])
    (hi : i+xs.length ≤ W) :
    Run (cfg .row {d with row := xs.flatMap encodeNat, amount := i.bits})
      (cfg (.job .copyDim .reverse) {d with row := [], amount := (i+xs.length).bits})
      ((xs.flatMap encodeNat).length*(2*W+4)+1) := by
  induction xs generalizing i with
  | nil => simpa using once (row_nil {d with amount := i.bits})
  | cons h xs ih =>
    have hi' : i+1+xs.length ≤ W := by simp only [List.length_cons] at hi; omega
    have bi : i.bits.length ≤ W := by
      have hb := TreeBudgetCostedCodec.nat_size_le i
      simp only [Nat.size_eq_bits_len]
      simp only [List.length_cons] at hi
      omega
    have a := row_field {d with amount := i.bits} h.bits (xs.flatMap encodeNat)
    have b := increment_job {d with row := xs.flatMap encodeNat, amount := i.bits} ht
    have c := ih (i+1) hi'
    dsimp only at a b
    rw [TreeBudgetStackRoutine.increment_bits] at b
    have allRun := seq (seq a b) c
    apply weaken (by
      simpa only [encodeNat, List.flatMap_cons, List.length_cons,
        TreeBudgetStackRoutine.increment_bits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using allRun)
    simp only [List.flatMap_cons, List.length_append, encodeNat_length,
      Nat.size_eq_bits_len] at bi ⊢
    nlinarith

theorem equal_nil (d : Data) :
    machine.step (cfg .equalSize {d with amount := [], dimCopy := []}) =
      some (cfg .tick {d with amount := [], dimCopy := []}) := by physical

theorem equal_left (d : Data) (a : Bool) (as : Bits) :
    machine.step (cfg .equalSize {d with amount := a::as, dimCopy := []}) =
      some (stop {d with amount := as, dimCopy := []} false) := by physical

theorem equal_right (d : Data) (b : Bool) (bs : Bits) :
    machine.step (cfg .equalSize {d with amount := [], dimCopy := b::bs}) =
      some (stop {d with amount := [], dimCopy := bs} false) := by physical

theorem equal_pair (d : Data) (a b : Bool) (as bs : Bits) :
    machine.step (cfg .equalSize {d with amount := a::as, dimCopy := b::bs}) =
      some (if a=b then cfg .equalSize {d with amount := as, dimCopy := bs}
        else stop {d with amount := as, dimCopy := bs} false) := by
  cases a <;> cases b <;> physical

def equalEnd (d : Data) : Bits → Bits → Cfg
  | [], [] => cfg .tick {d with amount := [], dimCopy := []}
  | a::as, [] => stop {d with amount := as, dimCopy := []} false
  | [], b::bs => stop {d with amount := [], dimCopy := bs} false
  | a::as, b::bs => if a=b then equalEnd d as bs
      else stop {d with amount := as, dimCopy := bs} false

def equal_run (d : Data) (a b : Bits) :
    Run (cfg .equalSize {d with amount := a, dimCopy := b})
      (equalEnd d a b) (a.length+b.length+1) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact once (equal_nil d)
    | cons b bs => exact weaken (once (equal_right d b bs)) (by simp)
  | cons a as ih =>
    cases b with
    | nil => exact weaken (once (equal_left d a as)) (by simp)
    | cons b bs =>
      by_cases h : a=b
      · subst b
        have st := equal_pair d a a as bs
        simp only [if_pos rfl] at st
        exact weaken (by simpa only [equalEnd, if_pos rfl] using prepend st (ih bs))
          (by simp; omega)
      · simpa only [equalEnd, if_neg h] using
          weaken (once (equal_pair d a b as bs)) (by simp)

theorem equalEnd_same (d : Data) (a : Bits) :
    equalEnd d a a = cfg .tick {d with amount := [], dimCopy := []} := by
  induction a <;> simp_all [equalEnd]

theorem equalEnd_different (d : Data) (a b : Bits) (h : a≠b) :
    (equalEnd d a b).l = none ∧ (equalEnd d a b).var.2 = false := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [equalEnd, stop]
  | cons a as ih =>
    cases b with
    | nil => exact ⟨rfl,rfl⟩
    | cons b bs =>
      by_cases he : a=b
      · subst b
        simpa only [equalEnd, if_pos rfl] using ih bs (by simpa using h)
      · simp [equalEnd, he, stop]

theorem equalEnd_kept (d : Data) (a b : Bits) : Kept d (equalEnd d a b) := by
  induction a generalizing b with
  | nil => cases b <;> exact ⟨rfl,rfl,rfl,rfl⟩
  | cons a as ih =>
    cases b with
    | nil => exact ⟨rfl,rfl,rfl,rfl⟩
    | cons b bs =>
      simp only [equalEnd]
      split
      · exact ih bs
      · exact ⟨rfl,rfl,rfl,rfl⟩

theorem bits_eq (i n : ℕ) : i.bits=n.bits ↔ i=n := by
  constructor
  · intro h
    simpa only [value_bits] using congrArg value h
  · exact congrArg Nat.bits

end UAVProof.A4CertRecords
