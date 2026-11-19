import LeanCompletion.UAV.TreeBudgetFrameRunsTM2
import LeanCompletion.UAV.TreeBudgetCanonicalDigits
import LeanCompletion.UAV.TreeBudgetCostedCodec

/-! A concrete signed integer parser using the callable canonical Nat parser.
The sign occupies a separate one-bit stack. Negative zero is rejected. The
source suffix and an unrelated context stack survive success and rejection. -/
namespace UAVProof.TreeBudgetIntTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetCanonicalDigits
open Turing StateTransition Turing.TM2.Stmt

def ports : Ports (Fin 5) := ⟨0, 1, 2, by decide, by decide, by decide⟩
def labels : Phase → Fin 7
  | .marker => 1 | .payload => 2 | .reverse => 3 | .clear => 4
def base (sign : Bits) (context : Bits) : Fin 5 → Bits :=
  fun k => if k = 3 then sign else if k = 4 then context else []

def program (l : Fin 7) : Statement (Fin 5) (Fin 7) :=
  match l.val with
  | 0 => pop 0 (fun s b => (b, s.2))
      (branch (fun s => s.1.isNone) (goto (fun _ => 6))
        (push 3 (fun s => s.1.getD false)
          (load (fun _ => (none, true)) (goto (fun _ => 1)))))
  | 1 => code ports labels 5 6 true .marker
  | 2 => code ports labels 5 6 true .payload
  | 3 => code ports labels 5 6 true .reverse
  | 4 => code ports labels 5 6 true .clear
  | 5 => peek 3 (fun s b => (b, s.2))
      (peek 2 (fun s b => (s.1, !(s.1 == some true && b.isNone)))
        (load (fun s => (none, s.2)) halt))
  | _ => load (fun _ => (none, false)) halt

def machine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Fin 7
  main := 0
  σ := State
  initialState := (none, true)
  m := program

theorem routine_code (p : Phase) : program (labels p) = code ports labels 5 6 true p := by
  cases p <;> rfl

def start (xs context : Bits) : Configuration (Fin 5) (Fin 7) :=
  cfg ports (base [] context) 0 none true xs [] []
def afterSign (sign : Bool) (xs context : Bits) : Configuration (Fin 5) (Fin 7) :=
  cfg ports (base [sign] context) 1 none true xs [] []
def parsed (sign : Bool) (bs rest context : Bits) : Configuration (Fin 5) (Fin 7) :=
  cfg ports (base [sign] context) 5 none true rest [] bs
def rejected (sign : Bits) (rest context : Bits) : Configuration (Fin 5) (Fin 7) :=
  cfg ports (base sign context) 6 none true rest [] []
def stopped (ok : Bool) (sign bs rest context : Bits) : Configuration (Fin 5) (Fin 7) :=
  ⟨none, (none, ok), tapes ports (base sign context) rest [] bs⟩

theorem step_sign (sign : Bool) (xs context : Bits) :
    machine.step (start (sign :: xs) context) = some (afterSign sign xs context) := by
  simp [machine, FinTM2.step, TM2.step, program, start, afterSign, cfg, TM2.stepAux,
    ports, tapes, base]
  congr 2
  funext k; fin_cases k <;> rfl

theorem step_empty (context : Bits) : machine.step (start [] context) =
    some (rejected [] [] context) := by
  simp [machine, FinTM2.step, TM2.step, program, start, rejected, cfg, TM2.stepAux,
    ports, tapes, base]
  congr 2
  funext k; fin_cases k <;> rfl

theorem step_parsed (sign : Bool) (bs rest context : Bits) :
    machine.step (parsed sign bs rest context) =
      some (stopped (!(sign && bs.isEmpty)) [sign] bs rest context) := by
  cases bs with
  | nil =>
    cases sign <;> simp [machine, FinTM2.step, TM2.step, program, parsed, stopped,
      cfg, TM2.stepAux, ports, tapes, base]
  | cons b bs =>
    cases sign <;> simp [machine, FinTM2.step, TM2.step, program, parsed, stopped,
      cfg, TM2.stepAux, ports, tapes, base]

theorem step_rejected (sign rest context : Bits) : machine.step (rejected sign rest context) =
    some (stopped false sign [] rest context) := rfl

def rejectSuffix (xs : Bits) : Bits := ((parseWord xs).map Prod.snd).getD []
def magnitudeOutcome (sign : Bool) (xs context : Bits) : Configuration (Fin 5) (Fin 7) :=
  match parseNat xs with
  | some (n, rest) => parsed sign n.bits rest context
  | none => rejected [sign] (rejectSuffix xs) context

def magnitude_run (sign : Bool) (xs context : Bits) :
    EvalsToInTime machine.step (afterSign sign xs context)
      (some (magnitudeOutcome sign xs context)) (2 * xs.length + 2) := by
  cases hp : parseWord xs with
  | none =>
    have run := truncated_run ports (base [sign] context) labels 5 6 true program routine_code
      xs hp none true [] []
    simpa [machine, FinTM2.step, magnitudeOutcome, parseNat_truncated xs hp, rejectSuffix, hp,
      afterSign, rejected, labels] using run
  | some out =>
    rcases out with ⟨bs, rest⟩
    have he := parseWord_consumed xs bs rest hp
    subst xs
    have run := framed_run ports (base [sign] context) labels 5 6 true program routine_code
      bs rest none true [] []
    have hb : 3 * bs.length + 2 ≤ 2 * (word bs ++ rest).length + 2 := by
      simp [List.length_append, word_length]; omega
    cases hc : lastDigit bs true with
    | false =>
      simpa [machine, FinTM2.step, magnitudeOutcome, parseNat_framed, hc, rejectSuffix,
        parseWord_append, afterSign, rejected, labels] using weaken run hb
    | true =>
      have hbits := canonical_of_last bs hc
      simpa [machine, FinTM2.step, magnitudeOutcome, parseNat_framed, hc,
        afterSign, parsed, labels, hbits] using weaken run hb

def intOutcome : Bits → Bits → Configuration (Fin 5) (Fin 7)
  | [], context => stopped false [] [] [] context
  | sign :: xs, context => match parseNat xs with
    | some (n, rest) => stopped (!(sign && n.bits.isEmpty)) [sign] n.bits rest context
    | none => stopped false [sign] [] (rejectSuffix xs) context

def integer_run (xs context : Bits) : EvalsToInTime machine.step (start xs context)
    (some (intOutcome xs context)) (2 * xs.length + 2) := by
  cases xs with
  | nil =>
    exact prepend (step_empty context) (once (step_rejected [] [] context))
  | cons sign xs =>
    have tail : EvalsToInTime machine.step (magnitudeOutcome sign xs context)
        (some (intOutcome (sign :: xs) context)) 1 := by
      cases hp : parseNat xs with
      | none =>
        simpa [magnitudeOutcome, intOutcome, hp] using
          (once (step_rejected [sign] (rejectSuffix xs) context))
      | some out =>
        rcases out with ⟨n, rest⟩
        simpa [magnitudeOutcome, intOutcome, hp] using once (step_parsed sign n.bits rest context)
    have run := prepend (step_sign sign xs context)
      (EvalsToInTime.trans machine.step (2 * xs.length + 2) 1 _ _ _
        (magnitude_run sign xs context) tail)
    convert run using 1; simp; omega

def readResult (c : Configuration (Fin 5) (Fin 7)) : Option (ℤ × Bits) :=
  if c.var.2 then
    some ((if (c.stk 3).headD false then -(value (c.stk 2) : ℤ) else (value (c.stk 2) : ℤ)), c.stk 0)
  else none

theorem bits_empty_iff (n : ℕ) : n.bits.isEmpty = true ↔ n = 0 := by
  constructor
  · intro h
    have he : n.bits = [] := List.isEmpty_iff.mp h
    have hv := value_bits n
    rw [he] at hv
    exact hv.symm
  · rintro rfl; rfl

theorem bits_nil_iff (n : ℕ) : n.bits = [] ↔ n = 0 := by
  simpa only [List.isEmpty_iff] using bits_empty_iff n

theorem integer_result (xs context : Bits) : readResult (intOutcome xs context) = parseInt xs := by
  cases xs with
  | nil => rfl
  | cons sign xs =>
    cases hp : parseNat xs with
    | none => simp [intOutcome, hp, readResult, stopped, parseInt]
    | some out =>
      rcases out with ⟨n, rest⟩
      cases sign <;> simp [intOutcome, hp, readResult, stopped, tapes, ports, base,
        parseInt, bits_nil_iff]

theorem refines_parseIntD (xs context : Bits) :
    readResult (intOutcome xs context) = (TreeBudgetCostedCodec.parseIntD xs).value := by
  rw [TreeBudgetCostedCodec.parseIntD_value, integer_result]

theorem context_preserved (xs context : Bits) : (intOutcome xs context).stk 4 = context := by
  cases xs with
  | nil => rfl
  | cons sign xs =>
    cases hp : parseNat xs with
    | none => simp [intOutcome, hp, stopped, tapes, ports, base]
    | some out => rcases out with ⟨n, rest⟩; simp [intOutcome, hp, stopped, tapes, ports, base]

theorem outcome_terminal (xs context : Bits) : machine.step (intOutcome xs context) = none := by
  cases xs with
  | nil => rfl
  | cons sign xs =>
    cases hp : parseNat xs with
    | none => simp [intOutcome, hp, stopped, machine, FinTM2.step, TM2.step]; rfl
    | some out =>
      rcases out with ⟨n, rest⟩
      simp [intOutcome, hp, stopped, machine, FinTM2.step, TM2.step]; rfl

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem init_eq (xs : Bits) : initList machine xs = start xs [] := by
  simp only [initList, machine, start, cfg]
  congr 1
  funext k; fin_cases k <;> rfl

def integer_from_init (xs : Bits) : EvalsToInTime machine.step (initList machine xs)
    (some (intOutcome xs [])) (2 * xs.length + 2) := by
  rw [init_eq]
  exact integer_run xs []

end UAVProof.TreeBudgetIntTM2
