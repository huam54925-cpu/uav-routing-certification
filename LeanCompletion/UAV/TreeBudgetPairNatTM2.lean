import LeanCompletion.UAV.TreeBudgetFrameRunsTM2
import LeanCompletion.UAV.TreeBudgetCanonicalDigits
import LeanCompletion.UAV.TreeBudgetSparseNPBridge
import LeanCompletion.UAV.TreeBudgetCostedParsing

/-! One concrete TM2 program calls the data-preserving frame routine twice:
first to split pairWire, then to read the instance's first canonical Nat.
Stacks 0/1/2/3 hold certificate / remaining instance / scratch / Nat digits.
Labels 8 and 9 are explicit successful and failed return points; the next
transition halts. This is a verifier frontend component, not StandardVerifier. -/
namespace UAVProof.TreeBudgetPairNatTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetCanonicalDigits
open TreeBudgetSparseNPBridge Turing StateTransition

def pairPorts : Ports (Fin 4) := ⟨0, 2, 1, by decide, by decide, by decide⟩
def natPorts : Ports (Fin 4) := ⟨1, 2, 3, by decide, by decide, by decide⟩
def pairLab : Phase → Fin 10
  | .marker => 0 | .payload => 1 | .reverse => 2 | .clear => 3
def natLab : Phase → Fin 10
  | .marker => 4 | .payload => 5 | .reverse => 6 | .clear => 7

def program (label : Fin 10) : Statement (Fin 4) (Fin 10) :=
  match label.val with
  | 0 => code pairPorts pairLab 4 9 false .marker
  | 1 => code pairPorts pairLab 4 9 false .payload
  | 2 => code pairPorts pairLab 4 9 false .reverse
  | 3 => code pairPorts pairLab 4 9 false .clear
  | 4 => code natPorts natLab 8 9 true .marker
  | 5 => code natPorts natLab 8 9 true .payload
  | 6 => code natPorts natLab 8 9 true .reverse
  | 7 => code natPorts natLab 8 9 true .clear
  | 8 => TM2.Stmt.load (fun _ => (none, true)) TM2.Stmt.halt
  | _ => TM2.Stmt.load (fun _ => (none, false)) TM2.Stmt.halt

def machine : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 10
  main := 0
  σ := State
  initialState := (none, true)
  m := program

theorem pair_code (p : Phase) : program (pairLab p) = code pairPorts pairLab 4 9 false p := by
  cases p <;> rfl
theorem nat_code (p : Phase) : program (natLab p) = code natPorts natLab 8 9 true p := by
  cases p <;> rfl

def empty : Fin 4 → Bits := fun _ => []
def certBase (certificate : Bits) : Fin 4 → Bits := fun k => if k = 0 then certificate else []
def start (wire : Bits) : Configuration (Fin 4) (Fin 10) :=
  cfg pairPorts empty 0 none true wire [] []
def splitReturn (x y : Bits) : Configuration (Fin 4) (Fin 10) :=
  cfg natPorts (certBase y) 4 none true x [] []
def natReturn (n : ℕ) (rest y : Bits) : Configuration (Fin 4) (Fin 10) :=
  cfg natPorts (certBase y) 8 none true rest [] n.bits
def failed (rest y : Bits) : Configuration (Fin 4) (Fin 10) :=
  cfg natPorts (certBase y) 9 none true rest [] []

theorem init_eq (wire : Bits) : initList machine wire = start wire := by
  simp only [initList, machine, start, cfg]
  congr 1
  funext k; fin_cases k <;> rfl

theorem split_return_eq (x y : Bits) :
    cfg pairPorts empty 4 none true y [] x = splitReturn x y := by
  unfold splitReturn cfg
  congr 1
  funext k; fin_cases k <;> rfl

def split_run (x y : Bits) : EvalsToInTime machine.step (initList machine (pairWire (x, y)))
    (some (splitReturn x y)) (3 * x.length + 2) := by
  have run := framed_run pairPorts empty pairLab 4 9 false program pair_code x y none true [] []
  rw [init_eq]
  simpa [machine, FinTM2.step, start, pairWire, pairLab, split_return_eq] using run

theorem pair_failed_eq : cfg pairPorts empty 9 none true [] [] [] = failed [] [] := by
  unfold failed cfg
  congr 1
  funext k; fin_cases k <;> rfl

def split_truncated (wire : Bits) (h : parseWord wire = none) :
    EvalsToInTime machine.step (initList machine wire) (some (failed [] []))
      (2 * wire.length + 2) := by
  have run := truncated_run pairPorts empty pairLab 4 9 false program pair_code wire h none true [] []
  rw [init_eq]
  simpa [machine, FinTM2.step, start, pairLab, pair_failed_eq] using run

def nat_success (n : ℕ) (rest y : Bits) :
    EvalsToInTime machine.step (splitReturn (encodeNat n ++ rest) y)
      (some (natReturn n rest y)) (3 * n.size + 2) := by
  have run := framed_run natPorts (certBase y) natLab 8 9 true program nat_code
    n.bits rest none true [] []
  simpa [machine, FinTM2.step, splitReturn, natReturn, natLab, encodeNat,
    lastDigit_bits, Nat.size_eq_bits_len] using run

def nat_noncanonical (xs rest y : Bits) (h : lastDigit xs true = false) :
    EvalsToInTime machine.step (splitReturn (word xs ++ rest) y)
      (some (failed rest y)) (3 * xs.length + 2) := by
  have run := framed_run natPorts (certBase y) natLab 8 9 true program nat_code
    xs rest none true [] []
  simpa [machine, FinTM2.step, splitReturn, failed, natLab, h] using run

def nat_truncated (xs y : Bits) (h : parseWord xs = none) :
    EvalsToInTime machine.step (splitReturn xs y) (some (failed [] y)) (2 * xs.length + 2) := by
  have run := truncated_run natPorts (certBase y) natLab 8 9 true program nat_code xs h none true [] []
  simpa [machine, FinTM2.step, splitReturn, failed, natLab] using run

def remainder (xs : Bits) : Bits := ((parseWord xs).map Prod.snd).getD []
def natOutcome (xs y : Bits) : Configuration (Fin 4) (Fin 10) :=
  match parseNat xs with
  | some (n, rest) => natReturn n rest y
  | none => failed (remainder xs) y

def nat_run (xs y : Bits) : EvalsToInTime machine.step (splitReturn xs y)
    (some (natOutcome xs y)) (2 * xs.length + 2) := by
  cases hp : parseWord xs with
  | none => simpa [natOutcome, parseNat_truncated xs hp, remainder, hp] using nat_truncated xs y hp
  | some out =>
    rcases out with ⟨bs, rest⟩
    have he := parseWord_consumed xs bs rest hp
    subst xs
    cases hc : lastDigit bs true with
    | false =>
      have run := nat_noncanonical bs rest y hc
      have hb : 3 * bs.length + 2 ≤ 2 * (word bs ++ rest).length + 2 := by
        simp [List.length_append, word_length]; omega
      simpa [natOutcome, parseNat_framed, hc, remainder, parseWord_append] using weaken run hb
    | true =>
      have hbits := canonical_of_last bs hc
      have run := nat_success (value bs) rest y
      have hb : 3 * (value bs).size + 2 ≤ 2 * (word bs ++ rest).length + 2 := by
        rw [← Nat.size_eq_bits_len, hbits]
        simp [List.length_append, word_length]; omega
      simpa [natOutcome, parseNat_framed, hc, encodeNat, hbits] using weaken run hb

/-- Actual sequential calls in one machine; no abstract composition axiom. -/
def pair_nat_run (x y : Bits) :
    EvalsToInTime machine.step (initList machine (pairWire (x, y)))
      (some (natOutcome x y)) (5 * x.length + 4) := by
  have run := EvalsToInTime.trans machine.step (3 * x.length + 2) (2 * x.length + 2)
    _ _ _ (split_run x y) (nat_run x y)
  convert run using 1; omega

theorem returned_stacks (n : ℕ) (rest y : Bits) :
    (natReturn n rest y).stk 0 = y ∧ (natReturn n rest y).stk 1 = rest ∧
    (natReturn n rest y).stk 2 = [] ∧ (natReturn n rest y).stk 3 = n.bits := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def readReturn (c : Configuration (Fin 4) (Fin 10)) : Option (ℕ × Bits) :=
  if c.l = some 8 then some (value (c.stk 3), c.stk 1) else none

theorem nat_result (x y : Bits) : readReturn (natOutcome x y) = parseNat x := by
  cases hp : parseNat x with
  | none => simp [natOutcome, hp, readReturn, failed, cfg]
  | some out =>
    rcases out with ⟨n, rest⟩
    simp [natOutcome, hp, readReturn, natReturn, cfg, tapes, natPorts]

theorem nat_refines_executor (x y : Bits) :
    readReturn (natOutcome x y) = (TreeBudgetCostedCodec.parseNatD x).value := by
  rw [TreeBudgetCostedCodec.parseNatD_value, nat_result]

theorem certificate_preserved (x y : Bits) : (natOutcome x y).stk 0 = y := by
  cases hp : parseNat x with
  | none => simp [natOutcome, hp, failed, cfg, tapes, natPorts, certBase]
  | some out =>
    rcases out with ⟨n, rest⟩
    simp [natOutcome, hp, natReturn, cfg, tapes, natPorts, certBase]

theorem scratch_cleared (x y : Bits) : (natOutcome x y).stk 2 = [] := by
  cases hp : parseNat x with
  | none => simp [natOutcome, hp, failed, cfg, tapes, natPorts]
  | some out =>
    rcases out with ⟨n, rest⟩
    simp [natOutcome, hp, natReturn, cfg, tapes, natPorts]

def frontOutcome (wire : Bits) : Configuration (Fin 4) (Fin 10) :=
  match parseWord wire with
  | none => failed [] []
  | some (x, y) => natOutcome x y

/-- Arbitrary wire strings, including outer and inner truncation. -/
def frontend_run (wire : Bits) : EvalsToInTime machine.step (initList machine wire)
    (some (frontOutcome wire)) (3 * wire.length + 4) := by
  cases hp : parseWord wire with
  | none =>
    simpa [frontOutcome, hp] using weaken (split_truncated wire hp)
      (show 2 * wire.length + 2 ≤ 3 * wire.length + 4 by omega)
  | some out =>
    rcases out with ⟨x, y⟩
    have he := parseWord_consumed wire x y hp
    subst wire
    have hb : 5 * x.length + 4 ≤ 3 * (word x ++ y).length + 4 := by
      simp [List.length_append, word_length]; omega
    simpa [frontOutcome, parseWord_append, pairWire] using weaken (pair_nat_run x y) hb

def stopped (c : Configuration (Fin 4) (Fin 10)) : Configuration (Fin 4) (Fin 10) :=
  ⟨none, (none, decide (c.l = some 8)), c.stk⟩

theorem step_outcome (wire : Bits) : machine.step (frontOutcome wire) =
    some (stopped (frontOutcome wire)) := by
  cases hp : parseWord wire with
  | none => simp [frontOutcome, hp, failed, stopped, cfg,
      machine, FinTM2.step, TM2.step, TM2.stepAux, program]
  | some out =>
    rcases out with ⟨x, y⟩
    cases hn : parseNat x with
    | none => simp [frontOutcome, hp, natOutcome, hn, failed, stopped, cfg,
        machine, FinTM2.step, TM2.step, TM2.stepAux, program]
    | some z =>
      rcases z with ⟨n, rest⟩
      simp [frontOutcome, hp, natOutcome, hn, natReturn, stopped, cfg,
        machine, FinTM2.step, TM2.step, TM2.stepAux, program]

def frontend_halts (wire : Bits) : EvalsToInTime machine.step (initList machine wire)
    (some (stopped (frontOutcome wire))) (3 * wire.length + 5) := by
  have run := EvalsToInTime.trans machine.step (3 * wire.length + 4) 1
    _ _ _ (frontend_run wire) (once (step_outcome wire))
  convert run using 1; omega

theorem stopped_terminal (wire : Bits) : machine.step (stopped (frontOutcome wire)) = none := rfl

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end UAVProof.TreeBudgetPairNatTM2
