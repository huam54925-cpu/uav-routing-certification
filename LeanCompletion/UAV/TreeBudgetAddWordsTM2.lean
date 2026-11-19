import LeanCompletion.UAV.TreeBudgetFrameRoutineTM2
import LeanCompletion.UAV.TreeBudgetBitPrimitives

/-! A concrete finite-alphabet TM2 binary adder. Inputs and output are raw
little-endian words, possibly padded; the theorem is about their Nat values.
Every pair of words terminates in a linear number of actual TM2 transitions.
No arithmetic is hidden in a stack symbol or finite-control operation. -/
namespace UAVProof.TreeBudgetAddWordsTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition Turing.TM2.Stmt

def digit (a b c : Bool) : Bool := xor (xor a b) c
def carry (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

def addWords : Bits → Bits → Bool → Bits
  | [], [], c => if c then [true] else []
  | a :: xs, [], c => digit a false c :: addWords xs [] (carry a false c)
  | [], b :: ys, c => digit false b c :: addWords [] ys (carry false b c)
  | a :: xs, b :: ys, c => digit a b c :: addWords xs ys (carry a b c)

theorem addWords_value (xs ys : Bits) (c : Bool) :
    value (addWords xs ys c) = value xs + value ys + c.toNat := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addWords, value, Nat.bit, Bool.toNat]
    | cons b ys ih =>
      simp only [addWords, value, ih]
      cases b <;> cases c <;> simp [digit, carry, Nat.bit, Bool.toNat]; omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      simp only [addWords, value, ih]
      cases a <;> cases c <;> simp [digit, carry, Nat.bit, Bool.toNat]; omega
    | cons b ys =>
      simp only [addWords, value, ih]
      cases a <;> cases b <;> cases c <;> simp [digit, carry, Nat.bit, Bool.toNat] <;> omega

theorem addWords_length (xs ys : Bits) (c : Bool) :
    (addWords xs ys c).length ≤ xs.length + ys.length + 1 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addWords]
    | cons b ys ih => simpa [addWords] using ih (carry false b c)
  | cons a xs ih =>
    cases ys with
    | nil => simpa [addWords] using ih [] (carry a false c)
    | cons b ys =>
      have ht := ih ys (carry a b c)
      simp only [addWords, List.length_cons]
      omega

def tapes (xs ys acc out : Bits) : Fin 4 → Bits := fun k =>
  match k.val with | 0 => xs | 1 => ys | 2 => acc | _ => out

@[simp] theorem tapes_zero (xs ys acc out : Bits) : tapes xs ys acc out 0 = xs := rfl
@[simp] theorem tapes_one (xs ys acc out : Bits) : tapes xs ys acc out 1 = ys := rfl
@[simp] theorem tapes_two (xs ys acc out : Bits) : tapes xs ys acc out 2 = acc := rfl
@[simp] theorem tapes_three (xs ys acc out : Bits) : tapes xs ys acc out 3 = out := rfl
@[simp] theorem update_zero (xs ys acc out zs : Bits) :
    Function.update (tapes xs ys acc out) 0 zs = tapes zs ys acc out := by
  funext k; fin_cases k <;> rfl
@[simp] theorem update_one (xs ys acc out zs : Bits) :
    Function.update (tapes xs ys acc out) 1 zs = tapes xs zs acc out := by
  funext k; fin_cases k <;> rfl
@[simp] theorem update_two (xs ys acc out zs : Bits) :
    Function.update (tapes xs ys acc out) 2 zs = tapes xs ys zs out := by
  funext k; fin_cases k <;> rfl
@[simp] theorem update_three (xs ys acc out zs : Bits) :
    Function.update (tapes xs ys acc out) 3 zs = tapes xs ys acc zs := by
  funext k; fin_cases k <;> rfl

def mix (s : State) (b : Option Bool) : State :=
  if s.1.isNone && b.isNone then (none, s.2) else
    (some (digit (s.1.getD false) (b.getD false) s.2),
      carry (s.1.getD false) (b.getD false) s.2)

def program (l : Fin 3) : Statement (Fin 4) (Fin 3) :=
  if l = 0 then pop 0 (fun s a => (a, s.2)) (pop 1 mix
    (branch (fun s => s.1.isNone)
      (branch Prod.snd (push 2 (fun _ => true) (goto (fun _ => 1))) (goto (fun _ => 1)))
      (push 2 (fun s => s.1.getD false) (goto (fun _ => 0)))))
  else if l = 1 then pop 2 (fun s b => (b, s.2))
    (branch (fun s => s.1.isNone) (load (fun _ => (none, false)) (goto (fun _ => 2)))
      (push 3 (fun s => s.1.getD false) (goto (fun _ => 1))))
  else halt

def machine : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := State
  initialState := (none, false)
  m := program

def cfg (l : Fin 3) (tmp : Option Bool) (c : Bool) (xs ys acc out : Bits) :
    Configuration (Fin 4) (Fin 3) := ⟨some l, (tmp, c), tapes xs ys acc out⟩

theorem step_reverse_nil (tmp : Option Bool) (c : Bool) (out : Bits) :
    machine.step (cfg 1 tmp c [] [] [] out) = some (cfg 2 none false [] [] [] out) := by
  simp [machine, FinTM2.step, TM2.step, program, cfg, TM2.stepAux]
  congr 2
  funext k; fin_cases k <;> rfl
theorem step_reverse_cons (tmp : Option Bool) (c b : Bool) (acc out : Bits) :
    machine.step (cfg 1 tmp c [] [] (b :: acc) out) =
      some (cfg 1 (some b) c [] [] acc (b :: out)) := by
  simp [machine, FinTM2.step, TM2.step, program, cfg, TM2.stepAux]
  congr 2
  funext k; fin_cases k <;> rfl

def reverse_run (acc : Bits) (tmp : Option Bool) (c : Bool) (out : Bits) :
    EvalsToInTime machine.step (cfg 1 tmp c [] [] acc out)
      (some (cfg 2 none false [] [] [] (acc.reverse ++ out))) (acc.length + 1) := by
  induction acc generalizing tmp out with
  | nil => exact once (step_reverse_nil tmp c out)
  | cons b acc ih =>
    simpa [List.reverse_cons, List.append_assoc] using
      prepend (step_reverse_cons tmp c b acc out) (ih (some b) (b :: out))

theorem step_done (tmp : Option Bool) (c : Bool) (acc out : Bits) :
    machine.step (cfg 0 tmp c [] [] acc out) =
      some (cfg 1 none c [] [] (if c then true :: acc else acc) out) := by
  cases c <;> simp [machine, FinTM2.step, TM2.step, program, cfg, mix, TM2.stepAux]
  all_goals congr 2
  all_goals funext k; fin_cases k <;> rfl
theorem step_left (tmp : Option Bool) (a c : Bool) (xs acc out : Bits) :
    machine.step (cfg 0 tmp c (a :: xs) [] acc out) =
      some (cfg 0 (some (digit a false c)) (carry a false c) xs [] (digit a false c :: acc) out) := by
  simp [machine, FinTM2.step, TM2.step, program, cfg, mix, TM2.stepAux]
  congr 2
  funext k; fin_cases k <;> rfl
theorem step_right (tmp : Option Bool) (b c : Bool) (ys acc out : Bits) :
    machine.step (cfg 0 tmp c [] (b :: ys) acc out) =
      some (cfg 0 (some (digit false b c)) (carry false b c) [] ys (digit false b c :: acc) out) := by
  simp [machine, FinTM2.step, TM2.step, program, cfg, mix, TM2.stepAux]
  congr 2
  funext k; fin_cases k <;> rfl
theorem step_both (tmp : Option Bool) (a b c : Bool) (xs ys acc out : Bits) :
    machine.step (cfg 0 tmp c (a :: xs) (b :: ys) acc out) =
      some (cfg 0 (some (digit a b c)) (carry a b c) xs ys (digit a b c :: acc) out) := by
  simp [machine, FinTM2.step, TM2.step, program, cfg, mix, TM2.stepAux]
  congr 2
  funext k; fin_cases k <;> rfl

def add_run (xs ys : Bits) (tmp : Option Bool) (c : Bool) (acc out : Bits) :
    EvalsToInTime machine.step (cfg 0 tmp c xs ys acc out)
      (some (cfg 2 none false [] [] [] (acc.reverse ++ addWords xs ys c ++ out)))
      (2 * (xs.length + ys.length) + acc.length + 3) := by
  induction xs generalizing ys tmp c acc with
  | nil =>
    induction ys generalizing tmp c acc with
    | nil =>
      have run := prepend (step_done tmp c acc out)
        (reverse_run (if c then true :: acc else acc) none c out)
      cases c <;> exact weaken (by simpa [addWords, List.reverse_cons, List.append_assoc] using run)
        (by simp)
    | cons b ys ih =>
      have run := prepend (step_right tmp b c ys acc out)
        (ih (some (digit false b c)) (carry false b c) (digit false b c :: acc))
      apply weaken (by simpa [addWords, List.reverse_cons, List.append_assoc] using run)
      simp; omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      have run := prepend (step_left tmp a c xs acc out)
        (ih [] (some (digit a false c)) (carry a false c) (digit a false c :: acc))
      apply weaken (by simpa [addWords, List.reverse_cons, List.append_assoc] using run)
      simp; omega
    | cons b ys =>
      have run := prepend (step_both tmp a b c xs ys acc out)
        (ih ys (some (digit a b c)) (carry a b c) (digit a b c :: acc))
      apply weaken (by simpa [addWords, List.reverse_cons, List.append_assoc] using run)
      simp; omega

theorem refines_addNatD (xs ys : Bits) :
    value (addWords xs ys false) = (TreeBudgetBitPrimitives.addNatD (value xs) (value ys)).value := by
  simp [addWords_value]

def addition_run (xs ys : Bits) : EvalsToInTime machine.step (cfg 0 none false xs ys [] [])
    (some (cfg 2 none false [] [] [] (addWords xs ys false))) (2 * (xs.length + ys.length) + 3) := by
  simpa using add_run xs ys none false [] []

def done (out : Bits) : Configuration (Fin 4) (Fin 3) :=
  ⟨none, (none, false), tapes [] [] [] out⟩

theorem step_return (out : Bits) : machine.step (cfg 2 none false [] [] [] out) =
    some (done out) := rfl

def addition_halts (xs ys : Bits) : EvalsToInTime machine.step (cfg 0 none false xs ys [] [])
    (some (done (addWords xs ys false))) (2 * (xs.length + ys.length) + 4) := by
  have run := EvalsToInTime.trans machine.step (2 * (xs.length + ys.length) + 3) 1 _ _ _
    (addition_run xs ys) (once (step_return (addWords xs ys false)))
  convert run using 1; omega

theorem done_terminal (out : Bits) : machine.step (done out) = none := rfl

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end UAVProof.TreeBudgetAddWordsTM2
