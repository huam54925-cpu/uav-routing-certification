import LeanCompletion.UAV.TreeBudgetAddWordsTM2

/-! A finite-state comparator on arbitrary little-endian words. A higher
differing digit replaces the comparison of all lower digits. Padding is
allowed, and both true and false results have actual linear TM2 time. -/
namespace UAVProof.TreeBudgetLeWordsTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition Turing.TM2.Stmt
open TreeBudgetAddWordsTM2 (tapes)

def flag (a b old : Bool) : Bool := if a == b then old else b

def leWords : Bits → Bits → Bool → Bool
  | [], [], old => old
  | a :: xs, [], old => leWords xs [] (flag a false old)
  | [], b :: ys, old => leWords [] ys (flag false b old)
  | a :: xs, b :: ys, old => leWords xs ys (flag a b old)

theorem compare_bit (n m : ℕ) (a b old : Bool) :
    (n < m ∨ (n = m ∧ flag a b old = true)) ↔
      (Nat.bit a n < Nat.bit b m ∨ (Nat.bit a n = Nat.bit b m ∧ old = true)) := by
  cases a <;> cases b <;> cases old <;> simp [flag, Nat.bit] <;> omega

theorem leWords_value (xs ys : Bits) (old : Bool) :
    leWords xs ys old = decide (value xs < value ys ∨ (value xs = value ys ∧ old = true)) := by
  induction xs generalizing ys old with
  | nil =>
    induction ys generalizing old with
    | nil => cases old <;> simp [leWords, value]
    | cons b ys ih =>
      rw [leWords, ih]
      simpa only [value] using Bool.decide_congr (compare_bit 0 (value ys) false b old)
  | cons a xs ih =>
    cases ys with
    | nil =>
      rw [leWords, ih]
      simpa only [value] using Bool.decide_congr (compare_bit (value xs) 0 a false old)
    | cons b ys =>
      rw [leWords, ih]
      exact Bool.decide_congr (compare_bit (value xs) (value ys) a b old)

theorem refines_leNatD (xs ys : Bits) :
    leWords xs ys true = (TreeBudgetBitPrimitives.leNatD (value xs) (value ys)).value := by
  simp only [leWords_value, TreeBudgetBitPrimitives.leNatD_value, and_true]
  apply Bool.decide_congr
  omega

def mix (s : State) (b : Option Bool) : State :=
  if s.1.isNone && b.isNone then (none, s.2) else
    (some false, flag (s.1.getD false) (b.getD false) s.2)

def program (_ : Unit) : Statement (Fin 4) Unit :=
  pop 0 (fun s a => (a, s.2)) (pop 1 mix
    (branch (fun s => s.1.isNone)
      (push 3 Prod.snd (load (fun _ => (none, true)) halt)) (goto (fun _ => ()))))

def machine : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := State
  initialState := (none, true)
  m := program

def cfg (tmp : Option Bool) (old : Bool) (xs ys : Bits) : Configuration (Fin 4) Unit :=
  ⟨some (), (tmp, old), tapes xs ys [] []⟩
def done (b : Bool) : Configuration (Fin 4) Unit := ⟨none, (none, true), tapes [] [] [] [b]⟩

theorem step_done (tmp : Option Bool) (old : Bool) :
    machine.step (cfg tmp old [] []) = some (done old) := by
  simp [machine, FinTM2.step, TM2.step, program, cfg, done, mix, TM2.stepAux]
  congr 2
  funext k; fin_cases k <;> rfl
theorem step_left (tmp : Option Bool) (a old : Bool) (xs : Bits) :
    machine.step (cfg tmp old (a :: xs) []) = some (cfg (some false) (flag a false old) xs []) := by
  simp [machine, FinTM2.step, TM2.step, program, cfg, mix, TM2.stepAux]
  congr 2
  funext k; fin_cases k <;> rfl
theorem step_right (tmp : Option Bool) (b old : Bool) (ys : Bits) :
    machine.step (cfg tmp old [] (b :: ys)) = some (cfg (some false) (flag false b old) [] ys) := by
  simp [machine, FinTM2.step, TM2.step, program, cfg, mix, TM2.stepAux]
  congr 2
  funext k; fin_cases k <;> rfl
theorem step_both (tmp : Option Bool) (a b old : Bool) (xs ys : Bits) :
    machine.step (cfg tmp old (a :: xs) (b :: ys)) = some (cfg (some false) (flag a b old) xs ys) := by
  simp [machine, FinTM2.step, TM2.step, program, cfg, mix, TM2.stepAux]
  congr 2
  funext k; fin_cases k <;> rfl

def compare_run (xs ys : Bits) (tmp : Option Bool) (old : Bool) :
    EvalsToInTime machine.step (cfg tmp old xs ys) (some (done (leWords xs ys old)))
      (xs.length + ys.length + 1) := by
  induction xs generalizing ys tmp old with
  | nil =>
    induction ys generalizing tmp old with
    | nil => simpa [leWords] using once (step_done tmp old)
    | cons b ys ih =>
      simpa [leWords, Nat.add_assoc] using prepend (step_right tmp b old ys)
        (ih (some false) (flag false b old))
  | cons a xs ih =>
    cases ys with
    | nil =>
      simpa [leWords, Nat.add_assoc] using prepend (step_left tmp a old xs)
        (ih [] (some false) (flag a false old))
    | cons b ys =>
      have run := prepend (step_both tmp a b old xs ys)
        (ih ys (some false) (flag a b old))
      apply weaken (by simpa [leWords] using run)
      simp; omega

def comparison_run (xs ys : Bits) :
    EvalsToInTime machine.step (cfg none true xs ys)
      (some (done ((TreeBudgetBitPrimitives.leNatD (value xs) (value ys)).value)))
      (xs.length + ys.length + 1) := by
  simpa [refines_leNatD] using compare_run xs ys none true

theorem done_terminal (b : Bool) : machine.step (done b) = none := rfl
theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end UAVProof.TreeBudgetLeWordsTM2
