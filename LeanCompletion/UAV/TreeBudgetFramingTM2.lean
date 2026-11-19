import LeanCompletion.UAV.TreeBudgetBinaryCodec
import Mathlib.Computability.TuringMachine.Computable

/-! First concrete finite-alphabet TM2 component: recognize whether the input
contains a complete framed word, exactly as parseWord does (not canonical Nat
validation). Both success and failure drain the input before halting. -/
namespace UAVProof.TreeBudgetFramingTM2
open TreeBudgetBinaryCodec Turing StateTransition
open Turing.TM2.Stmt

abbrev State := Option Bool × Bool
abbrev Statement := Turing.TM2.Stmt (fun _ : Bool => Bool) (Fin 3) State
abbrev Configuration := Turing.TM2.Cfg (fun _ : Bool => Bool) (Fin 3) State

def readInput (next : Statement) : Statement := pop false (fun s b => (b, s.2)) next
def result (b : Bool) : Statement := load (fun _ => (none, b)) (goto (fun _ => 2))

def program (label : Fin 3) : Statement :=
  if label = 0 then readInput
    (branch (fun s => s.1.isNone) (result false)
      (branch (fun s => s.1 == some false) (result true) (goto (fun _ => 1))))
  else if label = 1 then readInput
    (branch (fun s => s.1.isNone) (result false) (goto (fun _ => 0)))
  else readInput (branch (fun s => s.1.isNone)
    (push true Prod.snd (load (fun _ => (none, false)) halt)) (goto (fun _ => 2)))

def machine : Turing.FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := State
  initialState := (none, false)
  m := program

def tapes (input output : Bits) : Bool → Bits := fun k => if k then output else input
def cfg (label : Fin 3) (tmp : Option Bool) (b : Bool) (input : Bits) : Configuration :=
  ⟨some label, (tmp, b), tapes input []⟩
def done (b : Bool) : Configuration := ⟨none, (none, false), tapes [] [b]⟩

@[simp] theorem tapes_false (xs out : Bits) : tapes xs out false = xs := rfl
@[simp] theorem tapes_true (xs out : Bits) : tapes xs out true = out := rfl

@[simp] theorem update_input (xs ys out : Bits) :
    Function.update (tapes xs out) false ys = tapes ys out := by funext k; cases k <;> rfl
@[simp] theorem update_output (xs ys out : Bits) :
    Function.update (tapes xs out) true ys = tapes xs ys := by funext k; cases k <;> rfl

theorem step_drain_nil (tmp : Option Bool) (b : Bool) :
    machine.step (cfg 2 tmp b []) = some (done b) := by
  simp [machine, program, readInput, cfg, done, Turing.FinTM2.step, Turing.TM2.step,
    Turing.TM2.stepAux]
  congr 2
  funext k
  cases k <;> rfl

theorem step_drain_cons (tmp : Option Bool) (b a : Bool) (xs : Bits) :
    machine.step (cfg 2 tmp b (a :: xs)) = some (cfg 2 (some a) b xs) := by
  simp [machine, program, readInput, cfg, Turing.FinTM2.step, Turing.TM2.step,
    Turing.TM2.stepAux]
  congr 2
  funext k
  cases k <;> rfl

theorem step_marker_nil (tmp : Option Bool) (b : Bool) :
    machine.step (cfg 0 tmp b []) = some (cfg 2 none false []) := by
  simp [machine, program, readInput, result, cfg, Turing.FinTM2.step, Turing.TM2.step,
    Turing.TM2.stepAux]
  congr 2
  funext k
  cases k <;> rfl

theorem step_marker_false (tmp : Option Bool) (b : Bool) (xs : Bits) :
    machine.step (cfg 0 tmp b (false :: xs)) = some (cfg 2 none true xs) := by
  simp [machine, program, readInput, result, cfg, Turing.FinTM2.step, Turing.TM2.step,
    Turing.TM2.stepAux]
  congr 2
  funext k
  cases k <;> rfl

theorem step_marker_true (tmp : Option Bool) (b : Bool) (xs : Bits) :
    machine.step (cfg 0 tmp b (true :: xs)) = some (cfg 1 (some true) b xs) := by
  simp [machine, program, readInput, result, cfg, Turing.FinTM2.step, Turing.TM2.step,
    Turing.TM2.stepAux]
  congr 2
  funext k
  cases k <;> rfl

theorem step_payload_nil (tmp : Option Bool) (b : Bool) :
    machine.step (cfg 1 tmp b []) = some (cfg 2 none false []) := by
  simp [machine, program, readInput, result, cfg, Turing.FinTM2.step, Turing.TM2.step,
    Turing.TM2.stepAux]
  congr 2
  funext k
  cases k <;> rfl

theorem step_payload_cons (tmp : Option Bool) (b a : Bool) (xs : Bits) :
    machine.step (cfg 1 tmp b (a :: xs)) = some (cfg 0 (some a) b xs) := by
  simp [machine, program, readInput, result, cfg, Turing.FinTM2.step, Turing.TM2.step,
    Turing.TM2.stepAux]
  congr 2
  funext k
  cases k <;> rfl

def once {a b : Configuration} (h : machine.step a = some b) :
    EvalsToInTime machine.step a (some b) 1 := ⟨⟨1, by simpa using h⟩, le_rfl⟩

def prepend {a b : Configuration} {out : Option Configuration} {t : ℕ}
    (h : machine.step a = some b) (tail : EvalsToInTime machine.step b out t) :
    EvalsToInTime machine.step a out (t + 1) :=
  EvalsToInTime.trans machine.step 1 t a b out (once h) tail

def weaken {a : Configuration} {out : Option Configuration} {s t : ℕ}
    (run : EvalsToInTime machine.step a out s) (h : s ≤ t) :
    EvalsToInTime machine.step a out t := ⟨run.toEvalsTo, run.steps_le_m.trans h⟩

def drain_run (xs : Bits) (tmp : Option Bool) (b : Bool) :
    EvalsToInTime machine.step (cfg 2 tmp b xs) (some (done b)) (xs.length + 1) := by
  induction xs generalizing tmp with
  | nil => exact once (step_drain_nil tmp b)
  | cons a xs ih => exact prepend (step_drain_cons tmp b a xs) (ih (some a))

def framingOK (xs : Bits) : Bool := (parseWord xs).isSome

def marker_run (xs : Bits) (tmp : Option Bool) (b : Bool) :
    EvalsToInTime machine.step (cfg 0 tmp b xs) (some (done (framingOK xs))) (xs.length + 2) :=
  match xs with
  | [] => prepend (step_marker_nil tmp b) (drain_run [] none false)
  | false :: xs =>
    weaken (prepend (step_marker_false tmp b xs) (drain_run xs none true)) (by simp)
  | true :: [] =>
    prepend (step_marker_true tmp b [])
      (prepend (step_payload_nil (some true) b) (drain_run [] none false))
  | true :: a :: xs => by
    have tail := marker_run xs (some a) b
    have run := prepend (step_marker_true tmp b (a :: xs))
      (prepend (step_payload_cons (some true) b a xs) tail)
    simpa [framingOK, parseWord, List.length_cons, Nat.add_assoc] using run

theorem init_eq (xs : Bits) : Turing.initList machine xs = cfg 0 none false xs := by
  simp only [Turing.initList, cfg, machine]
  congr 1
  funext k
  cases k <;> rfl

theorem halt_eq (b : Bool) : Turing.haltList machine [b] = done b := by
  simp only [Turing.haltList, done, machine]
  congr 1

def outputs (xs : Bits) : Turing.TM2OutputsInTime machine xs (some [framingOK xs]) (xs.length + 2) := by
  change EvalsToInTime machine.step _ _ _
  simp only [Option.map_some, init_eq, halt_eq]
  exact marker_run xs none false

noncomputable def computer : Turing.TM2ComputableInPolyTime (fun xs : Bits => xs)
    (fun b : Bool => [b]) framingOK where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 2
  outputsFun xs := by
    change TM2OutputsInTime machine (xs.map id) (some [id (framingOK xs)]) _
    simpa using outputs xs

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end UAVProof.TreeBudgetFramingTM2
