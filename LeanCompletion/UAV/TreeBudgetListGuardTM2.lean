import LeanCompletion.UAV.TreeBudgetNatListLoop
import LeanCompletion.UAV.TreeBudgetListCleanup
import LeanCompletion.UAV.TreeBudgetCanonicalDigits
import LeanCompletion.UAV.TreeBudgetCostedParsing

/-! The length guard debits one suffix bit per successful binary decrement.
The saved suffix is restored in order, producing one loop token per debit. -/
namespace UAVProof.TreeBudgetListGuardTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetCanonicalDigits
open Turing StateTransition Turing.TM2.Stmt

abbrev Label := TreeBudgetNatListLoop.L
abbrev Stmt := Statement (Fin 7) Label
abbrev Cfg := Configuration (Fin 7) Label

def ports : Ports (Fin 7) := ⟨0, 1, 2, by decide, by decide, by decide⟩
def lab : Phase → Label
  | .marker => 0 | .payload => 1 | .reverse => 2 | .clear => 3

def jump (l : Label) : Stmt := load (fun _ => (none,true)) (goto (fun _ => l))
def takeBit (k : Fin 7) (absent present : Stmt) : Stmt :=
  pop k (fun _ b => (b,true)) (branch (fun s => s.1.isNone) absent present)
def put (k : Fin 7) (b : Bool) := push (Λ := Label) (σ := State) (Γ := fun _ : Fin 7 => Bool) k (fun _ => b)
def moveBit (k : Fin 7) (next : Stmt) : Stmt := push k (fun s => s.1.getD false) next

/-- 4 borrows, 5 restores low ones, 6 debits a suffix bit, 7 clears
underflow scratch, 8 restores the suffix and produces the unary counter.
9 and 10 are caller return labels. -/
def program (l : Label) : Stmt :=
  match l.val with
  | 0 => code ports lab 4 10 true .marker
  | 1 => code ports lab 4 10 true .payload
  | 2 => code ports lab 4 10 true .reverse
  | 3 => code ports lab 4 10 true .clear
  | 4 => takeBit 2 (jump 7) (branch (fun s => s.1.getD false)
      (put 2 false (jump 5)) (put 1 true (jump 4)))
  | 5 => takeBit 1 (jump 6) (put 2 true (jump 5))
  | 6 => takeBit 0 (jump 10) (moveBit 3 (jump 4))
  | 7 => takeBit 1 (jump 8) (jump 7)
  | 8 => takeBit 3 (jump 9) (moveBit 0 (put 4 true (jump 8)))
  | 10 => TreeBudgetListCleanup.program
  | _ => TreeBudgetNatListLoop.loopCode l

def machine : FinTM2 where
  K := Fin 7
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Label
  main := 0
  σ := State
  initialState := (none,true)
  m := program

def layout (r d t saved tokens ctx : Bits) (k : Fin 7) : Bits :=
  match k.val with
  | 0 => r | 1 => t | 2 => d | 3 => saved | 4 => tokens | 5 => ctx | _ => []
def atLabel (l : Label) (r d t saved tokens ctx : Bits) : Cfg :=
  ⟨some l, (none,true), layout r d t saved tokens ctx⟩

theorem code_eq (p : Phase) : program (lab p) = code ports lab 4 10 true p := by cases p <;> rfl

theorem borrow_zero (r d t saved tokens ctx : Bits) :
    machine.step (atLabel 4 r (false :: d) t saved tokens ctx) = some (atLabel 4 r d (true :: t) saved tokens ctx) := by
  unfold machine FinTM2.step TM2.step atLabel
  simp [program, takeBit, jump, put, TM2.stepAux, layout]
  congr 2
  funext k; fin_cases k <;> rfl

theorem borrow_one (r d t saved tokens ctx : Bits) :
    machine.step (atLabel 4 r (true :: d) t saved tokens ctx) = some (atLabel 5 r (false :: d) t saved tokens ctx) := by
  unfold machine FinTM2.step TM2.step atLabel
  simp [program, takeBit, jump, put, TM2.stepAux, layout]
  congr 2
  funext k; fin_cases k <;> rfl

theorem borrow_empty (r t saved tokens ctx : Bits) :
    machine.step (atLabel 4 r [] t saved tokens ctx) = some (atLabel 7 r [] t saved tokens ctx) := by
  unfold machine FinTM2.step TM2.step atLabel
  simp [program, takeBit, jump, put, TM2.stepAux, layout]
  congr 2
  funext k; fin_cases k <;> rfl

theorem ones_cons (r d t saved tokens ctx : Bits) :
    machine.step (atLabel 5 r d (true :: t) saved tokens ctx) = some (atLabel 5 r (true :: d) t saved tokens ctx) := by
  unfold machine FinTM2.step TM2.step atLabel
  simp [program, takeBit, jump, put, TM2.stepAux, layout]
  congr 2
  funext k; fin_cases k <;> rfl

theorem ones_empty (r d saved tokens ctx : Bits) :
    machine.step (atLabel 5 r d [] saved tokens ctx) = some (atLabel 6 r d [] saved tokens ctx) := by
  unfold machine FinTM2.step TM2.step atLabel
  simp [program, takeBit, jump, put, TM2.stepAux, layout]
  congr 2
  funext k; fin_cases k <;> rfl

theorem debit_cons (r d saved tokens ctx : Bits) (b : Bool) :
    machine.step (atLabel 6 (b :: r) d [] saved tokens ctx) = some (atLabel 4 r d [] (b :: saved) tokens ctx) := by
  unfold machine FinTM2.step TM2.step atLabel
  simp [program, takeBit, jump, moveBit, TM2.stepAux, layout]
  congr 2
  funext k; fin_cases k <;> rfl

theorem debit_empty (d saved tokens ctx : Bits) :
    machine.step (atLabel 6 [] d [] saved tokens ctx) = some (atLabel 10 [] d [] saved tokens ctx) := by
  unfold machine FinTM2.step TM2.step atLabel
  simp [program, takeBit, jump, moveBit, TM2.stepAux, layout]
  congr 2
  funext k; fin_cases k <;> rfl

theorem clear_cons (r t saved tokens ctx : Bits) :
    machine.step (atLabel 7 r [] (true :: t) saved tokens ctx) = some (atLabel 7 r [] t saved tokens ctx) := by
  unfold machine FinTM2.step TM2.step atLabel
  simp [program, takeBit, jump, TM2.stepAux, layout]
  congr 2
  funext k; fin_cases k <;> rfl

theorem clear_empty (r saved tokens ctx : Bits) :
    machine.step (atLabel 7 r [] [] saved tokens ctx) = some (atLabel 8 r [] [] saved tokens ctx) := by
  unfold machine FinTM2.step TM2.step atLabel
  simp [program, takeBit, jump, TM2.stepAux, layout]
  congr 2
  funext k; fin_cases k <;> rfl

theorem restore_cons (r saved tokens ctx : Bits) (b : Bool) :
    machine.step (atLabel 8 r [] [] (b :: saved) tokens ctx) = some (atLabel 8 (b :: r) [] [] saved (true :: tokens) ctx) := by
  unfold machine FinTM2.step TM2.step atLabel
  simp [program, takeBit, jump, put, moveBit, TM2.stepAux, layout]
  congr 2
  funext k; fin_cases k <;> rfl

theorem restore_empty (r tokens ctx : Bits) :
    machine.step (atLabel 8 r [] [] [] tokens ctx) = some (atLabel 9 r [] [] [] tokens ctx) := by
  unfold machine FinTM2.step TM2.step atLabel
  simp [program, takeBit, jump, put, moveBit, TM2.stepAux, layout]
  congr 2
  funext k; fin_cases k <;> rfl

end UAVProof.TreeBudgetListGuardTM2
