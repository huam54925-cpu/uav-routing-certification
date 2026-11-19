import LeanCompletion.UAV.TreeBudgetAddWordsTM2

/-! Shift-and-add with a preloaded accumulator. Each pass copies and restores
the shifted operand, and transfers the sum back in little-endian order. -/
namespace UAVProof.TreeBudgetWeightedTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition Turing.TM2.Stmt
open TreeBudgetAddWordsTM2 (addWords digit carry)
abbrev Cfg := Configuration (Fin 6) (Fin 6)
abbrev Stmt := Statement (Fin 6) (Fin 6)

def jump (l : Fin 6) : Stmt := load (fun _ => (none,false)) (goto (fun _ => l))
def getBit (i : Fin 6) (q : Stmt) : Stmt := pop i (fun s b => (b,s.2)) q
def pushBit (i : Fin 6) (q : Stmt) : Stmt := push i (fun s => s.1.getD false) q
def addDigit : Stmt :=
  pop 2 TreeBudgetAddWordsTM2.mix
    (branch (fun s => s.1.isNone)
      (branch Prod.snd (push 4 (fun _ => true) (jump 2)) (jump 2))
      (pushBit 4 (load (fun s => (none,s.2)) (goto (fun _ => 1)))))

def program (l : Fin 6) : Stmt :=
  match l.val with
  | 0 => getBit 0 (branch (fun s => s.1.isNone) (jump 4)
      (branch (fun s => s.1.getD false) (jump 1) (push 1 (fun _ => false) (jump 0))))
  | 1 => getBit 1 (branch (fun s => s.1.isNone) addDigit (pushBit 3 addDigit))
  | 2 => getBit 3 (branch (fun s => s.1.isNone) (push 1 (fun _ => false) (jump 3))
      (pushBit 1 (jump 2)))
  | 3 => getBit 4 (branch (fun s => s.1.isNone) (jump 0) (pushBit 2 (jump 3)))
  | 4 => getBit 1 (branch (fun s => s.1.isNone) (jump 5) (jump 4))
  | _ => halt

def machine : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Fin 6
  main := 0
  σ := State
  initialState := (none,false)
  m := program

def cfg (l : Fin 6) (c : Bool) (x h a copy buf ctx : Bits) : Cfg :=
  ⟨some l,(none,c), fun k => match k.val with
    | 0 => x | 1 => h | 2 => a | 3 => copy | 4 => buf | _ => ctx⟩

local macro "reduce_step" : tactic => `(tactic|
  (simp [machine, FinTM2.step, TM2.step, cfg, program, getBit, pushBit, jump,
    addDigit, TreeBudgetAddWordsTM2.mix, TM2.stepAux]
   all_goals try congr 2
   all_goals funext k; fin_cases k <;> rfl))

theorem outer_nil (h a ctx : Bits) :
    machine.step (cfg 0 false [] h a [] [] ctx) = some (cfg 4 false [] h a [] [] ctx) := by
  reduce_step

theorem outer_false (x h a ctx : Bits) :
    machine.step (cfg 0 false (false :: x) h a [] [] ctx) = some (cfg 0 false x (false :: h) a [] [] ctx) := by
  reduce_step

theorem outer_true (x h a ctx : Bits) :
    machine.step (cfg 0 false (true :: x) h a [] [] ctx) = some (cfg 1 false x h a [] [] ctx) := by
  reduce_step

theorem add_both (b d c : Bool) (x h a cp buf ctx : Bits) :
    machine.step (cfg 1 c x (b :: h) (d :: a) cp buf ctx) = some (cfg 1 (carry b d c) x h a (b :: cp) (digit b d c :: buf) ctx) := by
  reduce_step

theorem add_left (b c : Bool) (x h cp buf ctx : Bits) :
    machine.step (cfg 1 c x (b :: h) [] cp buf ctx) = some (cfg 1 (carry b false c) x h [] (b :: cp) (digit b false c :: buf) ctx) := by
  reduce_step

theorem add_right (d c : Bool) (x a cp buf ctx : Bits) :
    machine.step (cfg 1 c x [] (d :: a) cp buf ctx) = some (cfg 1 (carry false d c) x [] a cp (digit false d c :: buf) ctx) := by
  reduce_step

theorem add_end (c : Bool) (x cp buf ctx : Bits) :
    machine.step (cfg 1 c x [] [] cp buf ctx) = some (cfg 2 false x [] [] cp (if c then true :: buf else buf) ctx) := by
  cases c <;> reduce_step

theorem restore_one (b : Bool) (x h cp buf ctx : Bits) :
    machine.step (cfg 2 false x h [] (b :: cp) buf ctx) = some (cfg 2 false x (b :: h) [] cp buf ctx) := by
  reduce_step

theorem restore_end (x h buf ctx : Bits) :
    machine.step (cfg 2 false x h [] [] buf ctx) = some (cfg 3 false x (false :: h) [] [] buf ctx) := by
  reduce_step

theorem sum_one (b : Bool) (x h a buf ctx : Bits) :
    machine.step (cfg 3 false x h a [] (b :: buf) ctx) = some (cfg 3 false x h (b :: a) [] buf ctx) := by
  reduce_step

theorem sum_end (x h a ctx : Bits) :
    machine.step (cfg 3 false x h a [] [] ctx) = some (cfg 0 false x h a [] [] ctx) := by
  reduce_step

theorem clear_one (b : Bool) (h a ctx : Bits) :
    machine.step (cfg 4 false [] (b :: h) a [] [] ctx) = some (cfg 4 false [] h a [] [] ctx) := by
  reduce_step

theorem clear_end (a ctx : Bits) :
    machine.step (cfg 4 false [] [] a [] [] ctx) = some (cfg 5 false [] [] a [] [] ctx) := by
  reduce_step

end UAVProof.TreeBudgetWeightedTM2
