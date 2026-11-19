import LeanCompletion.UAV.TreeBudgetFrameRoutineTM2

namespace UAVProof.TreeBudgetListCleanup
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing Turing.TM2.Stmt StateTransition

abbrev Cfg := Configuration (Fin 7) (Fin 18)
abbrev Stmt := Statement (Fin 7) (Fin 18)

/-- At the reject label, discard one live scratch cell per transition.
When all five work stacks are empty, halt with the failure flag. -/
def discard (k : Fin 7) (next : Stmt) : Stmt :=
  pop k (fun _ b => (b,true)) (branch (fun s => s.1.isNone) next
    (load (fun _ => (none,true)) (goto (fun _ => 10))))
def program : Stmt := discard 1 (discard 2 (discard 3 (discard 4 (discard 6
  (load (fun _ => (none,false)) halt)))))

def tapes (r t d s k acc ctx : Bits) (i : Fin 7) : Bits :=
  match i.val with
  | 0 => r | 1 => t | 2 => d | 3 => s | 4 => k | 5 => ctx | _ => acc
def cfg (r t d s k acc ctx : Bits) : Cfg := ⟨some 10,(none,true),tapes r t d s k acc ctx⟩
def done (r ctx : Bits) : Cfg := ⟨none,(none,false),tapes r [] [] [] [] [] ctx⟩
def workCells (c : Cfg) := (c.stk 1).length+(c.stk 2).length+(c.stk 3).length+
  (c.stk 4).length+(c.stk 6).length

variable {M : Fin 18 → Stmt} (hM : M 10 = program)
include hM

theorem step_0 (b : Bool) (r t d s k acc ctx : Bits) :
    TM2.step M (cfg r (b :: t) d s k acc ctx) = some (cfg r t d s k acc ctx) := by
  simp [TM2.step, cfg, hM, program, discard, TM2.stepAux, tapes]
  all_goals funext j; fin_cases j <;> rfl

theorem step_1 (b : Bool) (r d s k acc ctx : Bits) :
    TM2.step M (cfg r [] (b :: d) s k acc ctx) = some (cfg r [] d s k acc ctx) := by
  simp [TM2.step, cfg, hM, program, discard, TM2.stepAux, tapes]
  all_goals funext j; fin_cases j <;> rfl

theorem step_2 (b : Bool) (r s k acc ctx : Bits) :
    TM2.step M (cfg r [] [] (b :: s) k acc ctx) = some (cfg r [] [] s k acc ctx) := by
  simp [TM2.step, cfg, hM, program, discard, TM2.stepAux, tapes]
  all_goals funext j; fin_cases j <;> rfl

theorem step_3 (b : Bool) (r k acc ctx : Bits) :
    TM2.step M (cfg r [] [] [] (b :: k) acc ctx) = some (cfg r [] [] [] k acc ctx) := by
  simp [TM2.step, cfg, hM, program, discard, TM2.stepAux, tapes]
  all_goals funext j; fin_cases j <;> rfl

theorem step_4 (b : Bool) (r acc ctx : Bits) :
    TM2.step M (cfg r [] [] [] [] (b :: acc) ctx) = some (cfg r [] [] [] [] acc ctx) := by
  simp [TM2.step, cfg, hM, program, discard, TM2.stepAux, tapes]
  all_goals funext j; fin_cases j <;> rfl

theorem step_5 (r  ctx : Bits) :
    TM2.step M (cfg r [] [] [] [] [] ctx) = some (done r ctx) := by
  simp [TM2.step, cfg, done, hM, program, discard, TM2.stepAux, tapes]
  all_goals funext j; fin_cases j <;> rfl

def clean_run (fuel : ℕ) (r t d s k acc ctx : Bits)
    (hf : t.length+d.length+s.length+k.length+acc.length ≤ fuel) :
    EvalsToInTime (TM2.step M) (cfg r t d s k acc ctx) (some (done r ctx)) (fuel+1) := by
  induction fuel generalizing t d s k acc with
  | zero =>
    simp at hf
    obtain ⟨⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩ := hf
    exact once (step_5 hM r ctx)
  | succ fuel ih =>
    cases t with
    | cons b t =>
      exact prepend (step_0 hM b r t d s k acc ctx)
        (ih t d s k acc (by simp at hf ⊢; omega))
    | nil =>
      cases d with
      | cons b d =>
        exact prepend (step_1 hM b r d s k acc ctx)
          (ih [] d s k acc (by simp at hf ⊢; omega))
      | nil =>
        cases s with
        | cons b s =>
          exact prepend (step_2 hM b r s k acc ctx)
            (ih [] [] s k acc (by simp at hf ⊢; omega))
        | nil =>
          cases k with
          | cons b k =>
            exact prepend (step_3 hM b r k acc ctx)
              (ih [] [] [] k acc (by simp at hf ⊢; omega))
          | nil =>
            cases acc with
            | cons b acc =>
              exact prepend (step_4 hM b r acc ctx)
                (ih [] [] [] [] acc (by simp at hf ⊢; omega))
            | nil =>
              exact weaken (once (step_5 hM r ctx)) (by omega)

end UAVProof.TreeBudgetListCleanup
