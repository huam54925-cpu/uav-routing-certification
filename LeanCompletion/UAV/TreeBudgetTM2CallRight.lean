import LeanCompletion.UAV.TreeBudgetTM2Call

/-! The right-bank counterpart of the existing caller compiler. This allows
two independently proved subprograms to share one finite-control caller. -/
namespace UAVProof.TreeBudgetTM2Call
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition

variable {K R Λ Ω : Type}

theorem updatedRight [DecidableEq K] [DecidableEq R] (k : K)
    (saved : R → Bits) (localStk : K → Bits) (v : Bits) :
    Function.update (banks saved localStk) (.inr k) v = banks saved (Function.update localStk k v) := by
  funext p
  cases p with
  | inl r => simp [banks]
  | inr i => by_cases h : i=k <;> simp [banks,Function.update_apply,h]

def compileRight (label : Λ → Ω) (ret : Ω) : Statement K Λ → Statement (R ⊕ K) Ω
  | .push k f q => .push (.inr k) f (compileRight label ret q)
  | .pop k f q => .pop (.inr k) f (compileRight label ret q)
  | .peek k f q => .peek (.inr k) f (compileRight label ret q)
  | .load f q => .load f (compileRight label ret q)
  | .branch f t e => .branch f (compileRight label ret t) (compileRight label ret e)
  | .goto f => .goto (fun s => label (f s))
  | .halt => .goto (fun _ => ret)

def embedRight (label : Λ → Ω) (ret : Ω) (saved : R → Bits) (c : Configuration K Λ) :
    Configuration (R ⊕ K) Ω := ⟨some (c.l.elim ret label),c.var,banks saved c.stk⟩

theorem statement_step_right [DecidableEq K] [DecidableEq R] (label : Λ → Ω) (ret : Ω)
    (saved : R → Bits) (q : Statement K Λ) (v : State) (s : K → Bits) :
    TM2.stepAux (compileRight label ret q) v (banks saved s) =
      embedRight label ret saved (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih => simp only [compileRight,TM2.stepAux,updatedRight]; exact ih _ _
  | pop k f q ih => simp only [compileRight,TM2.stepAux,updatedRight]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f t e ht he => cases h : f v <;> simp [compileRight,TM2.stepAux,h,ht,he]
  | goto f => rfl
  | halt => rfl

theorem selected_step_right [DecidableEq K] [DecidableEq R] (label : Λ → Ω) (ret : Ω)
    (saved : R → Bits) (A : Λ → Statement K Λ) (B : Ω → Statement (R ⊕ K) Ω)
    (linked : ∀ l, B (label l) = compileRight label ret (A l))
    (a b : Configuration K Λ) (h : TM2.step A a = some b) :
    TM2.step B (embedRight label ret saved a) = some (embedRight label ret saved b) := by
  cases a with
  | mk l v stk =>
    cases l with
    | none => simp [TM2.step] at h
    | some l =>
      simp only [TM2.step,Option.some.injEq] at h
      subst b
      simpa [embedRight,TM2.step,linked] using
        congrArg some (statement_step_right label ret saved (A l) v stk)

def call_run_right [DecidableEq K] [DecidableEq R] (label : Λ → Ω) (ret : Ω)
    (saved : R → Bits) (A : Λ → Statement K Λ) (B : Ω → Statement (R ⊕ K) Ω)
    (linked : ∀ l, B (label l) = compileRight label ret (A l))
    {a b : Configuration K Λ} {n : ℕ} (run : EvalsToInTime (TM2.step A) a (some b) n) :
    EvalsToInTime (TM2.step B) (embedRight label ret saved a) (some (embedRight label ret saved b)) n :=
  ⟨⟨run.steps,transport_steps _ _ _ (selected_step_right label ret saved A B linked)
    _ _ _ run.evals_in_steps⟩,run.steps_le_m⟩

end UAVProof.TreeBudgetTM2Call
