import LeanCompletion.UAV.TreeBudgetFrameRoutineTM2

/-! Relabel a Boolean-stack TM2 subprogram, preserve caller-owned stacks and
return to a real continuation when the callee executes halt. Each callee
transition takes exactly one caller transition. -/
namespace UAVProof.TreeBudgetTM2Call
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition

def banks {K R : Type} (localStk : K → Bits) (saved : R → Bits) : K ⊕ R → Bits :=
  Sum.elim localStk saved

theorem updated {K R : Type} [DecidableEq K] [DecidableEq R] (k : K)
    (a : K → Bits) (b : R → Bits) (v : Bits) :
    Function.update (banks a b) (.inl k) v = banks (Function.update a k v) b := by
  funext p
  cases p with
  | inr r => simp [banks]
  | inl i => by_cases h : i = k <;> simp [banks, Function.update_apply, h]

variable {K R Λ Ω : Type}

def compile (label : Λ → Ω) (ret : Ω) : Statement K Λ → Statement (K ⊕ R) Ω
  | .push k f q => .push (.inl k) f (compile label ret q)
  | .pop k f q => .pop (.inl k) f (compile label ret q)
  | .peek k f q => .peek (.inl k) f (compile label ret q)
  | .load f q => .load f (compile label ret q)
  | .branch f t e => .branch f (compile label ret t) (compile label ret e)
  | .goto f => .goto (fun s => label (f s))
  | .halt => .goto (fun _ => ret)

def embed (label : Λ → Ω) (ret : Ω) (saved : R → Bits) (c : Configuration K Λ) :
    Configuration (K ⊕ R) Ω :=
  ⟨some (c.l.elim ret label), c.var, banks c.stk saved⟩

theorem statement_step [DecidableEq K] [DecidableEq R] (label : Λ → Ω) (ret : Ω)
    (saved : R → Bits) (q : Statement K Λ) (v : State) (s : K → Bits) :
    TM2.stepAux (compile label ret q) v (banks s saved) =
      embed label ret saved (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih => simp only [compile, TM2.stepAux, updated]; exact ih _ _
  | pop k f q ih => simp only [compile, TM2.stepAux, updated]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f t e ht he => cases h : f v <;> simp [compile, TM2.stepAux, h, ht, he]
  | goto f => rfl
  | halt => rfl

theorem selected_step [DecidableEq K] [DecidableEq R] (label : Λ → Ω) (ret : Ω)
    (saved : R → Bits) (A : Λ → Statement K Λ) (B : Ω → Statement (K ⊕ R) Ω)
    (linked : ∀ l, B (label l) = compile label ret (A l))
    (a b : Configuration K Λ) (h : TM2.step A a = some b) :
    TM2.step B (embed label ret saved a) = some (embed label ret saved b) := by
  cases a with
  | mk l v stk =>
    cases l with
    | none => simp [TM2.step] at h
    | some l =>
      simp only [TM2.step, Option.some.injEq] at h
      subst b
      simpa [embed, TM2.step, linked] using congrArg some (statement_step label ret saved (A l) v stk)

private theorem after_none {S : Type} (f : S → Option S) (n : ℕ) :
    (flip bind f)^[n] (none : Option S) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Function.iterate_succ_apply] using ih

theorem transport_steps {S T : Type} (f : S → Option S) (g : T → Option T) (e : S → T)
    (step : ∀ a b, f a = some b → g (e a) = some (e b)) (n : ℕ) (a b : S)
    (h : (flip bind f)^[n] (some a) = some b) :
    (flip bind g)^[n] (some (e a)) = some (e b) := by
  induction n generalizing a with
  | zero => simpa using congrArg (Option.map e) h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (flip bind f)^[n] (f a) = some b at h
    change (flip bind g)^[n] (g (e a)) = some (e b)
    cases hf : f a with
    | none => rw [hf, after_none] at h; contradiction
    | some a' => rw [step _ _ hf]; exact ih a' (hf ▸ h)

def call_run [DecidableEq K] [DecidableEq R] (label : Λ → Ω) (ret : Ω)
    (saved : R → Bits) (A : Λ → Statement K Λ) (B : Ω → Statement (K ⊕ R) Ω)
    (linked : ∀ l, B (label l) = compile label ret (A l))
    {a b : Configuration K Λ} {n : ℕ} (run : EvalsToInTime (TM2.step A) a (some b) n) :
    EvalsToInTime (TM2.step B) (embed label ret saved a) (some (embed label ret saved b)) n :=
  ⟨⟨run.steps, transport_steps _ _ _ (selected_step label ret saved A B linked)
    _ _ _ run.evals_in_steps⟩, run.steps_le_m⟩

end UAVProof.TreeBudgetTM2Call
