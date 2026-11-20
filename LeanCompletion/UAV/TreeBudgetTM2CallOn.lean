import LeanCompletion.UAV.TreeBudgetTM2Call

/-! Subprogram calls on a selected bank, including banks nested in larger sums.
The selector is static wiring; it never inspects the contents of a stack. -/
namespace UAVProof.TreeBudgetTM2CallOn
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition

structure Wiring (K R : Type) where
  put : K → R
  get : R → Option K
  get_put : ∀ k, get (put k)=some k
  get_eq : ∀ r k, get r=some k → r=put k

variable {K R Λ Ω : Type}

def bank (w : Wiring K R) (saved : R → Bits) (localStk : K → Bits) (r : R) : Bits :=
  (w.get r).elim (saved r) localStk

@[simp] theorem bank_put (w : Wiring K R) (saved : R → Bits) (s : K → Bits) (k : K) :
    bank w saved s (w.put k)=s k := by simp [bank,w.get_put]

theorem updated [DecidableEq K] [DecidableEq R] (w : Wiring K R)
    (saved : R → Bits) (s : K → Bits) (k : K) (v : Bits) :
    Function.update (bank w saved s) (w.put k) v = bank w saved (Function.update s k v) := by
  funext r
  cases h : w.get r with
  | none =>
    have hr : r≠w.put k := by intro he; rw [he,w.get_put] at h; contradiction
    simp [bank,h,hr]
  | some i =>
    have hr := w.get_eq r i h
    have hi : w.put i=w.put k ↔ i=k := by
      constructor
      · intro he; have := congrArg w.get he; simpa [w.get_put] using this
      · exact congrArg w.put
    subst r
    by_cases he : i=k <;> simp [Function.update_apply,hi,he]

def compile (w : Wiring K R) (label : Λ → Ω) (ret : Ω) : Statement K Λ → Statement R Ω
  | .push k f q => .push (w.put k) f (compile w label ret q)
  | .pop k f q => .pop (w.put k) f (compile w label ret q)
  | .peek k f q => .peek (w.put k) f (compile w label ret q)
  | .load f q => .load f (compile w label ret q)
  | .branch f t e => .branch f (compile w label ret t) (compile w label ret e)
  | .goto f => .goto (fun s => label (f s))
  | .halt => .goto (fun _ => ret)

def embed (w : Wiring K R) (label : Λ → Ω) (ret : Ω) (saved : R → Bits)
    (c : Configuration K Λ) : Configuration R Ω :=
  ⟨some (c.l.elim ret label),c.var,bank w saved c.stk⟩

theorem statement_step [DecidableEq K] [DecidableEq R] (w : Wiring K R)
    (label : Λ → Ω) (ret : Ω) (saved : R → Bits) (q : Statement K Λ) (v : State) (s : K → Bits) :
    TM2.stepAux (compile w label ret q) v (bank w saved s) =
      embed w label ret saved (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih => simp only [compile,TM2.stepAux,bank_put,updated]; exact ih _ _
  | pop k f q ih => simp only [compile,TM2.stepAux,bank_put,updated]; exact ih _ _
  | peek k f q ih => simp only [compile,TM2.stepAux,bank_put]; exact ih _ _
  | load f q ih => exact ih _ _
  | branch f t e ht he => cases h : f v <;> simp [compile,TM2.stepAux,h,ht,he]
  | goto f => rfl
  | halt => rfl

theorem selected_step [DecidableEq K] [DecidableEq R] (w : Wiring K R)
    (label : Λ → Ω) (ret : Ω) (saved : R → Bits) (A : Λ → Statement K Λ) (B : Ω → Statement R Ω)
    (linked : ∀ l, B (label l)=compile w label ret (A l))
    (a b : Configuration K Λ) (h : TM2.step A a=some b) :
    TM2.step B (embed w label ret saved a)=some (embed w label ret saved b) := by
  cases a with
  | mk l v stk =>
    cases l with
    | none => simp [TM2.step] at h
    | some l =>
      simp only [TM2.step,Option.some.injEq] at h
      subst b
      simpa [embed,TM2.step,linked] using congrArg some (statement_step w label ret saved (A l) v stk)

def call_run [DecidableEq K] [DecidableEq R] (w : Wiring K R)
    (label : Λ → Ω) (ret : Ω) (saved : R → Bits) (A : Λ → Statement K Λ) (B : Ω → Statement R Ω)
    (linked : ∀ l, B (label l)=compile w label ret (A l))
    {a b : Configuration K Λ} {n : ℕ} (h : EvalsToInTime (TM2.step A) a (some b) n) :
    EvalsToInTime (TM2.step B) (embed w label ret saved a) (some (embed w label ret saved b)) n :=
  ⟨⟨h.steps,TreeBudgetTM2Call.transport_steps _ _ _ (selected_step w label ret saved A B linked)
    _ _ _ h.evals_in_steps⟩,h.steps_le_m⟩

end UAVProof.TreeBudgetTM2CallOn
