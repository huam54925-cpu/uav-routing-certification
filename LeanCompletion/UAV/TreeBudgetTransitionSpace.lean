import LeanCompletion.UAV.TreeBudgetTM2CallOn

/-! Physical stack space follows from the actual transition count. This bound
is independent of success and includes every nested push in a TM2 statement. -/
namespace UAVProof.TreeBudgetTransitionSpace
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
variable {K Λ : Type} [DecidableEq K]

def pushes : Statement K Λ → ℕ
  | .push _ _ q => pushes q+1
  | .pop _ _ q => pushes q
  | .peek _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ a b => max (pushes a) (pushes b)
  | .goto _ => 0
  | .halt => 0

def Bounded (s : K → Bits) (n : ℕ) : Prop := ∀ k, (s k).length≤n

theorem update_bound (s : K → Bits) (n : ℕ) (h : Bounded s n)
    (k : K) (v : Bits) (hv : v.length≤n) : Bounded (Function.update s k v) n := by
  intro j
  by_cases hj : j=k
  · subst j; simpa using hv
  · simpa [Function.update_of_ne hj] using h j

theorem statement_bound (q : Statement K Λ) (v : State) (s : K → Bits) (n : ℕ)
    (h : Bounded s n) : Bounded (TM2.stepAux q v s).stk (n+pushes q) := by
  induction q generalizing v s n with
  | push k f q ih =>
    have hb : Bounded (Function.update s k (f v::s k)) (n+1) := by
      apply update_bound s (n+1) (fun j => (h j).trans (by omega))
      simp only [List.length_cons]; exact Nat.add_le_add_right (h k) 1
    simpa only [TM2.stepAux,pushes,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih _ _ _ hb
  | pop k f q ih =>
    have hb := update_bound s n h k (s k).tail (by simpa only [List.length_tail] using (Nat.sub_le (s k).length 1).trans (h k))
    simpa only [TM2.stepAux,pushes] using ih _ _ _ hb
  | peek k f q ih => exact ih _ _ _ h
  | load f q ih => exact ih _ _ _ h
  | branch f a b ia ib =>
    cases hf : f v
    · intro k
      simpa only [TM2.stepAux,hf,Bool.false_eq_true,ite_false,pushes] using
        (ib v s n h k).trans (Nat.add_le_add_left (Nat.le_max_right (pushes a) (pushes b)) n)
    · intro k
      simpa only [TM2.stepAux,hf,ite_true,pushes] using
        (ia v s n h k).trans (Nat.add_le_add_left (Nat.le_max_left (pushes a) (pushes b)) n)
  | goto f => simpa only [TM2.stepAux,pushes,Nat.add_zero] using h
  | halt => simpa only [TM2.stepAux,pushes,Nat.add_zero] using h

theorem transition_bound (M : Λ → Statement K Λ) (B : ℕ)
    (hM : ∀ l, pushes (M l)≤B) (a b : Configuration K Λ)
    (hstep : TM2.step M a=some b) (n : ℕ) (h : Bounded a.stk n) :
    Bounded b.stk (n+B) := by
  cases a with
  | mk l v s =>
    cases l with
    | none => simp [TM2.step] at hstep
    | some l =>
      simp only [TM2.step,Option.some.injEq] at hstep
      subst b
      intro k
      exact (statement_bound (M l) v s n h k).trans (Nat.add_le_add_left (hM l) n)

theorem iterate_bound (M : Λ → Statement K Λ) (B : ℕ)
    (hM : ∀ l, pushes (M l)≤B) (t : ℕ) (a b : Configuration K Λ)
    (he : (flip bind (TM2.step M))^[t] (some a)=some b)
    (n : ℕ) (h : Bounded a.stk n) : Bounded b.stk (n+t*B) := by
  induction t generalizing a n with
  | zero => simp only [Function.iterate_zero_apply,Option.some.injEq] at he; subst b; simpa using h
  | succ t ih =>
    rw [Function.iterate_succ_apply] at he
    change (flip bind (TM2.step M))^[t] (TM2.step M a)=some b at he
    cases hs : TM2.step M a with
    | none =>
      have hn : ∀ j, (flip bind (TM2.step M))^[j] (none : Option (Configuration K Λ))=none := by
        intro j; induction j with
        | zero => rfl
        | succ j ij => simpa only [Function.iterate_succ_apply,flip,Option.bind_none] using ij
      rw [hs,hn] at he
      cases he
    | some c =>
      rw [hs] at he
      have hc := transition_bound M B hM a c hs n h
      simpa only [Nat.succ_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih c he (n+B) hc

theorem run_bound (M : Λ → Statement K Λ) (B : ℕ) (hM : ∀ l, pushes (M l)≤B)
    (a b : Configuration K Λ) (t n : ℕ)
    (run : EvalsToInTime (TM2.step M) a (some b) t) (h : Bounded a.stk n) :
    Bounded b.stk (n+t*B) := by
  intro k
  exact (iterate_bound M B hM run.steps a b run.evals_in_steps n h k).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right B run.steps_le_m) n)

end UAVProof.TreeBudgetTransitionSpace
