import LeanCompletion.UAV.TreeBudgetWeightedTM2

namespace UAVProof.TreeBudgetWeightedTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
open TreeBudgetAddWordsTM2 (addWords digit carry addWords_value)
abbrev Run (a b : Cfg) (n : ℕ) := EvalsToInTime machine.step a (some b) n

def restore_run (cp h x buf ctx : Bits) : Run (cfg 2 false x h [] cp buf ctx)
    (cfg 3 false x (false :: (cp.reverse ++ h)) [] [] buf ctx) (cp.length+1) := by
  induction cp generalizing h with
  | nil => exact once (restore_end x h buf ctx)
  | cons b cp ih =>
    simpa [List.reverse_cons,List.append_assoc] using
      prepend (restore_one b x h cp buf ctx) (ih (b :: h))

def sum_run (buf a x h ctx : Bits) : Run (cfg 3 false x h a [] buf ctx)
    (cfg 0 false x h (buf.reverse ++ a) [] [] ctx) (buf.length+1) := by
  induction buf generalizing a with
  | nil => exact once (sum_end x h a ctx)
  | cons b buf ih =>
    simpa [List.reverse_cons,List.append_assoc] using
      prepend (sum_one b x h a buf ctx) (ih (b :: a))

def clear_run (h a ctx : Bits) : Run (cfg 4 false [] h a [] [] ctx)
    (cfg 5 false [] [] a [] [] ctx) (h.length+1) := by
  induction h with
  | nil => exact once (clear_end a ctx)
  | cons b h ih => exact prepend (clear_one b h a ctx) ih

def digits_run (h a x cp buf ctx : Bits) (c : Bool) :
    Run (cfg 1 c x h a cp buf ctx)
      (cfg 2 false x [] [] (h.reverse ++ cp) ((addWords h a c).reverse ++ buf) ctx)
      (h.length+a.length+1) := by
  induction h generalizing a cp buf c with
  | nil =>
    induction a generalizing buf c with
    | nil => cases c <;> simpa [addWords] using once (add_end _ x cp buf ctx)
    | cons d a ih =>
      simpa [addWords,List.reverse_cons,List.append_assoc] using
        prepend (add_right d c x a cp buf ctx) (ih (digit false d c :: buf) (carry false d c))
  | cons b h ih =>
    cases a with
    | nil =>
      simpa [addWords,List.reverse_cons,List.append_assoc] using prepend (add_left b c x h cp buf ctx)
        (ih [] (b :: cp) (digit b false c :: buf) (carry b false c))
    | cons d a =>
      have run := prepend (add_both b d c x h a cp buf ctx)
        (ih a (b :: cp) (digit b d c :: buf) (carry b d c))
      apply weaken (by simpa [addWords,List.reverse_cons,List.append_assoc] using run)
      simp; omega

theorem add_width (h a : Bits) (c : Bool) :
    (addWords h a c).length ≤ max h.length a.length + 1 := by
  induction h generalizing a c with
  | nil =>
    induction a generalizing c with
    | nil => cases c <;> simp [addWords]
    | cons d a ih => simpa [addWords] using ih (carry false d c)
  | cons b h ih =>
    cases a with
    | nil => simpa [addWords] using ih [] (carry b false c)
    | cons d a =>
      have ht := ih a (carry b d c)
      simp only [addWords, List.length_cons]; omega

def add_pass (x h a ctx : Bits) : Run (cfg 1 false x h a [] [] ctx)
    (cfg 0 false x (false :: h) (addWords h a false) [] [] ctx) (4*(h.length+a.length+1)+2) := by
  have d := digits_run h a x [] [] ctx false
  simp only [List.append_nil] at d
  have r := restore_run h.reverse [] x (addWords h a false).reverse ctx
  simp only [List.reverse_reverse, List.append_nil] at r
  have s := sum_run (addWords h a false).reverse [] x (false :: h) ctx
  simp only [List.reverse_reverse, List.append_nil] at s
  have run := EvalsToInTime.trans machine.step _ _ _ _ _ (EvalsToInTime.trans machine.step _ _ _ _ _ d r) s
  exact weaken run (by simp; have hw := add_width h a false; omega)

def weighted : Bits → Bits → Bits → Bits
  | [], _, a => a
  | b :: x, h, a => weighted x (false :: h) (if b then addWords h a false else a)

theorem weighted_value (x h a : Bits) : value (weighted x h a) = value a + value x * value h := by
  induction x generalizing h a with
  | nil => simp [weighted,value]
  | cons b x ih =>
    cases b <;> simp [weighted, ih, addWords_value, value, Nat.bit] <;> ring

/-- B bounds both live operand widths. A shift and an add increase their
maximum by at most one. B + remaining multiplier length does not increase. -/
def weighted_run (x h a ctx : Bits) (B : ℕ) (hh : h.length ≤ B) (ha : a.length ≤ B) :
    Run (cfg 0 false x h a [] [] ctx) (cfg 5 false [] [] (weighted x h a) [] [] ctx)
      ((x.length+1)*(8*(B+x.length+1)+8)) := by
  induction x generalizing B h a with
  | nil =>
    exact weaken (prepend (outer_nil h a ctx) (clear_run h a ctx)) (by simp; omega)
  | cons b x ih =>
    have hh' : (false :: h).length ≤ B+1 := by simp [hh]
    cases b with
    | false =>
      have run := prepend (outer_false x h a ctx) (ih (false :: h) a (B+1) hh' (by omega))
      apply weaken run
      simp only [List.length_cons]; nlinarith
    | true =>
      have hw := add_width h a false
      have tail := ih (false :: h) (addWords h a false) (B+1) hh' (by omega)
      have run := prepend (outer_true x h a ctx)
        (EvalsToInTime.trans machine.step _ _ _ _ _ (add_pass x h a ctx) tail)
      apply weaken run
      simp only [List.length_cons]; nlinarith

theorem weighted_refines_executor (x h a : Bits) : value (weighted x h a) =
    (TreeBudgetBitPrimitives.addNatD (value a)
      (TreeBudgetBitPrimitives.mulNatD (value x) (value h)).value).value := by
  simp [weighted_value]

def update_run (x h a ctx : Bits) : Run (cfg 0 false x h a [] [] ctx)
    (cfg 5 false [] [] (weighted x h a) [] [] ctx)
    (16*(x.length+h.length+a.length+1)^2) := by
  have run := weighted_run x h a ctx (h.length+a.length) (by omega) (by omega)
  apply weaken run
  nlinarith [Nat.zero_le (h.length^2), Nat.zero_le (a.length^2)]

def stopped (out ctx : Bits) : Cfg := { cfg 5 false [] [] out [] [] ctx with l := none }

def update_halts (x h a ctx : Bits) : Run (cfg 0 false x h a [] [] ctx)
    (stopped (weighted x h a) ctx) (16*(x.length+h.length+a.length+1)^2 + 1) := by
  have last : machine.step (cfg 5 false [] [] (weighted x h a) [] [] ctx) =
      some (stopped (weighted x h a) ctx) := rfl
  have run := EvalsToInTime.trans machine.step _ _ _ _ _ (update_run x h a ctx) (once last)
  convert run using 1; omega

theorem product_refines (x h : Bits) : value (weighted x h []) =
    (TreeBudgetBitPrimitives.mulNatD (value x) (value h)).value := by simp [weighted_value, value]

def product_run (x h ctx : Bits) : Run (cfg 0 false x h [] [] [] ctx)
    (stopped (weighted x h []) ctx) (16*(x.length+h.length+1)^2+1) := by
  simpa using update_halts x h [] ctx

theorem stopped_terminal (out ctx : Bits) : machine.step (stopped out ctx) = none := rfl

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end UAVProof.TreeBudgetWeightedTM2
