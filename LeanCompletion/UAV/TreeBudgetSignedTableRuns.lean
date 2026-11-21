import LeanCompletion.UAV.TreeBudgetSignedTableTM2

namespace UAVProof.TreeBudgetSignedTableTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

local macro "one_step" : tactic => `(tactic|
  (simp [machine,FinTM2.step,TM2.step,TM2.stepAux,cfg,program,jump,moved,store]
   all_goals congr 2
   all_goals funext k; fin_cases k <;> rfl))

def word_run (u s h p n po no ctx : Bits) (b : Bool) :
    Run (cfg .marker b (word u++s) h p n po no ctx)
      (cfg .sign true s ((word u).reverse++h)
        (if b then p else (word u).reverse++p)
        (if b then (word u).reverse++n else n) po no ctx)
      (2*u.length+1) := by
  induction u generalizing h p n with
  | nil => cases b <;> apply once <;> simp only [word] <;> one_step
  | cons x u ih =>
    have st1 : machine.step (cfg .marker b (word (x::u)++s) h p n po no ctx)=
        some (cfg .payload b (x::(word u++s)) (true::h)
          (if b then p else true::p) (if b then true::n else n) po no ctx) := by
      cases b <;> simp only [word] <;> one_step
    have st2 : machine.step (cfg .payload b (x::(word u++s)) (true::h)
          (if b then p else true::p) (if b then true::n else n) po no ctx)=
        some (cfg .marker b (word u++s) (x::true::h)
          (if b then p else x::true::p) (if b then x::true::n else n) po no ctx) := by
      cases b <;> one_step
    have tail := ih (x::true::h) (if b then p else x::true::p) (if b then x::true::n else n)
    have run := prepend st1 (prepend st2 tail)
    cases b <;> simpa [word,List.reverse_append,List.reverse_cons,List.append_assoc,Nat.mul_add] using run

def field_run (a : ℤ) (s h p n po no ctx : Bits) :
    Run (cfg .sign true (encodeInt a++s) h p n po no ctx)
      (cfg .sign true s ((encodeInt a).reverse++h)
        ((encodeNat (pos a)).reverse++p) ((encodeNat (neg a)).reverse++n) po no ctx)
      (encodeInt a).length := by
  have st : machine.step (cfg .sign true (encodeInt a++s) h p n po no ctx)=
      some (cfg .marker (decide (a<0)) (word a.natAbs.bits++s) ((decide (a<0))::h)
        (if decide (a<0) then false::p else p)
        (if decide (a<0) then n else false::n) po no ctx) := by
    cases ha : decide (a<0) <;> simp only [encodeInt,ha] <;> one_step
  have run := prepend st (word_run a.natAbs.bits s ((decide (a<0))::h)
    (if decide (a<0) then false::p else p) (if decide (a<0) then n else false::n) po no ctx (decide (a<0)))
  cases a with
  | ofNat a =>
    have ha : ¬ ((a:ℤ)<0) := by omega
    simpa [encodeInt,encodeNat,pos,neg,word,List.reverse_cons,List.append_assoc,ha,Nat.mul_comm] using run
  | negSucc a =>
    simpa [encodeInt,encodeNat,pos,neg,word,List.reverse_cons,List.append_assoc,Nat.mul_comm] using run

def fields_run (xs : List ℤ) (s h p n po no ctx : Bits) :
    Run (cfg .sign true (xs.flatMap encodeInt++s) h p n po no ctx)
      (cfg .sign true s ((xs.flatMap encodeInt).reverse++h)
        ((positive xs).reverse++p) ((negative xs).reverse++n) po no ctx)
      (xs.flatMap encodeInt).length := by
  induction xs generalizing h p n with
  | nil => simpa [positive,negative] using EvalsToInTime.refl machine.step (cfg .sign true s h p n po no ctx)
  | cons a xs ih =>
    have first := field_run a (xs.flatMap encodeInt++s) h p n po no ctx
    have tail := ih ((encodeInt a).reverse++h) ((encodeNat (pos a)).reverse++p) ((encodeNat (neg a)).reverse++n)
    simpa [positive,negative,List.reverse_append,List.append_assoc,List.length_append] using seq first tail

def restore_run (h s p n po no ctx : Bits) :
    Run (cfg .restore true s h p n po no ctx)
      (cfg .positive true (h.reverse++s) [] p n po no ctx) (h.length+1) := by
  induction h generalizing s with
  | nil => apply once; one_step
  | cons b h ih =>
    have st : machine.step (cfg .restore true s (b::h) p n po no ctx)=
        some (cfg .restore true (b::s) h p n po no ctx) := by one_step
    simpa [List.reverse_cons,List.append_assoc] using prepend st (ih (b::s))

def positive_run (p s n po no ctx : Bits) :
    Run (cfg .positive true s [] p n po no ctx)
      (cfg .negative true s [] [] n (p.reverse++po) no ctx) (p.length+1) := by
  induction p generalizing po with
  | nil => apply once; one_step
  | cons b p ih =>
    have st : machine.step (cfg .positive true s [] (b::p) n po no ctx)=
        some (cfg .positive true s [] p n (b::po) no ctx) := by one_step
    simpa [List.reverse_cons,List.append_assoc] using prepend st (ih (b::po))

def negative_run (n s po no ctx : Bits) :
    Run (cfg .negative true s [] [] n po no ctx)
      (cfg .done true s [] [] [] po (n.reverse++no) ctx) (n.length+1) := by
  induction n generalizing no with
  | nil => apply once; one_step
  | cons b n ih =>
    have st : machine.step (cfg .negative true s [] [] (b::n) po no ctx)=
        some (cfg .negative true s [] [] n po (b::no) ctx) := by one_step
    simpa [List.reverse_cons,List.append_assoc] using prepend st (ih (b::no))

/-- One read pass, source restoration and two output reversals. -/
def split_run (xs : List ℤ) (ctx : Bits) :
    Run (start (xs.flatMap encodeInt) ctx)
      (stopped (xs.flatMap encodeInt) (positive xs) (negative xs) ctx)
      (3*(xs.flatMap encodeInt).length+5) := by
  have a := fields_run xs [] [] [] [] [] [] ctx
  simp only [List.append_nil] at a
  have st : machine.step (cfg .sign true [] (xs.flatMap encodeInt).reverse
      (positive xs).reverse (negative xs).reverse [] [] ctx)=
      some (cfg .restore true [] (xs.flatMap encodeInt).reverse
        (positive xs).reverse (negative xs).reverse [] [] ctx) := by one_step
  have b := restore_run (xs.flatMap encodeInt).reverse [] (positive xs).reverse (negative xs).reverse [] [] ctx
  have c := positive_run (positive xs).reverse (xs.flatMap encodeInt) (negative xs).reverse [] [] ctx
  have d := negative_run (negative xs).reverse (xs.flatMap encodeInt) (positive xs) [] ctx
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at b c d
  have last : machine.step (cfg .done true (xs.flatMap encodeInt) [] [] [] (positive xs) (negative xs) ctx)=
      some (stopped (xs.flatMap encodeInt) (positive xs) (negative xs) ctx) := rfl
  have run := seq (seq (seq (seq (seq a (once st)) b) c) d) (once last)
  apply weaken run
  have h := split_lengths xs
  omega

theorem preserves (xs : List ℤ) (ctx : Bits) :
    (stopped (xs.flatMap encodeInt) (positive xs) (negative xs) ctx).stk 0=xs.flatMap encodeInt ∧
    (stopped (xs.flatMap encodeInt) (positive xs) (negative xs) ctx).stk 6=ctx := ⟨rfl,rfl⟩

end UAVProof.TreeBudgetSignedTableTM2
