import LeanCompletion.UAV.TreeBudgetLeWordsTM2

/-! Destructive comparison of two bit stacks; every other stack is retained.
Equality compares canonical words exactly. Strict order accepts padded words too. -/
namespace UAVProof.TreeBudgetCompareRoutine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
open TreeBudgetLeWordsTM2 (leWords)

def flag (eq : Bool) (a b : Option Bool) (old : Bool) : Bool :=
  if eq then old && (a == b) else TreeBudgetLeWordsTM2.flag (a.getD false) (b.getD false) old
def words (eq : Bool) : Bits → Bits → Bool → Bool
  | [],[],old => old
  | a::xs,[],old => words eq xs [] (flag eq (some a) none old)
  | [],b::ys,old => words eq [] ys (flag eq none (some b) old)
  | a::xs,b::ys,old => words eq xs ys (flag eq (some a) (some b) old)

theorem words_lt (xs ys : Bits) (old : Bool) : words false xs ys old = leWords xs ys old := by
  induction xs generalizing ys old with
  | nil => induction ys generalizing old with
    | nil => simp [words,leWords]
    | cons b ys ih => simpa [words,leWords,flag] using ih (TreeBudgetLeWordsTM2.flag false b old)
  | cons a xs ih => cases ys <;> simp [words,leWords,flag,ih]

theorem words_eq (xs ys : Bits) (old : Bool) : words true xs ys old = (old && decide (xs=ys)) := by
  induction xs generalizing ys old with
  | nil => induction ys generalizing old with
    | nil => simp [words]
    | cons b ys ih => simp [words,flag,ih]
  | cons a xs ih =>
    cases ys with
    | nil => simp [words,flag,ih]
    | cons b ys => cases a <;> cases b <;> simp [words,flag,ih]

variable {K Λ : Type} [DecidableEq K]
def mix (eq : Bool) (s : State) (b : Option Bool) : State :=
  if s.1.isNone && b.isNone then (none,s.2) else (some false,flag eq s.1 b s.2)
def code (p : Ports K) (loop next : Λ) (eq : Bool) : Statement K Λ :=
  .pop p.src (fun s a => (a,s.2)) (.pop p.scratch (mix eq)
    (.branch (fun s => s.1.isNone) (.goto (fun _ => next)) (.goto (fun _ => loop))))

def run (p : Ports K) (base : K → Bits) (loop next : Λ) (eq : Bool)
    (M : Λ → Statement K Λ) (linked : M loop = code p loop next eq)
    (xs ys out : Bits) (tmp : Option Bool) (old : Bool) : EvalsToInTime (TM2.step M)
      (cfg p base loop tmp old xs ys out)
      (some (cfg p base next none (words eq xs ys old) [] [] out)) (xs.length+ys.length+1) := by
  induction xs generalizing ys tmp old with
  | nil =>
    induction ys generalizing tmp old with
    | nil => apply once; simp [cfg,TM2.step,linked,code,TM2.stepAux,mix,words]
    | cons b ys ih =>
      have h : TM2.step M (cfg p base loop tmp old [] (b::ys) out) =
          some (cfg p base loop (some false) (flag eq none (some b) old) [] ys out) := by
        simp [cfg,TM2.step,linked,code,TM2.stepAux,mix]
      simpa [words,Nat.add_assoc] using prepend h (ih (some false) (flag eq none (some b) old))
  | cons a xs ih =>
    cases ys with
    | nil =>
      have h : TM2.step M (cfg p base loop tmp old (a::xs) [] out) =
          some (cfg p base loop (some false) (flag eq (some a) none old) xs [] out) := by
        simp [cfg,TM2.step,linked,code,TM2.stepAux,mix]
      simpa [words,Nat.add_assoc] using prepend h (ih [] (some false) (flag eq (some a) none old))
    | cons b ys =>
      have h : TM2.step M (cfg p base loop tmp old (a::xs) (b::ys) out) =
          some (cfg p base loop (some false) (flag eq (some a) (some b) old) xs ys out) := by
        simp [cfg,TM2.step,linked,code,TM2.stepAux,mix]
      apply weaken (by simpa [words] using prepend h (ih ys (some false) (flag eq (some a) (some b) old)))
      simp; omega

end UAVProof.TreeBudgetCompareRoutine
