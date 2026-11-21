import LeanCompletion.UAV.TreeBudgetCanonicalDigits
import LeanCompletion.UAV.TreeBudgetFrameRunsTM2

/-! Consume an arbitrary padded magnitude and prepend its canonical signed
encoding. The sign lives in the finite control; zero is always nonnegative. -/
namespace UAVProof.TreeBudgetSignedWordTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetCanonicalDigits
open Turing StateTransition Turing.TM2.Stmt

def signed (neg : Bool) (n : ℕ) : ℤ := if neg then -(n:ℤ) else (n:ℤ)

theorem signed_mul (a : ℤ) (k : ℕ) : signed (decide (a<0)) (a.natAbs*k)=a*(k:ℤ) := by
  cases a with
  | ofNat n => simp [signed]
  | negSucc n =>
    simp [signed]
    rw [Int.negSucc_eq]
    ring

theorem signed_zero (neg : Bool) : signed neg 0=0 := by cases neg <;> rfl

theorem signed_encoding (neg : Bool) (n : ℕ) (hn : n≠0) :
    encodeInt (signed neg n)=neg::encodeNat n := by
  have hp : 0<n := by omega
  cases neg <;> simp [signed,encodeInt,hp]

theorem value_append_zero (s : Bits) : value (s++[false])=value s := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [value,ih]

theorem last_true (s : Bits) (b : Bool) : lastDigit (s++[true]) b=true := by
  induction s generalizing b with
  | nil => rfl
  | cons a s ih => exact ih a

theorem high_true_encoding (neg : Bool) (s : Bits) :
    encodeInt (signed neg (value (s.reverse++[true])))=neg::word (s.reverse++[true]) := by
  have hc := canonical_of_last (s.reverse++[true]) (last_true _ _)
  have hn : value (s.reverse++[true])≠0 := by
    intro h
    simp [h] at hc
  rw [signed_encoding neg _ hn,encodeNat,hc]

inductive Phase | reverse | trim | emit deriving DecidableEq, Fintype

variable {K Λ : Type} [DecidableEq K]

def jump (l : Λ) : Statement K Λ := load (fun _ => (none,true)) (goto fun _ => l)

def code (p : Ports K) (lab : Phase → Λ) (next : Λ) : Phase → Statement K Λ
  | .reverse => pop p.src (fun s b => (b,s.2))
      (branch (fun s => s.1.isNone) (goto fun _ => lab .trim)
        (push p.scratch (fun s => s.1.getD false) (goto fun _ => lab .reverse)))
  | .trim => pop p.scratch (fun s b => (b,s.2))
      (branch (fun s => s.1.isNone)
        (push p.dst (fun _ => false) (push p.dst (fun _ => false) (jump next)))
        (branch (fun s => s.1.getD false)
          (push p.dst (fun _ => false) (push p.dst (fun _ => true)
            (push p.dst (fun _ => true) (goto fun _ => lab .emit))))
          (goto fun _ => lab .trim)))
  | .emit => pop p.scratch (fun s b => (b,s.2))
      (branch (fun s => s.1.isNone) (push p.dst Prod.snd (jump next))
        (push p.dst (fun s => s.1.getD false)
          (push p.dst (fun _ => true) (goto fun _ => lab .emit))))

section Runs
variable (p : Ports K) (base : K → Bits) (lab : Phase → Λ) (next : Λ)
variable (M : Λ → Statement K Λ) (linked : ∀ ph, M (lab ph)=code p lab next ph)
include linked

local macro "step" : tactic => `(tactic|
  simp [TM2.step,cfg,linked,code,TM2.stepAux,jump])

def reverse_run (s t out : Bits) (neg : Bool) (tmp : Option Bool) :
    EvalsToInTime (TM2.step M) (cfg p base (lab .reverse) tmp neg s t out)
      (some (cfg p base (lab .trim) none neg [] (s.reverse++t) out)) (s.length+1) := by
  induction s generalizing t tmp with
  | nil => apply once; step
  | cons b s ih =>
    have h : TM2.step M (cfg p base (lab .reverse) tmp neg (b::s) t out)=
        some (cfg p base (lab .reverse) (some b) neg s (b::t) out) := by step
    simpa [List.reverse_cons,List.append_assoc] using prepend h (ih (b::t) (some b))

def emit_run (t s out : Bits) (neg : Bool) (tmp : Option Bool) :
    EvalsToInTime (TM2.step M) (cfg p base (lab .emit) tmp neg [] t (word s++out))
      (some (cfg p base next none true [] [] (neg::(word (t.reverse++s)++out))))
      (t.length+1) := by
  induction t generalizing s tmp with
  | nil => apply once; simp only [List.reverse_nil,List.nil_append]; step
  | cons b t ih =>
    have h : TM2.step M (cfg p base (lab .emit) tmp neg [] (b::t) (word s++out))=
        some (cfg p base (lab .emit) (some b) neg [] t (word (b::s)++out)) := by
      simp only [word]; step
    simpa [List.reverse_cons,List.append_assoc] using prepend h (ih (b::s) (some b))

def trim_run (t out : Bits) (neg : Bool) (tmp : Option Bool) :
    EvalsToInTime (TM2.step M) (cfg p base (lab .trim) tmp neg [] t out)
      (some (cfg p base next none true [] []
        (encodeInt (signed neg (value t.reverse))++out))) (t.length+1) := by
  induction t generalizing tmp with
  | nil => apply once; simp [signed_zero,encodeInt,encodeNat,word,value]; step
  | cons b t ih =>
    cases b with
    | false =>
      have h : TM2.step M (cfg p base (lab .trim) tmp neg [] (false::t) out)=
          some (cfg p base (lab .trim) (some false) neg [] t out) := by step
      simpa [List.reverse_cons,value_append_zero] using prepend h (ih (some false))
    | true =>
      have h : TM2.step M (cfg p base (lab .trim) tmp neg [] (true::t) out)=
          some (cfg p base (lab .emit) (some true) neg [] t (word [true]++out)) := by
        simp only [word]; step
      simpa [List.reverse_cons,high_true_encoding] using
        prepend h (emit_run p base lab next M linked t [true] out neg (some true))

def write_run (s out : Bits) (neg : Bool) :
    EvalsToInTime (TM2.step M) (cfg p base (lab .reverse) none neg s [] out)
      (some (cfg p base next none true [] [] (encodeInt (signed neg (value s))++out)))
      (2*s.length+2) := by
  have a := reverse_run p base lab next M linked s [] out neg none
  have b := trim_run p base lab next M linked s.reverse out neg none
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at a b
  exact weaken (EvalsToInTime.trans _ _ _ _ _ _ a b) (by omega)

end Runs
end UAVProof.TreeBudgetSignedWordTM2
