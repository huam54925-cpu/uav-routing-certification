import LeanCompletion.UAV.TreeBudgetTM2Call

/-! Physical stack operations used by the tree-validation caller. All loops
inspect a stack symbol. Binary increment never unfolds the value of a word;
the counter routine obtains one token per actual framed field. -/
namespace UAVProof.TreeBudgetStackRoutine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
open Turing.TM2.Stmt

inductive Phase | reverse | emit | carry | back | count | clear
  deriving DecidableEq, Fintype

variable {K Λ : Type} [DecidableEq K]

def jump (l : Λ) : Statement K Λ := load (fun _ => (none,true)) (goto fun _ => l)
def put (k : K) (q : Statement K Λ) := push k (fun s => s.1.getD false) q
def scan (k : K) (empty more : Statement K Λ) :=
  pop k (fun _ b => (b,true)) (branch (fun s => s.1.isNone) empty more)

def code (p : Ports K) (lab : Phase → Λ) (next : Λ) (framed : Bool) :
    Phase → Statement K Λ
  | .reverse => scan p.src
      (if framed then push p.dst (fun _ => false) (jump (lab .emit)) else jump (lab .emit))
      (put p.scratch (jump (lab .reverse)))
  | .emit => scan p.scratch (jump next)
      (put p.src (put p.dst
        (if framed then push p.dst (fun _ => true) (jump (lab .emit)) else jump (lab .emit))))
  | .carry => scan p.src
      (push p.src (fun _ => true) (jump (lab .back)))
      (branch (fun s => s.1.getD false)
        (push p.scratch (fun _ => false) (jump (lab .carry)))
        (push p.src (fun _ => true) (jump (lab .back))))
  | .back => scan p.scratch (jump next) (put p.src (jump (lab .back)))
  | .count => scan p.src (jump (lab .back))
      (put p.scratch (branch (fun s => s.1.getD false)
        (pop p.src (fun _ b => (b,true)) (put p.scratch (jump (lab .count))))
        (push p.dst (fun _ => true) (jump (lab .count)))))
  | .clear => scan p.src (jump next) (jump (lab .clear))

def conf (p : Ports K) (base : K → Bits) (l : Λ) (s t d : Bits) : Configuration K Λ :=
  ⟨some l,(none,true),tapes p base s t d⟩

def payload (framed : Bool) (s : Bits) :=
  if framed then s.flatMap (fun b => [true,b]) else s

section Runs
variable (p : Ports K) (base : K → Bits) (lab : Phase → Λ) (next : Λ) (framed : Bool)
variable (M : Λ → Statement K Λ)
variable (linked : ∀ phase, M (lab phase) = code p lab next framed phase)
include linked

local macro "step" : tactic => `(tactic|
  simp_all [conf,TM2.step,code,TM2.stepAux,scan,put,jump])

def reverse_run (s t d : Bits) :
    EvalsToInTime (TM2.step M) (conf p base (lab .reverse) s t d)
      (some (conf p base (lab .emit) [] (s.reverse ++ t)
        (if framed then false::d else d))) (s.length+1) := by
  induction s generalizing t with
  | nil => apply once; cases framed <;> step
  | cons b s ih =>
    have h : TM2.step M (conf p base (lab .reverse) (b::s) t d) =
        some (conf p base (lab .reverse) s (b::t) d) := by step
    simpa [List.reverse_cons,List.append_assoc] using prepend h (ih (b::t))

def emit_run (t s d : Bits) :
    EvalsToInTime (TM2.step M) (conf p base (lab .emit) s t d)
      (some (conf p base next (t.reverse ++ s) [] (payload framed t.reverse ++ d)))
      (t.length+1) := by
  induction t generalizing s d with
  | nil => apply once; cases framed <;> step <;> simp [payload]
  | cons b t ih =>
    cases framed with
    | false =>
      have h : TM2.step M (conf p base (lab .emit) s (b::t) d) =
          some (conf p base (lab .emit) (b::s) t (b::d)) := by step
      simpa [payload,List.reverse_cons,List.append_assoc] using prepend h (ih (b::s) (b::d))
    | true =>
      have h : TM2.step M (conf p base (lab .emit) s (b::t) d) =
          some (conf p base (lab .emit) (b::s) t (true::b::d)) := by step
      simpa [payload,List.reverse_cons,List.append_assoc] using prepend h (ih (b::s) (true::b::d))

/-- Preserve the source, clear the scratch stack, and prepend a physical copy
or a freshly framed copy to the destination. -/
def copy_run (s d : Bits) :
    EvalsToInTime (TM2.step M) (conf p base (lab .reverse) s [] d)
      (some (conf p base next s [] ((if framed then word s else s) ++ d)))
      (2*s.length+2) := by
  have a := reverse_run p base lab next framed M linked s [] d
  have b := emit_run p base lab next framed M linked s.reverse [] (if framed then false::d else d)
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at a b
  have h := EvalsToInTime.trans (TM2.step M) _ _ _ _ _ a b
  cases framed <;> simpa [payload,word,List.append_assoc,show s.length+1+(s.length+1)=2*s.length+2 by omega] using h

def back_run (t s d : Bits) :
    EvalsToInTime (TM2.step M) (conf p base (lab .back) s t d)
      (some (conf p base next (t.reverse ++ s) [] d)) (t.length+1) := by
  induction t generalizing s with
  | nil => apply once; step
  | cons b t ih =>
    have h : TM2.step M (conf p base (lab .back) s (b::t) d) =
        some (conf p base (lab .back) (b::s) t d) := by step
    simpa [List.reverse_cons,List.append_assoc] using prepend h (ih (b::s))

end Runs

def increment : Bits → Bits
  | [] => [true]
  | false::s => true::s
  | true::s => false::increment s

theorem increment_bits (i : ℕ) : increment i.bits = (i+1).bits := by
  induction i using Nat.binaryRec' with
  | zero => simp [increment]
  | bit b i hi ih =>
    rw [Nat.bits_append_bit i b hi]
    cases b with
    | false => simp [Nat.bit,increment]
    | true =>
      simp only [increment,ih]
      rw [show Nat.bit true i+1 = 2*(i+1) by simp [Nat.bit]; omega,
        Nat.bit0_bits (i+1) (by omega)]

section MoreRuns
variable (p : Ports K) (base : K → Bits) (lab : Phase → Λ) (next : Λ) (framed : Bool)
variable (M : Λ → Statement K Λ)
variable (linked : ∀ phase, M (lab phase) = code p lab next framed phase)
include linked

local macro "step" : tactic => `(tactic|
  simp_all [conf,TM2.step,code,TM2.stepAux,scan,put,jump])

def increment_run (s t d : Bits) :
    EvalsToInTime (TM2.step M) (conf p base (lab .carry) s t d)
      (some (conf p base next (t.reverse ++ increment s) [] d))
      (2*s.length+t.length+2) := by
  induction s generalizing t with
  | nil =>
    apply weaken (prepend (b := conf p base (lab .back) [true] t d) ?_
      (back_run p base lab next framed M linked t [true] d)) (by simp)
    step
  | cons b s ih =>
    cases b with
    | false =>
      apply weaken (prepend (b := conf p base (lab .back) (true::s) t d) ?_
        (back_run p base lab next framed M linked t (true::s) d)) (by simp)
      step
    | true =>
      have h : TM2.step M (conf p base (lab .carry) (true::s) t d) =
          some (conf p base (lab .carry) s (false::t) d) := by step
      convert prepend h (ih (false::t)) using 1
      · simp [increment,List.reverse_cons,List.append_assoc]
      · simp only [List.length_cons]; omega

def clear_run (s t d : Bits) :
    EvalsToInTime (TM2.step M) (conf p base (lab .clear) s t d)
      (some (conf p base next [] t d)) (s.length+1) := by
  induction s with
  | nil => apply once; step
  | cons b s ih =>
    apply prepend (b := conf p base (lab .clear) s t d) ?_ ih
    step

def count_field (s tail t d : Bits) :
    EvalsToInTime (TM2.step M) (conf p base (lab .count) (word s ++ tail) t d)
      (some (conf p base (lab .count) tail ((word s).reverse ++ t) (true::d)))
      (s.length+1) := by
  induction s generalizing t with
  | nil => apply once; simp [word]; step
  | cons b s ih =>
    have h : TM2.step M (conf p base (lab .count) (word (b::s) ++ tail) t d) =
        some (conf p base (lab .count) (word s ++ tail) (b::true::t) d) := by
      simp [word,List.append_assoc]; step
    simpa [word,List.reverse_append,List.append_assoc] using prepend h (ih (b::true::t))

def count_fields (xs : List ℕ) (t d : Bits) :
    EvalsToInTime (TM2.step M)
      (conf p base (lab .count) (xs.flatMap encodeNat) t d)
      (some (conf p base (lab .back) [] ((xs.flatMap encodeNat).reverse ++ t)
        (List.replicate xs.length true ++ d))) ((xs.flatMap encodeNat).length+1) := by
  induction xs generalizing t d with
  | nil => apply once; step
  | cons x xs ih =>
    have a := count_field p base lab next framed M linked x.bits (xs.flatMap encodeNat) t d
    have b := ih ((encodeNat x).reverse ++ t) (true::d)
    have ht : List.replicate xs.length true ++ true::d = List.replicate (xs.length+1) true ++ d := by
      rw [List.replicate_succ',List.append_assoc]; rfl
    rw [ht] at b
    apply weaken (by simpa only [encodeNat,List.flatMap_cons,List.reverse_append,List.append_assoc,
      List.length_cons] using
      EvalsToInTime.trans (TM2.step M) _ _ _ _ _ a b) ?_
    simp [encodeNat,word_length]; omega

/-- Derive the unary loop budget from the materialized table, retaining every
table bit. No binary count header is expanded. -/
def count_run (xs : List ℕ) (d : Bits) :
    EvalsToInTime (TM2.step M)
      (conf p base (lab .count) (xs.flatMap encodeNat) [] d)
      (some (conf p base next (xs.flatMap encodeNat) [] (List.replicate xs.length true ++ d)))
      (2*(xs.flatMap encodeNat).length+2) := by
  have a := count_fields p base lab next framed M linked xs [] d
  have b := back_run p base lab next framed M linked (xs.flatMap encodeNat).reverse []
    (List.replicate xs.length true ++ d)
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at a b
  exact weaken (EvalsToInTime.trans (TM2.step M) _ _ _ _ _ a b) (by omega)

end MoreRuns
end UAVProof.TreeBudgetStackRoutine
