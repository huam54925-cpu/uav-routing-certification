import LeanCompletion.UAV.TreeBudgetFrameRoutineTM2

/-! Execution proofs for the callable parser. Bounds include every cleanup
transition and require no assumptions on the payload or suffix. -/
namespace UAVProof.TreeBudgetFrameRoutineTM2
open TreeBudgetBinaryCodec Turing StateTransition
variable {K Λ : Type} [DecidableEq K]
variable (p : Ports K) (base : K → Bits) (lab : Phase → Λ) (ok bad : Λ) (canonical : Bool)
variable (M : Λ → Statement K Λ)
variable (hM : ∀ phase, M (lab phase) = code p lab ok bad canonical phase)

def reverse_run (acc : Bits) (tmp : Option Bool) (last : Bool) (xs out : Bits) :
    EvalsToInTime (TM2.step M) (cfg p base (lab .reverse) tmp last xs acc out)
      (some (cfg p base ok none true xs [] (acc.reverse ++ out))) (acc.length + 1) := by
  induction acc generalizing tmp out with
  | nil => exact once (step_reverse_nil p base lab ok bad canonical M hM tmp last xs out)
  | cons b acc ih =>
    simpa [List.reverse_cons, List.append_assoc] using
      prepend (step_reverse_cons p base lab ok bad canonical M hM tmp last b xs acc out)
        (ih (some b) (b :: out))

def clear_run (acc : Bits) (tmp : Option Bool) (last : Bool) (xs out : Bits) :
    EvalsToInTime (TM2.step M) (cfg p base (lab .clear) tmp last xs acc out)
      (some (cfg p base bad none true xs [] out)) (acc.length + 1) := by
  induction acc generalizing tmp with
  | nil => exact once (step_clear_nil p base lab ok bad canonical M hM tmp last xs out)
  | cons b acc ih =>
    exact prepend (step_clear_cons p base lab ok bad canonical M hM tmp last b xs acc out)
      (ih (some b))

def framed_run (bs rest : Bits) (tmp : Option Bool) (last : Bool) (acc out : Bits) :
    EvalsToInTime (TM2.step M)
      (cfg p base (lab .marker) tmp last (word bs ++ rest) acc out)
      (some (if !canonical || lastDigit bs last then
        cfg p base ok none true rest [] (acc.reverse ++ bs ++ out)
      else cfg p base bad none true rest [] out)) (3 * bs.length + acc.length + 2) := by
  induction bs generalizing tmp last acc with
  | nil =>
    have hs := step_marker_end p base lab ok bad canonical M hM tmp last rest acc out
    cases canonical <;> cases last <;> simp only [Bool.not_false, Bool.not_true,
      Bool.true_or, Bool.false_or, Bool.or_false, Bool.or_true] at hs ⊢
    all_goals first
      | simpa [word, lastDigit] using prepend hs
          (reverse_run p base lab ok bad _ M hM acc (some false) _ rest out)
      | simpa [word, lastDigit] using prepend hs
          (clear_run p base lab ok bad _ M hM acc (some false) _ rest out)
  | cons b bs ih =>
    have run := prepend
      (step_marker_more p base lab ok bad canonical M hM tmp last (b :: (word bs ++ rest)) acc out)
      (prepend (step_payload_cons p base lab ok bad canonical M hM (some true) last b
        (word bs ++ rest) acc out) (ih (some b) b (b :: acc)))
    have ht : 3 * bs.length + (b :: acc).length + 2 + 1 + 1 =
        3 * (b :: bs).length + acc.length + 2 := by simp; omega
    rw [ht] at run
    simpa [word, lastDigit, List.reverse_cons, List.append_assoc] using run

def truncated_run (xs : Bits) (h : parseWord xs = none) (tmp : Option Bool)
    (last : Bool) (acc out : Bits) :
    EvalsToInTime (TM2.step M) (cfg p base (lab .marker) tmp last xs acc out)
      (some (cfg p base bad none true [] [] out)) (2 * xs.length + acc.length + 2) :=
  match xs with
  | [] => by
    simpa using prepend (step_marker_nil p base lab ok bad canonical M hM tmp last acc out)
      (clear_run p base lab ok bad canonical M hM acc none last [] out)
  | false :: xs => by simp [parseWord] at h
  | true :: [] => by
    exact weaken
      (prepend (step_marker_more p base lab ok bad canonical M hM tmp last [] acc out)
        (prepend (step_payload_nil p base lab ok bad canonical M hM (some true) last acc out)
          (clear_run p base lab ok bad canonical M hM acc none last [] out))) (by simp)
  | true :: b :: xs => by
    have ht : parseWord xs = none := by simpa [parseWord] using h
    have run := prepend (step_marker_more p base lab ok bad canonical M hM tmp last (b :: xs) acc out)
      (prepend (step_payload_cons p base lab ok bad canonical M hM (some true) last b xs acc out)
        (truncated_run xs ht (some b) b (b :: acc) out))
    exact weaken run (by simp; omega)

end UAVProof.TreeBudgetFrameRoutineTM2
