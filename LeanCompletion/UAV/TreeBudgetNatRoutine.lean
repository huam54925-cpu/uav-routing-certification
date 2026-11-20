import LeanCompletion.UAV.TreeBudgetEntryTM2

/-! A canonical natural-number reader with caller-selected physical stacks.
The bound depends on input bits, including on rejected inputs. -/
namespace UAVProof.TreeBudgetNatRoutine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetCanonicalDigits Turing StateTransition

variable {K Λ : Type} [DecidableEq K]

def finish (p : Ports K) (base : K → Bits) (ok bad : Λ) (s out : Bits) : Configuration K Λ :=
  match parseNat s with
  | none => cfg p base bad none true (TreeBudgetNatListLoop.suffix s) [] out
  | some (n,r) => cfg p base ok none true r [] (n.bits ++ out)

def run (p : Ports K) (base : K → Bits) (lab : Phase → Λ) (ok bad : Λ)
    (M : Λ → Statement K Λ) (linked : ∀ q, M (lab q) = code p lab ok bad true q)
    (s out : Bits) : EvalsToInTime (TM2.step M)
      (cfg p base (lab .marker) none true s [] out) (some (finish p base ok bad s out))
      (2*s.length+2) := by
  cases hw : parseWord s with
  | none =>
    have h := truncated_run p base lab ok bad true M linked s hw none true [] out
    simpa [finish,parseNat_truncated s hw,TreeBudgetNatListLoop.suffix,hw] using h
  | some pair =>
    obtain ⟨bs,r⟩ := pair
    have he := parseWord_consumed s bs r hw
    subst s
    have h := framed_run p base lab ok bad true M linked bs r none true [] out
    have hb : 3*bs.length+2 ≤ 2*(word bs ++ r).length+2 := by simp [word_length]; omega
    cases hc : lastDigit bs true with
    | false => simpa [finish,parseNat_framed,hc,TreeBudgetNatListLoop.suffix,
        parseWord_append] using weaken h hb
    | true => simpa [finish,parseNat_framed,hc,canonical_of_last bs hc] using weaken h hb

end UAVProof.TreeBudgetNatRoutine
