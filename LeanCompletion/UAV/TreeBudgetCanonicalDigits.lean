import LeanCompletion.UAV.TreeBudgetFrameRoutineTM2

/-! A finite-state canonicality test for the existing little-endian Nat codec.
Empty payload is zero; a nonempty payload must end in true. -/
namespace UAVProof.TreeBudgetCanonicalDigits
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2

theorem lastDigit_seed (xs : Bits) (a b : Bool) (h : xs ≠ []) :
    lastDigit xs a = lastDigit xs b := by cases xs <;> simp_all [lastDigit]

theorem lastDigit_bits (n : ℕ) : lastDigit n.bits true = true := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    change lastDigit n.bits b = true
    by_cases hz : n = 0
    · subst n; simpa [lastDigit] using hn rfl
    · have hne : n.bits ≠ [] := by
        intro he
        have hv := value_bits n
        rw [he] at hv
        exact hz hv.symm
      rw [lastDigit_seed n.bits b true hne]
      exact ih

theorem canonical_of_last (xs : Bits) (h : lastDigit xs true = true) :
    (value xs).bits = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases xs with
    | nil =>
      have hb : b = true := h
      subst b
      rfl
    | cons c cs =>
      have ht : lastDigit (c :: cs) true = true := by simpa [lastDigit] using h
      have hc := ih ht
      have hn : value (c :: cs) ≠ 0 := by
        intro hz
        rw [hz, Nat.zero_bits] at hc
        contradiction
      change (Nat.bit b (value (c :: cs))).bits = _
      rw [Nat.bits_append_bit _ b (fun hz => False.elim (hn hz)), hc]

theorem canonical_iff_last (xs : Bits) :
    (value xs).bits = xs ↔ lastDigit xs true = true := by
  constructor
  · intro h; rw [← h]; exact lastDigit_bits _
  · exact canonical_of_last xs

theorem parseNat_framed (xs rest : Bits) :
    parseNat (word xs ++ rest) =
      if lastDigit xs true then some (value xs, rest) else none := by
  simp [parseNat, parseWord_append, canonical_iff_last]

theorem parseNat_truncated (xs : Bits) (h : parseWord xs = none) :
    parseNat xs = none := by simp [parseNat, h]

end UAVProof.TreeBudgetCanonicalDigits
