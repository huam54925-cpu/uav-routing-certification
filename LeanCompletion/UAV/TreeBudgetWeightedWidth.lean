import LeanCompletion.UAV.TreeBudgetWeightedRuns

namespace UAVProof.TreeBudgetWeightedTM2
open TreeBudgetBinaryCodec

/-- Actual stored width, including high zero padding, for every starting accumulator. -/
theorem weighted_length (u h a : Bits) :
    (weighted u h a).length ≤ u.length + max h.length a.length := by
  induction u generalizing h a with
  | nil => simp [weighted]
  | cons b u ih =>
    have hw := add_width h a false
    cases b <;> simp only [weighted,Bool.false_eq_true,ite_false,ite_true,List.length_cons]
    · have ht := ih (false::h) a
      simp only [List.length_cons] at ht
      omega
    · have ht := ih (false::h) (TreeBudgetAddWordsTM2.addWords h a false)
      simp only [List.length_cons] at ht
      omega

theorem product_length (u h : Bits) : (weighted u h []).length ≤ u.length+h.length := by
  simpa using weighted_length u h []

end UAVProof.TreeBudgetWeightedTM2
