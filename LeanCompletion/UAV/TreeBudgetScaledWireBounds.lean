import LeanCompletion.UAV.TreeBudgetRowCheckBounds
import LeanCompletion.UAV.TreeBudgetSignedTableTM2

namespace UAVProof.A4ScaledWireBounds
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetSparseVerifier TreeBudgetVectorChecker
open A4RowCheckSpec

theorem dimension_length (x : Bits) (I : Instance) (hi : parseInstance x=some I) :
    I.data.n≤x.length := by
  obtain ⟨raw,hx,hs,hd⟩ := parseInstance_canonical x I hi
  have hn : I.data.n≤(encodeInput raw).length :=
    (decodeRaw_fields raw I.data hd).1.trans_le (vertexCount_le_length raw hs)
  simp only [hx,encodeSpecified,List.length_append]
  omega

theorem fees_wire_length (x : Bits) (I : Instance) (hi : parseInstance x=some I) :
    ((scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator).toList.flatMap encodeInt).length
      ≤4*(x.length+1)^2 := by
  let A := scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator
  have hwidth := (scaled_width x I hi).1
  have h := encoded_ints_length A.toList (2*x.length+1) (by
    intro a ha
    obtain ⟨v,hv,he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp ha)
    rw [← he]
    exact hwidth ⟨v,hv⟩)
  have hn := dimension_length x I hi
  simp only [Vector.length_toList] at h
  change (A.toList.flatMap encodeInt).length≤_
  nlinarith

theorem split_fees_wire_length (x : Bits) (I : Instance) (hi : parseInstance x=some I) :
    (TreeBudgetSignedTableTM2.positive
      (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator).toList).length+
    (TreeBudgetSignedTableTM2.negative
      (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator).toList).length
      ≤4*(x.length+1)^2 := by
  rw [TreeBudgetSignedTableTM2.split_lengths]
  exact fees_wire_length x I hi

theorem budget_wire_length (x : Bits) (I : Instance) (hi : parseInstance x=some I) :
    (encodeInt (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator)).length
      ≤4*x.length+4 := by
  have h := (scaled_width x I hi).2
  simp only [Nat.size_eq_bits_len] at h
  simp only [encodeInt_length]
  omega

theorem split_budget_width (x : Bits) (I : Instance) (hi : parseInstance x=some I) :
    (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator).toNat.bits.length+
    (-(scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator)).toNat.bits.length
      ≤2*x.length+1 := by
  have h := (scaled_width x I hi).2
  generalize scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator=b at *
  cases b <;> simpa using h

end UAVProof.A4ScaledWireBounds
