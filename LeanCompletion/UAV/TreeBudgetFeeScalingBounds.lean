import LeanCompletion.UAV.TreeBudgetFeeScalingSpec

namespace UAVProof.A4FeeScaling
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetSparseVerifier

theorem mass_split (es : List Row) :
    mass es=((es.map Prod.fst).map (fun a => a.natAbs.bits.length)).sum+
      ((es.map Prod.snd).map (fun b => b.bits.length)).sum := by
  induction es <;> simp_all [mass] <;> omega

theorem history_length (p : Bits) (es : List Row) : (history p es).length=es.length := by
  induction es generalizing p <;> simp_all [history]

/-- Width and copying budgets occupy positions of the instance itself. -/
theorem instance_bounds (x : Bits) (I : Instance) (hi : parseInstance x=some I) :
    let es := rows I.data.numerators I.data.denominators
    es.length ≤ x.length ∧
    mass es+I.data.budgetNumerator.natAbs.bits.length+I.data.budgetDenominator.bits.length ≤ x.length ∧
    (I.data.numerators.toList.flatMap encodeInt).length ≤ x.length ∧
    (I.data.denominators.toList.flatMap encodeNat).length ≤ x.length ∧
    (encodeInt I.data.budgetNumerator).length ≤ x.length ∧
    (encodeNat I.data.budgetDenominator).length ≤ x.length := by
  obtain ⟨raw,hx,shape,hd⟩ := parseInstance_canonical x I hi
  obtain ⟨hn,_,_,ha,hb,hat,hbt⟩ := decodeRaw_fields raw I.data hd
  have hw := inputWeight_le_length raw
  have hv := vertexCount_le_length raw shape
  have hl : (encodeInput raw).length ≤ x.length := by
    simp only [hx,encodeSpecified,List.length_append]; omega
  have hm : mass (rows I.data.numerators I.data.denominators)=
      (raw.numerators.map (fun a => a.natAbs.size)).sum+
        (raw.denominators.map Nat.size).sum := by
    simp only [mass_split,rows_fst,rows_snd,ha,hb,Nat.size_eq_bits_len]
  have hs : (raw.numerators.flatMap encodeInt).length ≤ x.length ∧
      (raw.denominators.flatMap encodeNat).length ≤ x.length ∧
      (encodeInt raw.budgetNumerator).length ≤ x.length ∧
      (encodeNat raw.budgetDenominator).length ≤ x.length := by
    simp only [hx,encodeSpecified,encodeInput,encodeInts,encodeNats,encodeList,List.length_append]
    omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [rows,hn] using hv.trans hl
  · rw [hm,hat,hbt,Nat.size_eq_bits_len,Nat.size_eq_bits_len]
    unfold inputWeight at hw
    omega
  · simpa [ha] using hs.1
  · simpa [hb] using hs.2.1
  · simpa [hat] using hs.2.2.1
  · simpa [hbt] using hs.2.2.2

/-- Saved fee fields describe the same typed instance returned by parseInstance. -/
theorem parsed_fee_fields (x : Bits) (I : Instance) (hi : parseInstance x=some I)
    (a : TreeBudgetRootFlowSpec.Raw) (f : A4FeeTailSpec.Fields)
    (ha : TreeBudgetRootFlowSpec.parse x=some a)
    (hr : TreeBudgetRootFlowSpec.accepted x=true)
    (hf : A4FeeTailSpec.read a.vertices a.rest=some f) :
    f.nums=I.data.numerators.toList ∧ f.dens=I.data.denominators.toList ∧
      f.budgetNum=I.data.budgetNumerator ∧ f.budgetDen=I.data.budgetDenominator := by
  obtain ⟨hn,hH,_⟩ := A4FeeTailSpec.root_contract x a ha hr
  have hd := A4FeeTailSpec.parseInstance_finish x a f ha hf hn hH
  rw [hi] at hd
  have raw := (decodeSpecified_fields _ _ I hd.symm).2
  have fields := decodeRaw_fields _ _ raw
  exact ⟨fields.2.2.2.1.symm,fields.2.2.2.2.1.symm,
    fields.2.2.2.2.2.1.symm,fields.2.2.2.2.2.2.symm⟩

end UAVProof.A4FeeScaling
