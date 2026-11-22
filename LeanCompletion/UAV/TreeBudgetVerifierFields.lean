import LeanCompletion.UAV.TreeBudgetVerifierSetup

namespace UAVProof.A4Verifier
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetSparseCodec
open TreeBudgetSparseVerifier TreeBudgetSparseNPBridge TreeBudgetCertificate
open TreeBudgetVectorChecker

/-- The physical parser stacks match the typed instance and certificate.
No part of preparation needs to reconstruct an input from the Lean model. -/
structure SavedFields (s : A4FeeScaling.K → Bits) (I : Instance)
    (C : Certificate (Fin I.data.n)) : Prop where
  parents : s pSource=(I.data.parents.parents.toList.map Fin.val).flatMap encodeNat
  demands : s hSource=I.data.H.toList.flatMap encodeNat
  root : s rSource=I.data.parents.root.val.bits
  routes : s mSource=I.routes.bits
  body : s bodySource=(toRaw C).flatMap encodeEntry
  marks : s marksSource=List.replicate C.size true

theorem saved_fields (x y : Bits) (out : A4FeeScaling.Entry.Cfg) (I : Instance)
    (C : Certificate (Fin I.data.n)) (hi : parseInstance x=some I)
    (hc : decodeCertificate I.data.n y=some C)
    (hs : A4PairedParser.Saved x y (A4FeeScaling.Entry.view out)) :
    SavedFields out.stk I C := by
  obtain ⟨a,f,ha,hr,hf,_,_⟩ := A4PairedParser.parsed_fields x I hi
  obtain ⟨hn,hH,_⟩ := A4FeeTailSpec.root_contract x a ha hr
  have hd := A4FeeTailSpec.parseInstance_finish x a f ha hf hn hH
  rw [hi] at hd
  obtain ⟨hm,hd⟩ := decodeSpecified_fields _ _ I hd.symm
  have hP := decodeRaw_parent_values _ _ hd
  have H := decodeRaw_fields _ _ hd
  have hsx := hs.1 a f ha hr hf
  have hp := (A4CertRecords.packet_iff _ _ (toRaw C)).mpr
    ⟨decodeCertificate_canonical y C hc,toRaw_sized C⟩
  have hsy := (hs.2.2 I hi).2.2 (toRaw C) hp
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [hP,A4FeeTailSpec.rebuild] using hsx.2.2.2.1
  · simpa only [H.2.2.1,A4FeeTailSpec.rebuild] using hsx.2.2.2.2.1
  · simpa only [H.2.1,A4FeeTailSpec.rebuild] using hsx.2.2.1
  · simpa only [hm] using hsx.1
  · exact hsy.2.1
  · simpa only [toRaw_length] using hsy.1

theorem instance_wire_bounds (x : Bits) (I : Instance) (hi : parseInstance x=some I) :
    ((I.data.parents.parents.toList.map Fin.val).flatMap encodeNat).length≤x.length ∧
      (I.data.H.toList.flatMap encodeNat).length≤x.length ∧
      I.data.parents.root.val.bits.length≤x.length ∧ I.routes.bits.length≤x.length := by
  obtain ⟨raw,hx,_,hd⟩ := parseInstance_canonical x I hi
  have hP := decodeRaw_parent_values _ _ hd
  have H := decodeRaw_fields _ _ hd
  rw [hP,H.2.1,H.2.2.1]
  simp only [hx,encodeSpecified,encodeInput,encodeNats,encodeList,List.length_append,
    encodeNat,word_length]
  omega

theorem certificate_wire_bounds (n : ℕ) (y : Bits) (C : Certificate (Fin n))
    (h : decodeCertificate n y=some C) :
    ((toRaw C).flatMap encodeEntry).length≤y.length ∧ C.size≤y.length := by
  have hlen := length_le_flatMap encodeEntry encodeEntry_nonempty (toRaw C)
  rw [toRaw_length] at hlen
  have hb : ((toRaw C).flatMap encodeEntry).length≤y.length := by
    simp only [decodeCertificate_canonical y C h,encodeCert,encodeRaw,encodeList,List.length_append]
    omega
  exact ⟨hb,hlen.trans hb⟩

end UAVProof.A4Verifier
