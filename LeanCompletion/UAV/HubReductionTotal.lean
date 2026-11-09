import LeanCompletion.UAV.HubReductionEncoding
import LeanCompletion.UAV.HubThreePartitionExamples

/-! Total bitstring transformation. Invalid sources map to the fixed 129-bit
NO instance. The target language does not impose the source promises.
Output length is not a running-time bound. -/
namespace UAVProof.HubReductionTotal
open HubGammaCodec HubReductionCodec HubReductionEncoding HubThreePartition

instance {m : ℕ} (a : Item m → ℕ) (b : ℕ) : Decidable (ValidInput a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def noSource : Source := ⟨2,30,[9,9,9,13,10,10]⟩
theorem noSource_shape : SourceShape noSource := by decide +kernel

theorem noSource_weights : sourceWeights noSource noSource_shape =
    HubThreePartitionExamples.badWeights := by
  funext i
  fin_cases i <;> rfl

def noBits : Bits := encodeTarget (canonicalTarget noSource)

theorem noBits_length : noBits.length = 129 := by decide +kernel

/-- Canonical strict-hub target language; no source validity assumption. -/
def TargetLanguage (y : Bits) : Prop :=
  ∃ t, decodeTarget y = some t ∧
    (∃ s, SourceShape s ∧ t = canonicalTarget s) ∧ SparseFeasible t

theorem targetLanguage_encode (s : Source) (hs : SourceShape s) :
    TargetLanguage (encodeTarget (canonicalTarget s)) ↔ SparseFeasible (canonicalTarget s) := by
  simp only [TargetLanguage, decodeTarget_encode _ (canonicalTarget_wellFormed s hs),
    Option.some.injEq]
  constructor
  · rintro ⟨t,rfl,_,hf⟩; exact hf
  · intro hf; exact ⟨_,rfl,⟨s,hs,rfl⟩,hf⟩

theorem noBits_not_mem : ¬ TargetLanguage noBits := by
  rw [noBits, targetLanguage_encode noSource noSource_shape,
    canonicalTarget_feasible_iff noSource noSource_shape, noSource_weights]
  exact HubThreePartitionExamples.infeasible_exact_routing

def SourceLanguage (x : Bits) : Prop :=
  ∃ s, ∃ hs : SourceShape s, decodeSource x = some s ∧
    ValidInput (sourceWeights s hs) s.budget ∧ ThreePartition (sourceWeights s hs) s.budget

def reduceBits (x : Bits) : Bits :=
  match decodeSource x with
  | none => noBits
  | some s =>
    if hs : SourceShape s then
      if ValidInput (sourceWeights s hs) s.budget then encodeTarget (canonicalTarget s)
      else noBits
    else noBits

theorem reduceBits_correct (x : Bits) : SourceLanguage x ↔ TargetLanguage (reduceBits x) := by
  cases hd : decodeSource x with
  | none => simp [SourceLanguage, reduceBits, hd, noBits_not_mem]
  | some s =>
    obtain ⟨hs,_⟩ := (decodeSource_eq_some_iff x s).1 hd
    by_cases hv : ValidInput (sourceWeights s hs) s.budget
    · simp only [reduceBits, hd, dif_pos hs, if_pos hv]
      rw [targetLanguage_encode s hs, canonicalTarget_threePartition_iff s hs hv]
      simp [SourceLanguage, hd, hs, hv]
    · simp [SourceLanguage, reduceBits, hd, hs, hv, noBits_not_mem]

theorem reduceBits_length_le (x : Bits) : (reduceBits x).length ≤ 4*x.length+129 := by
  cases hd : decodeSource x with
  | none => simp [reduceBits, hd, noBits_length]
  | some s =>
    obtain ⟨hs,hx⟩ := (decodeSource_eq_some_iff x s).1 hd
    by_cases hv : ValidInput (sourceWeights s hs) s.budget
    · simp only [reduceBits, hd, dif_pos hs, if_pos hv]
      have := canonicalTarget_length_le_of_valid s hs hv
      rw [hx]; omega
    · simp [reduceBits, hd, hs, hv, noBits_length]

theorem reduceBits_decodes (x : Bits) :
    ∃ s, SourceShape s ∧ decodeTarget (reduceBits x) = some (canonicalTarget s) := by
  have hno : decodeTarget noBits = some (canonicalTarget noSource) :=
    decodeTarget_encode _ (canonicalTarget_wellFormed noSource noSource_shape)
  cases hd : decodeSource x with
  | none => exact ⟨noSource,noSource_shape,by simpa [reduceBits,hd] using hno⟩
  | some s =>
    obtain ⟨hs,_⟩ := (decodeSource_eq_some_iff x s).1 hd
    by_cases hv : ValidInput (sourceWeights s hs) s.budget
    · exact ⟨s,hs,by simp [reduceBits,hd,hs,hv,canonicalTarget_wellFormed s hs]⟩
    · exact ⟨noSource,noSource_shape,by simpa [reduceBits,hd,hs,hv] using hno⟩

end UAVProof.HubReductionTotal
