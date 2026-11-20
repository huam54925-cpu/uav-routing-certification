import LeanCompletion.UAV.TreeBudgetFeeTailSpec

/-! Arbitrary-bitstring semantic bridge from root flow plus the fee suffix to
the repository's full instance parser. -/
namespace UAVProof.A4FeeTailSpec
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetParentArray
open TreeBudgetSparseVerifier

def accepted (s : Bits) : Bool := TreeBudgetRootFlowSpec.accepted s &&
  (TreeBudgetRootFlowSpec.parse s).any (fun a => (read a.vertices a.rest).isSome)

theorem read_wire (n : ℕ) (f : Fields) : (read n (wire f)).isSome=good n f := by
  have hp := prefix_append f []
  rw [List.append_nil] at hp
  cases hg : good n f <;> simp [read,hp,hg]

theorem decodeRaw_some (raw : RawInput) : (decodeRaw raw).isSome =
    (decide (Shape raw) && (decodeParents raw.root raw.parents).isSome &&
      denominatorsPositiveB raw.denominators raw.budgetDenominator) := by
  by_cases hs : Shape raw
  · cases hp : decodeParents raw.root raw.parents with
    | none => simp [decodeRaw,hs,hp]
    | some p =>
      cases hd : denominatorsPositiveB raw.denominators raw.budgetDenominator <;>
        simp [decodeRaw,hs,hp,hd]
  · simp [decodeRaw,hs]

theorem decoded_rootSum (raw : RawInput) (I : Input) (h : decodeRaw raw=some I) :
    TreeBudgetRootFlowSpec.rootSum raw.root 0 raw.parents raw.multiplicities =
      (TreeBudgetCostedCandidates.rootCountCost I.parents I.H).value := by
  have hf := decodeRaw_fields raw I h
  have hp := decodeRaw_parent_values raw I h
  have hr := TreeBudgetRootFlowSpec.reference I.n I.parents I.H
  simpa only [TreeBudgetParentWalkTM2.table,hf.2.1,hp,hf.2.2.1] using hr

theorem decodeSpecified_some (m : ℕ) (raw : RawInput) : (decodeSpecified m raw).isSome =
    (decide (Shape raw) && (decodeParents raw.root raw.parents).isSome &&
      denominatorsPositiveB raw.denominators raw.budgetDenominator &&
      decide (TreeBudgetRootFlowSpec.rootSum raw.root 0 raw.parents raw.multiplicities=m)) := by
  rw [← decodeRaw_some]
  cases hd : decodeRaw raw with
  | none => simp [decodeSpecified,hd]
  | some I =>
    have hr := decoded_rootSum raw I hd
    by_cases hm : m=(TreeBudgetCostedCandidates.rootCountCost I.parents I.H).value <;>
      simp [decodeSpecified,hd,hr,hm,eq_comm]

def rawFields (raw : RawInput) : Fields :=
  ⟨raw.numerators,raw.denominators,raw.budgetNumerator,raw.budgetDenominator⟩

theorem accepted_encode (m : ℕ) (raw : RawInput) (hs : Shape raw) :
    accepted (encodeSpecified m raw)=(decodeSpecified m raw).isSome := by
  have he : encodeSpecified m raw=TreeBudgetRootFlowSpec.encode (TreeBudgetRootFlowTM2.inputFields m raw []) := by
    simpa only [List.append_nil] using (TreeBudgetRootFlowTM2.inputFields_encoding m raw []).symm
  have ht : (TreeBudgetRootFlowTM2.inputFields m raw []).rest=wire (rawFields raw) := by
    simp [TreeBudgetRootFlowTM2.inputFields,wire,rawFields,List.append_assoc]
  rw [he,decodeSpecified_some]
  simp only [accepted,TreeBudgetRootFlowSpec.parse_encode,Option.any_some,ht,read_wire,
    TreeBudgetRootFlowSpec.accepted_encode]
  simp [TreeBudgetRootFlowSpec.encode,TreeBudgetParentPrefix.accepted_encode,
    TreeBudgetRootFlowSpec.front,TreeBudgetRootFlowSpec.listOK,TreeBudgetRootFlowTM2.inputFields,
    good,rawFields,hs,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,Bool.and_assoc,Bool.and_comm,Bool.and_left_comm]

theorem root_parse_of_accept (s : Bits) (h : TreeBudgetRootFlowSpec.accepted s=true) :
    ∃ a, TreeBudgetRootFlowSpec.parse s=some a := by
  cases hp : TreeBudgetParentPrefix.parse s with
  | none => simp [TreeBudgetRootFlowSpec.accepted,TreeBudgetParentPrefix.accepted,hp] at h
  | some a =>
    cases hh : parseNats a.rest with
    | none => simp [TreeBudgetRootFlowSpec.accepted,TreeBudgetRootFlowSpec.suffixOK,hp,hh] at h
    | some e =>
      obtain ⟨hs,t⟩ := e
      exact ⟨⟨a.routes,a.vertices,a.root,a.parents,hs,t⟩,by simp [TreeBudgetRootFlowSpec.parse,hp,hh]⟩

/-- Equality on every raw instance string, not only successful encodings. -/
theorem accepted_eq_parseInstance (s : Bits) : accepted s=(parseInstance s).isSome := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hh : TreeBudgetRootFlowSpec.accepted s=true ∧
        (TreeBudgetRootFlowSpec.parse s).any (fun a => (read a.vertices a.rest).isSome)=true := by
      simpa only [accepted,Bool.and_eq_true] using h
    obtain ⟨hr,hf⟩ := hh
    obtain ⟨a,ha⟩ := root_parse_of_accept s hr
    simp only [ha,Option.any_some] at hf
    obtain ⟨f,hf⟩ := Option.isSome_iff_exists.mp hf
    have hp := TreeBudgetRootFlowSpec.canonical s a ha
    have root := (TreeBudgetRootFlowSpec.accepts_iff a).mp (by simpa [← hp] using hr)
    have fee := (good_iff _ _).mp ((read_iff _ _ _).mp hf).2
    have shape : Shape (rebuild a f) := ⟨root.1.symm,root.2.2.1,fee.1,fee.2.1⟩
    have eq := rebuild_wire s a f ha hf
    rw [eq] at h ⊢
    simpa only [accepted_encode _ _ shape,parseInstance_encode _ _ shape] using h
  · intro h
    obtain ⟨I,hI⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨raw,he,hs,hd⟩ := parseInstance_canonical s I hI
    rw [he,parseInstance_encode _ _ hs] at hI
    rw [he,accepted_encode _ _ hs,hI]
    rfl

theorem root_contract (s : Bits) (a : TreeBudgetRootFlowSpec.Raw)
    (ha : TreeBudgetRootFlowSpec.parse s=some a) (hr : TreeBudgetRootFlowSpec.accepted s=true) :
    a.parents.length=a.vertices ∧ a.demands.length=a.vertices ∧
      TreeBudgetParentPrefix.accepted s=true := by
  have he := TreeBudgetRootFlowSpec.canonical s a ha
  have h := (TreeBudgetRootFlowSpec.accepts_iff a).mp (by simpa only [← he] using hr)
  have hp : TreeBudgetParentPrefix.accepted s=true := by
    have hh : TreeBudgetParentPrefix.accepted s=true ∧
        (TreeBudgetParentPrefix.parse s).any TreeBudgetRootFlowSpec.suffixOK=true := by
      simpa only [TreeBudgetRootFlowSpec.accepted,Bool.and_eq_true] using hr
    exact hh.1
  exact ⟨h.1.symm,h.2.2.1,hp⟩

/-- Dimensions and fee suffix are bounded by the occupied raw input, even when
the fee suffix is malformed. No bound depends on its declared natural values. -/
theorem fee_input_bounds (s : Bits) (a : TreeBudgetRootFlowSpec.Raw)
    (ha : TreeBudgetRootFlowSpec.parse s=some a) (hr : TreeBudgetRootFlowSpec.accepted s=true) :
    (a.parents.flatMap encodeNat).length ≤ s.length ∧ a.vertices.bits.length ≤ s.length ∧
      a.vertices ≤ s.length ∧ a.rest.length ≤ s.length := by
  have he := TreeBudgetRootFlowSpec.canonical s a ha
  have hn := (root_contract s a ha hr).1
  have hp := TreeBudgetParentPrefix.occupied (TreeBudgetRootFlowSpec.front a)
  have hc : TreeBudgetParentPrefix.encode (TreeBudgetRootFlowSpec.front a)=s := he.symm
  rw [hc] at hp
  simp only [TreeBudgetRootFlowSpec.front,TreeBudgetParentPrefix.body,List.length_append] at hp
  omega

end UAVProof.A4FeeTailSpec
