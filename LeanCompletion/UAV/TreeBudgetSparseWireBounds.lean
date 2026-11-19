import LeanCompletion.UAV.TreeBudgetSparseVerifier
import LeanCompletion.UAV.TreeBudgetSparseCertificate

/-! Length of the actual certificate encoding, measured against the actual
specified-route input bits. This is a length/semantics result, not a runtime bound. -/
namespace UAVProof.TreeBudgetSparseWireBounds

open TreeFlowExistence TreeBudgetPatterns TreeBudgetMatrix TreeBudgetCertificate
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetSparseCodec
open TreeBudgetSparseVerifier TreeBudgetSparse TreeBudgetVector TreeBudgetCostedCandidates

theorem encodeNat_length_mono {a b : ℕ} (h : a ≤ b) :
    (encodeNat a).length ≤ (encodeNat b).length := by
  have hs := Nat.size_le_size h
  simp only [encodeNat_length]
  omega

theorem encodeRow_length {n : ℕ} (p : Fin n → ℕ) :
    (encodeNats (List.ofFn p)).length =
      2 * Nat.size n + 1 + 2 * (∑ v, Nat.size (p v)) + n := by
  simp [encodeNats_length, List.map_ofFn, List.sum_ofFn]

theorem vector_toList {n : ℕ} (H : Vector ℕ n) : List.ofFn (decode H) = H.toList := by
  simpa [encode, Vector.toList_ofFn] using congrArg Vector.toList (encode_decode H)

theorem encodeRow_length_mono {n : ℕ} (p q : Fin n → ℕ) (h : ∀ v, p v ≤ q v) :
    (encodeNats (List.ofFn p)).length ≤ (encodeNats (List.ofFn q)).length := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => Nat.size_le_size (h v))
  rw [encodeRow_length, encodeRow_length]
  omega

theorem input_fields_length (m : ℕ) (raw : RawInput) :
    (encodeNat m).length + (encodeNats raw.multiplicities).length ≤
      (encodeSpecified m raw).length := by
  simp only [encodeSpecified, encodeInput, List.length_append]
  omega

theorem input_twice_bits (m : ℕ) (raw : RawInput) :
    2 * (Nat.size m + (raw.multiplicities.map Nat.size).sum) ≤
      (encodeSpecified m raw).length := by
  have h := input_fields_length m raw
  rw [encodeNat_length, encodeNats_length] at h
  omega

theorem parsed_fields_length (input : Bits) (I : Instance) (hp : parseInstance input = some I) :
    (encodeNat I.routes).length + (encodeNats I.data.H.toList).length ≤ input.length := by
  obtain ⟨raw, he, _, hd⟩ := parseInstance_canonical input I hp
  have hf := (decodeRaw_fields raw I.data hd).2.2.1
  rw [he, hf]
  exact input_fields_length I.routes raw

theorem parsed_twice_bits (input : Bits) (I : Instance) (hp : parseInstance input = some I) :
    2 * (Nat.size I.routes + ∑ v, Nat.size (decode I.data.H v)) ≤ input.length := by
  obtain ⟨raw, he, _, hd⟩ := parseInstance_canonical input I hp
  have hf := (decodeRaw_fields raw I.data hd).2.2.1
  have h := input_twice_bits I.routes raw
  rw [← hf, ← vector_toList] at h
  simpa [he, List.map_ofFn, List.sum_ofFn] using h

theorem nonroot_bits_le_total {n : ℕ} (R : RootedTree (Fin n)) (H : Fin n → ℕ) :
    (∑ v : Nonroot R, Nat.size (H v.val)) ≤ ∑ v, Nat.size (H v) := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.erase R.root) (by simp) (fun v => Nat.size (H v))]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

theorem valid_count_le {n : ℕ} (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (m : ℕ) (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : TreeBudgetCertificate.Valid R H m s T C) (i : Fin C.size) : C.count i ≤ m := by
  rw [← hc.2.1]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem positive_size_le_routes {n : ℕ} (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (m : ℕ) (s : Fin n → ℚ) (T : ℚ) (C : Certificate (Fin n))
    (hc : TreeBudgetCertificate.Valid R H m s T C) (hpos : ∀ i, 0 < C.count i) : C.size ≤ m := by
  calc
    C.size = ∑ _i : Fin C.size, 1 := by simp
    _ ≤ ∑ i, C.count i := Finset.sum_le_sum (fun i _ => hpos i)
    _ = m := hc.2.1

theorem valid_row_le {n : ℕ} (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (s : Fin n → ℚ) (T : ℚ) (p : Fin n → ℕ) (hp : RowValid R H s T p) :
    ∀ v, p v ≤ H v := by
  intro v
  by_cases hv : v = R.root
  · subst v; rw [hp.1]; exact Nat.zero_le _
  · exact hp.2.1 v hv

/-- The count and row fields of each valid entry fit into the corresponding
two input fields. This also covers valid zero-count entries. -/
theorem entry_length_le_input (input : Bits) (I : Instance)
    (hp : parseInstance input = some I) (C : Certificate (Fin I.data.n))
    (hc : TreeBudgetCertificate.Valid (tree I) (decode I.data.H) I.routes (fees I) (budget I) C)
    (i : Fin C.size) :
    (encodeNat (C.count i)).length + (encodeNats (List.ofFn (C.row i))).length ≤ input.length := by
  have hcount := encodeNat_length_mono (valid_count_le _ _ _ _ _ C hc i)
  have hrow := encodeRow_length_mono (C.row i) (decode I.data.H)
    (valid_row_le _ _ _ _ _ (hc.1 i))
  rw [vector_toList] at hrow
  exact (Nat.add_le_add hcount hrow).trans (parsed_fields_length input I hp)

theorem sparse_size_le_half_input (input : Bits) (I : Instance)
    (hp : parseInstance input = some I) (k : ℕ)
    (hk : k ≤ Nat.size I.routes + ∑ v : Nonroot (tree I), Nat.size (decode I.data.H v.val)) :
    k ≤ input.length / 2 := by
  have hn := nonroot_bits_le_total (tree I) (decode I.data.H)
  have hi := parsed_twice_bits input I hp
  omega

/-- Exact chosen wire format: header <= L and every entry <= L. -/
theorem certificate_length_bound (input : Bits) (I : Instance)
    (hp : parseInstance input = some I) (C : Certificate (Fin I.data.n))
    (hc : TreeBudgetCertificate.Valid (tree I) (decode I.data.H) I.routes (fees I) (budget I) C)
    (hpos : ∀ i, 0 < C.count i)
    (hbits : C.size ≤ Nat.size I.routes +
      ∑ v : Nonroot (tree I), Nat.size (decode I.data.H v.val)) :
    (encodeCert C).length ≤ input.length * (input.length / 2 + 1) := by
  have hk := sparse_size_le_half_input input I hp C.size hbits
  have hm := positive_size_le_routes _ _ _ _ _ C hc hpos
  have hhead := (encodeNat_length_mono hm).trans
    (Nat.le_trans (Nat.le_add_right _ _) (parsed_fields_length input I hp))
  have hs : (∑ i, ((encodeNat (C.count i)).length +
      (encodeNats (List.ofFn (C.row i))).length)) ≤ C.size * input.length := by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => entry_length_le_input input I hp C hc i)
  have hmul := Nat.mul_le_mul_right input.length hk
  rw [encodeCert_length]
  nlinarith

/-- Main short-bitstring existence theorem, using the single simultaneous
sparse certificate from A0--A2 and the actual input and certificate encoders. -/
theorem exists_short_witness (input : Bits) (I : Instance)
    (hp : parseInstance input = some I)
    (hm : MatrixFeasible (tree I) (decode I.data.H) I.routes (fees I) (budget I)) :
    ∃ certificate : Bits, verify input certificate = true ∧
      certificate.length ≤ input.length * (input.length / 2 + 1) := by
  obtain ⟨C, hc, _, hpos, _, hbits, _⟩ :=
    exists_sparse_certificate (tree I) (decode I.data.H) I.routes (fees I) (budget I) hm
  refine ⟨encodeCert C, ?_, certificate_length_bound input I hp C
    ((checkCertificate_eq_true_iff ..).mp hc) hpos hbits⟩
  exact (verify_parsed_iff input (encodeCert C) I hp).mpr ⟨C, rfl, hc⟩

/-- All input strings, including malformed ones. Polynomial verification time
is a separate A4 obligation; this theorem proves semantics and witness length. -/
theorem language_iff_short_witness (input : Bits) :
    (∃ I : Instance, parseInstance input = some I ∧
      MatrixFeasible (tree I) (decode I.data.H) I.routes (fees I) (budget I)) ↔
    ∃ certificate : Bits, certificate.length ≤ input.length * (input.length / 2 + 1) ∧
      verify input certificate = true := by
  constructor
  · rintro ⟨I, hp, hm⟩
    obtain ⟨bits, hv, hl⟩ := exists_short_witness input I hp hm
    exact ⟨bits, hl, hv⟩
  · rintro ⟨bits, _, hv⟩
    obtain ⟨I, hp, C, _, hc⟩ := (verify_refines input bits).mp hv
    exact ⟨I, hp, valid_implies_matrix _ _ _ _ _ C ((checkCertificate_eq_true_iff ..).mp hc)⟩

theorem feasible_routes_eq_root {n : ℕ} (R : RootedTree (Fin n)) (H : Fin n → ℕ)
    (m : ℕ) (s : Fin n → ℚ) (T : ℚ) (hm : MatrixFeasible R H m s T) : m = rootCount R H := by
  obtain ⟨z, hz⟩ := (matrix_iff_augmented_counts R H m s T).mp hm
  have ht : (∑ p, z p) = m := by simpa [augmented, target] using hz none
  exact ht.symm.trans (pattern_count_total R H s T z (fun v hv => hz (some ⟨v, hv⟩)))

/-- The explicit root-flow precheck does not discard a feasible specified-m input. -/
theorem feasible_raw_has_short_witness (raw : RawInput) (J : Input) (m : ℕ)
    (hd : decodeRaw raw = some J)
    (hm : MatrixFeasible (TreeBudgetParentArray.toRootedTree J.parents J.valid) (decode J.H) m
      (fun v => (J.numerators[v] : ℚ) / (J.denominators[v] : ℚ))
      ((J.budgetNumerator : ℚ) / (J.budgetDenominator : ℚ))) :
    ∃ certificate : Bits, verify (encodeSpecified m raw) certificate = true ∧
      certificate.length ≤ (encodeSpecified m raw).length * ((encodeSpecified m raw).length / 2 + 1) := by
  have hroot : m = (rootCountCost J.parents J.H).value := by
    rw [rootCountCost_value J.parents J.valid]
    exact feasible_routes_eq_root _ _ m _ _ hm
  let I : Instance := ⟨J, m, hroot⟩
  have hp : parseInstance (encodeSpecified m raw) = some I := by
    rw [parseInstance_encode m raw (decodeRaw_shape raw J hd)]
    simp [decodeSpecified, hd, hroot, I]
  exact exists_short_witness (encodeSpecified m raw) I hp hm

end UAVProof.TreeBudgetSparseWireBounds
