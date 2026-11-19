import LeanCompletion.UAV.TreeBudgetSparseCostedFrontend
import LeanCompletion.UAV.TreeBudgetSparseCheckBounds

/-! Unconditional total reference-word work for the complete binary verifier.
The separate finite-alphabet machine simulation is not assumed or proved here. -/
namespace UAVProof.TreeBudgetSparseTotalWork
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCandidates
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetCostedCodec TreeBudgetCostedParsing
open TreeBudgetCostedInput TreeBudgetSparseCodec TreeBudgetSparseVerifier
open TreeBudgetSparseExecutionWidths TreeBudgetSparseCostedCheck TreeBudgetSparseCostedParsing
open TreeBudgetSparseCostedFrontend TreeBudgetSparseCheckBounds TreeBudgetSparsePrefixBounds

theorem rootGuardD_work (raw : RawInput) (J : Input) (m N : ℕ)
    (hd : decodeRaw raw = some J) (hl : (encodeInput raw).length ≤ N) (hm : m.size ≤ N) :
    work (rootGuardD J m) ≤ 4096 * (N + 1) ^ 3 := by
  have hn : J.n ≤ N := ((decodeRaw_fields raw J hd).1.trans_le
    (vertexCount_le_length raw (decodeRaw_shape raw J hd))).trans hl
  have hH : ∀ v : Fin J.n, J.H[v].size ≤ N := fun v =>
    (TreeBudgetBinarySearchInputBounds.decoded_coordinate_width raw J hd v).trans hl
  let B := (N + 1) ^ 2
  have hNB : N ≤ B := by dsimp [B]; nlinarith
  have hr := rootTerms_width J.parents J.H N hH
  have hprod := Nat.mul_le_mul_right N hn
  have hs : (rootTerms J.parents J.H).sum.size ≤ B := by dsimp [B]; nlinarith
  have ht := rootCountCost_work J.parents J.H B ((nat_size_le _).trans (hn.trans hNB))
    (fun v => (hH v).trans hNB) hs
  have he : (rootCountCost J.parents J.H).value = (rootTerms J.parents J.H).sum := by
    simp [rootCountCost, rootTerms, List.map_ofFn, Function.comp_def]
  have hw : (rootCountCost J.parents J.H).value.size ≤ B := by rw [he]; exact hs
  have es := (dynamic_steps m _ B (hm.trans hNB) hw).1
  have ea := (dynamic_allocations m _ B (hm.trans hNB) hw).1
  have hmul := Nat.mul_le_mul_right (B + 1) (Nat.add_le_add_right hn 1)
  simp only [rootGuardD, work]
  split_ifs <;> dsimp only
  all_goals unfold work at ht
  all_goals dsimp [B] at *
  all_goals nlinarith only [ht, es, ea, hmul, Nat.zero_le N,
    Nat.zero_le (N ^ 2), Nat.zero_le (N ^ 3)]

theorem decodeSpecifiedD_work (raw : RawInput) (m N : ℕ) (hs : Shape raw)
    (hl : (encodeInput raw).length ≤ N) (hm : m.size ≤ N) :
    work (decodeSpecifiedD m raw) ≤ 65536 * (N + 1) ^ 3 := by
  have hv := TreeBudgetCostedInput.decodeRawCost_work_encoded raw hs
  have ht := thenD_work (decodeRawCost raw) (fun J => rootGuardD J m) (4096 * (N + 1) ^ 3)
    (fun J hJ => rootGuardD_work raw J m N (by simpa using hJ) hl hm)
  have hpoly : ((encodeInput raw).length + 1) ^ 2 * ((encodeInput raw).length + 3) ≤
      3 * (N + 1) ^ 3 := by
    calc
      _ ≤ (N + 1) ^ 2 * (3 * (N + 1)) := by gcongr; omega
      _ = _ := by ring
  change work (thenD _ _) ≤ _
  nlinarith [show 1 ≤ (N + 1) ^ 3 by exact one_le_pow₀ (by omega)]

theorem parseInstanceD_work (input : Bits) :
    work (parseInstanceD input) ≤ 262144 * (input.length + 1) ^ 3 := by
  have hp := parseSpecifiedD_work input
  have ht := thenD_work (parseSpecifiedD input) (fun (m, raw) => decodeSpecifiedD m raw)
    (65536 * (input.length + 1) ^ 3) (by
      rintro ⟨m, raw⟩ h
      obtain ⟨he, hs⟩ := parseSpecifiedRaw_canonical input m raw (by simpa using h)
      have hl := congrArg List.length he
      simp only [encodeSpecified, List.length_append, encodeNat_length] at hl
      exact decodeSpecifiedD_work raw m input.length hs (by omega) (by omega))
  change work (thenD _ _) ≤ _
  unfold work at ht ⊢
  nlinarith [Nat.zero_le (input.length ^ 2), Nat.zero_le (input.length ^ 3)]

theorem parsed_raw_dimensions (wire : Bits) (xs : RawCertificate) (h : parseRaw wire = some xs) :
    xs.length ≤ wire.length ∧ ∀ e ∈ xs, e.2.length ≤ wire.length := by
  have he := parseRaw_canonical wire xs h
  have ho : Occupies wire xs := ⟨encodeNat xs.length, [], by simp [he, encodeRaw, encodeList]⟩
  refine ⟨occupied_entry_count wire xs ho, ?_⟩
  intro e hem
  have hn : e.2.length ≤ (encodeEntry e).length := by
    simp only [encodeEntry, List.length_append, encodeNat_length, encodeNats_length]
    omega
  have hm : (encodeEntry e).length ≤ (xs.flatMap encodeEntry).length := by
    rw [List.length_flatMap]
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨e, hem, rfl⟩)
  obtain ⟨before, after, hx⟩ := ho
  have := congrArg List.length hx
  simp only [List.length_append] at this
  omega

theorem sizesD_work (n N : ℕ) (xs : RawCertificate) (hn : n ≤ N)
    (hk : xs.length ≤ N) (hr : ∀ e ∈ xs, e.2.length ≤ N) :
    work (sizesD n xs) ≤ 512 * (N + 1) ^ 3 := by
  have ht := allD_work (fun e : RawEntry =>
    (⟨(eqNatD (lengthD e.2).value n).value,
      (lengthD e.2).steps + (eqNatD (lengthD e.2).value n).steps + 1,
      (lengthD e.2).allocations + (eqNatD (lengthD e.2).value n).allocations⟩ : Costed Bool))
    xs (400 * (N + 1) ^ 2) (by
      intro e he
      have hl := lengthD_steps e.2
      have ha := lengthD_allocations_le_steps e.2
      have hw := (nat_size_le e.2.length).trans (hr e he)
      have hs := (dynamic_steps e.2.length n N hw ((nat_size_le n).trans hn)).1
      have hb := (dynamic_allocations e.2.length n N hw ((nat_size_le n).trans hn)).1
      have hpow : (e.2.length + 1) ^ 2 ≤ (N + 1) ^ 2 := by gcongr; exact hr e he
      simp only [lengthD_value, work]
      nlinarith)
  have hm := Nat.mul_le_mul_right (400 * (N + 1) ^ 2 + 2) hk
  change work (allD _ _) ≤ _
  nlinarith [Nat.zero_le (N ^ 2), Nat.zero_le (N ^ 3)]

theorem decodeCertificateD_work (n N : ℕ) (wire : Bits) (hn : n ≤ N) (hw : wire.length ≤ N) :
    work (decodeCertificateD n wire) ≤ 16384 * (N + 1) ^ 3 := by
  have hp := parseRawD_work wire
  have ht := thenD_work (parseRawD wire) (finishCertificateD n) (1024 * (N + 1) ^ 3) (by
    intro xs hx
    obtain ⟨hk, hr⟩ := parsed_raw_dimensions wire xs (by simpa using hx)
    have hs := sizesD_work n N xs hn (hk.trans hw) (fun e he => (hr e he).trans hw)
    simp only [finishCertificateD, work]
    split_ifs <;> dsimp only
    all_goals unfold work at hs
    all_goals nlinarith only [hs, show 1 ≤ (N + 1) ^ 3 by exact one_le_pow₀ (by omega)])
  have hpow : (wire.length + 1) ^ 3 ≤ (N + 1) ^ 3 := by gcongr
  change work (thenD _ _) ≤ _
  unfold work at ht ⊢
  nlinarith [show 1 ≤ (N + 1) ^ 3 by exact one_le_pow₀ (by omega)]

/-- Both strings are arbitrary. Every false-return branch is included. -/
theorem verifyD_work (input wire : Bits) :
    work (verifyD input wire) ≤ 4194304 * (input.length + wire.length + 1) ^ 6 := by
  let N := input.length + wire.length
  have hp := parseInstanceD_work input
  have ht := onSomeD_work (parseInstanceD input) (fun I =>
    onSomeD (decodeCertificateD I.data.n wire) (checkD I))
    (2129920 * (N + 1) ^ 6) (by
      intro I hi
      have hi' : parseInstance input = some I := by simpa using hi
      obtain ⟨raw, he, hs, hd⟩ := parseInstance_canonical input I hi'
      have hl := congrArg List.length he
      simp only [encodeSpecified, List.length_append] at hl
      have hn := ((decodeRaw_fields raw I.data hd).1.trans_le (vertexCount_le_length raw hs))
      have hdecode := decodeCertificateD_work I.data.n N wire (by dsimp [N]; omega) (by dsimp [N]; omega)
      have hcheck := onSomeD_work (decodeCertificateD I.data.n wire) (checkD I)
        (2097152 * (N + 1) ^ 6) (fun C hc => checkD_work input wire I C hi' (by simpa using hc))
      have hpow := pow_up N 3 6 (by omega)
      have hpos : 1 ≤ (N + 1) ^ 6 := by exact one_le_pow₀ (by omega)
      change work (onSomeD (decodeCertificateD I.data.n wire) (checkD I)) ≤ _
      omega)
  have hpow : (input.length + 1) ^ 3 ≤ (N + 1) ^ 6 :=
    (by gcongr; dsimp [N]; omega : (input.length + 1) ^ 3 ≤ (N + 1) ^ 3) |>.trans
      (pow_up N 3 6 (by omega))
  have hpos : 1 ≤ (N + 1) ^ 6 := by exact one_le_pow₀ (by omega)
  change work (onSomeD _ _) ≤ 4194304 * (N + 1) ^ 6
  omega

theorem verifyD_refines_and_polynomial (input wire : Bits) :
    (verifyD input wire).value = verify input wire ∧
    work (verifyD input wire) ≤ 4194304 * (input.length + wire.length + 1) ^ 6 :=
  ⟨verifyD_value input wire, verifyD_work input wire⟩

end UAVProof.TreeBudgetSparseTotalWork
