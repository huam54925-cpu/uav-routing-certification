import LeanCompletion.UAV.TreeBudgetSparseCostedCheck

/-! Decoded checking costs. Decoding equations are used only to bound actual
read fields; acceptance/Valid/target bounds are never assumed. -/
namespace UAVProof.TreeBudgetSparseCheckBounds
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetCostedCandidates
open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetBinaryPreprocessing
open TreeBudgetSparseCodec TreeBudgetSparseVerifier TreeBudgetSparseWeightedCost
open TreeBudgetSparseExecutionWidths TreeBudgetSparseCostedCheck TreeBudgetCertificate
open TreeBudgetBinaryExecutionBounds TreeBudgetSparsePrefixBounds

theorem pow_up (N a b : ℕ) (h : a ≤ b) : (N + 1) ^ a ≤ (N + 1) ^ b :=
  Nat.pow_le_pow_right (by omega) h

set_option maxHeartbeats 4000000 in
theorem checkD_work (input wire : Bits) (I : Instance) (C : Certificate (Fin I.data.n))
    (hi : parseInstance input = some I) (hc : decodeCertificate I.data.n wire = some C) :
    work (checkD I C) ≤ 2097152 * (input.length + wire.length + 1) ^ 6 := by
  let N := input.length + wire.length
  obtain ⟨raw, hcanon, hshape, hd⟩ := parseInstance_canonical input I hi
  have hlen : (encodeInput raw).length ≤ N := by
    have hl := congrArg List.length hcanon
    simp only [encodeSpecified, List.length_append] at hl
    dsimp [N]; omega
  have hm : I.routes.size ≤ N := by
    have hl := congrArg List.length hcanon
    simp only [encodeSpecified, List.length_append, encodeNat_length] at hl
    dsimp [N]; omega
  have hn : I.data.n ≤ N := ((decodeRaw_fields raw I.data hd).1.trans_le
    (vertexCount_le_length raw hshape)).trans hlen
  have hH : ∀ v : Fin I.data.n, I.data.H[v].size ≤ N := fun v =>
    (TreeBudgetBinarySearchInputBounds.decoded_coordinate_width raw I.data hd v).trans hlen
  have hA : ∀ v : Fin I.data.n,
      (TreeBudgetVectorChecker.scaleFees I.data.numerators I.data.denominators
        I.data.budgetDenominator)[v].natAbs.size ≤ 2 * N + 1 := fun v =>
    (scaled_fee_width raw I.data hd v).trans (by omega)
  have hT := (scaled_budget_width raw I.data hd).trans
    (by omega : 2 * (encodeInput raw).length + 1 ≤ 2 * N + 1)
  obtain ⟨hk, hcount, hrow⟩ := decoded_fields wire C hc
  have hWN : wire.length ≤ N := by dsimp [N]; omega
  have hkN := hk.trans hWN
  have hcN : ∀ i, (C.count i).size ≤ N := fun i => (hcount i).trans hWN
  have hpN : ∀ i v, (C.row i v).size ≤ N := fun i v => (hrow i v).trans hWN
  have hmat := materialize_work C N hn hkN hcN
  have hpre := preprocessing_steps raw I.data hd
  have haf := scaleFeesCost_allocations I.data.numerators I.data.denominators I.data.budgetDenominator
  have hat := scaleBudgetCost_allocations I.data.denominators I.data.budgetNumerator
  have hpreN : work (scaleFeesCost I.data.numerators I.data.denominators I.data.budgetDenominator) +
      work (scaleBudgetCost I.data.denominators I.data.budgetNumerator) ≤ 65536 * (N + 1) ^ 4 := by
    have hpow : ((encodeInput raw).length + 1) ^ 4 ≤ (N + 1) ^ 4 := by gcongr
    unfold work
    omega
  let rows := fun i : Fin C.size =>
    let p := copyVector (Vector.ofFn (C.row i))
    let out := rowCheck I.data.parents I.data.H
      (scaleFeesCost I.data.numerators I.data.denominators I.data.budgetDenominator).value
      (scaleBudgetCost I.data.denominators I.data.budgetNumerator).value p.value
    (⟨out.value, p.steps + out.steps + 1, p.allocations + out.allocations⟩ : Costed Bool)
  have hr : ∀ i, work (rows i) ≤ 524544 * (N + 1) ^ 5 := by
    intro i
    have hp : ∀ v : Fin I.data.n, (Vector.ofFn (C.row i))[v].size ≤ N := by simpa using hpN i
    have hcopy := copyVector_work (Vector.ofFn (C.row i)) N hp
    have hcheck := arbitrary_row_work I.data.parents I.data.H _ _ (Vector.ofFn (C.row i)) N
      hn hH hA hT hp
    have hnm : (I.data.n + 1) * (N + 1) ≤ (N + 1) ^ 2 := by nlinarith
    have hpow := pow_up N 2 5 (by omega)
    dsimp only [rows]
    simp only [copyVector_value, scaleFeesCost_value _ _ _ I.data.positive,
      scaleBudgetCost_value _ _ _ I.data.budgetPositive, work] at *
    nlinarith [show 1 ≤ (N + 1) ^ 5 by exact one_le_pow₀ (by omega)]
  have hrows := allFinD_work C.size N (524544 * (N + 1) ^ 5) rows hkN hr
  have hrowsN : work (allFinD C.size rows) ≤ 1048576 * (N + 1) ^ 6 := by
    have hmul := Nat.mul_le_mul_right (524544 * (N + 1) ^ 5 + 256 * (N + 2) + 4) hkN
    nlinarith [Nat.zero_le (N ^ 2), Nat.zero_le (N ^ 3), Nat.zero_le (N ^ 4), Nat.zero_le (N ^ 5), Nat.zero_le (N ^ 6)]
  have hsum : ((toRaw C).map Prod.fst).sum.size ≤ (N + 1) ^ 2 := by
    have ht := size_sum_uniform ((toRaw C).map Prod.fst) N (by
      intro x hx
      simp only [toRaw, List.map_ofFn, Function.comp_def] at hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hcN i)
    simp only [List.length_map, toRaw_length] at ht
    have := Nat.mul_le_mul_right N hkN
    nlinarith
  have htotal := countD_work (toRaw C) ((N + 1) ^ 2) hsum
  simp only [toRaw_length] at htotal
  have hsum' : (countD (toRaw C)).value.size ≤ (N + 1) ^ 2 := by simpa using hsum
  have hm' : I.routes.size ≤ (N + 1) ^ 2 := hm.trans (by nlinarith)
  have heqs := (dynamic_steps _ _ _ hsum' hm').1
  have heqa := (dynamic_allocations _ _ _ hsum' hm').1
  have hcols : ∀ v, work (columnCheckD I (toRaw C) v) ≤ 1024 * (N + 1) ^ 3 := by
    intro v
    have hcol := decoded_column_wire_work wire C v hc
    have hw : (columnD (toRaw C) v.val).value.size ≤ N := by
      rw [columnD_value]
      exact (column_accumulator_width wire (toRaw C) v.val (decoded_occupation wire C hc)).trans (by omega)
    have hv : v.val.size ≤ N := (TreeBudgetCostedCodec.nat_size_le _).trans (v.isLt.le.trans hn)
    have hroot : I.data.parents.root.val.size ≤ N := (TreeBudgetCostedCodec.nat_size_le _).trans
      (I.data.parents.root.isLt.le.trans hn)
    have hs₁ := (dynamic_steps _ _ N hw (hH v)).1
    have ha₁ := (dynamic_allocations _ _ N hw (hH v)).1
    have hs₂ := (dynamic_steps _ _ N hv hroot).1
    have ha₂ := (dynamic_allocations _ _ N hv hroot).1
    have hpow : (wire.length + 1) ^ 3 ≤ (N + 1) ^ 3 := by gcongr
    simp only [columnCheckD, work]
    nlinarith [Nat.zero_le (N ^ 2), Nat.zero_le (N ^ 3)]
  have hcolumns := allFinD_work I.data.n N (1024 * (N + 1) ^ 3) _ hn hcols
  have hcolumnsN : work (allFinD I.data.n (columnCheckD I (toRaw C))) ≤ 4096 * (N + 1) ^ 4 := by
    have hmul := Nat.mul_le_mul_right (1024 * (N + 1) ^ 3 + 256 * (N + 2) + 4) hn
    nlinarith [Nat.zero_le (N ^ 2), Nat.zero_le (N ^ 3), Nat.zero_le (N ^ 4)]
  have htotalN : work (countD (toRaw C)) ≤ 256 * (N + 1) ^ 3 := by
    have hmul := Nat.mul_le_mul_right (80 * ((N + 1) ^ 2 + 1)) hkN
    nlinarith [Nat.zero_le (N ^ 2), Nat.zero_le (N ^ 3)]
  have p₂ := pow_up N 2 6 (by omega)
  have p₃ := pow_up N 3 6 (by omega)
  have p₄ := pow_up N 4 6 (by omega)
  have p₀ : 1 ≤ (N + 1) ^ 6 := by exact one_le_pow₀ (by omega)
  change _ ≤ 2097152 * (N + 1) ^ 6
  simp only [checkD, materialize_value, work]
  dsimp only [rows] at hrowsN
  unfold work at hmat hpreN hrowsN htotalN hcolumnsN
  omega

end UAVProof.TreeBudgetSparseCheckBounds
