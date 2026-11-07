import LeanCompletion.UAV.TreeBudgetCostedExecution
import LeanCompletion.UAV.TreeBudgetBinaryExecutionBounds
import LeanCompletion.UAV.TreeBudgetBinaryOutputBounds

/-! Uniform intrinsic work of the complete costed evaluator, including binary
input parsing, checked parent arrays, preprocessing, candidates, search and
matrix output. This is an instruction-work profile theorem, not a RAM time or
FPT theorem: identifying all accesses with a bounded reference store remains
a separate refinement obligation. -/
namespace UAVProof.TreeBudgetBinaryTotalWork
open TreeBudgetBinaryInput TreeBudgetBinaryCodec TreeBudgetCostedInput TreeBudgetCostedParsing
open TreeBudgetCostedExecution TreeBudgetBinaryOutput TreeBudgetBinaryPipeline
open TreeBudgetBinaryExecutionBounds TreeBudgetBinaryOutputBounds TreeBudgetCostedCandidates
open TreeBudgetParentArray TreeBudgetVector TreeBudgetMemoBounds TreeBudgetStateParameters

noncomputable def states (J : Input) : ℕ :=
  stateBound (toRootedTree J.parents J.valid)
    (TreeBudgetPatterns.normalize (toRootedTree J.parents J.valid) (decode J.H))

noncomputable def mass (J : Input) : ℕ :=
  totalMultiplicity (toRootedTree J.parents J.valid)
    (TreeBudgetPatterns.normalize (toRootedTree J.parents J.valid) (decode J.H))

noncomputable def support (J : Input) : ℕ :=
  positiveCount (toRootedTree J.parents J.valid)
    (TreeBudgetPatterns.normalize (toRootedTree J.parents J.valid) (decode J.H))

noncomputable def maximum (J : Input) : ℕ :=
  maxMultiplicity (toRootedTree J.parents J.valid)
    (TreeBudgetPatterns.normalize (toRootedTree J.parents J.valid) (decode J.H))

theorem decodeRawCost_work_encoded (I : RawInput) (hs : Shape I) :
    work (decodeRawCost I) ≤ 65536 * ((encodeInput I).length + 1) ^ 3 := by
  let ell := (encodeInput I).length
  have hw := inputWeight_le_length I
  have hn := vertexCount_le_length I hs
  have hp : ∀ p ∈ I.parents, p.size ≤ ell + 1 := by
    intro p hp
    have hb := List.le_sum_of_mem (List.mem_map.mpr ⟨p, hp, rfl⟩ : p.size ∈ I.parents.map Nat.size)
    dsimp [inputWeight] at hw
    omega
  have hd : ∀ d ∈ I.denominators, d.size ≤ ell + 1 := by
    intro d hd
    have hb := List.le_sum_of_mem (List.mem_map.mpr ⟨d, hd, rfl⟩ : d.size ∈ I.denominators.map Nat.size)
    dsimp [inputWeight] at hw
    omega
  have hcost := decodeRawCost_work I hs (ell + 1) (by omega)
    (by dsimp [inputWeight] at hw; omega)
    (by dsimp [inputWeight] at hw; omega) hp hd
    (by dsimp [inputWeight] at hw; omega)
  have hm : (I.n + 1) ^ 2 * (ell + 3) ≤ (ell + 1) ^ 2 * (ell + 3) := by gcongr
  change _ ≤ 65536 * (ell + 1) ^ 3
  nlinarith only [hcost, hm, Nat.zero_le (ell ^ 3), Nat.zero_le (ell ^ 2)]

theorem total_envelope (ell S parser validator prepared output : ℕ)
    (hp : parser ≤ 65536 * (ell + 1) ^ 2)
    (hv : validator ≤ 65536 * (ell + 1) ^ 3)
    (hs : prepared ≤ 500000 * (ell + 1) ^ 4 * (S + 1) ^ 3)
    (ho : output ≤ 1024 * (ell + 1) ^ 3 * (S + 1) ^ 2) :
    parser + validator + prepared + output + 4 ≤
      1048576 * (ell + 1) ^ 4 * (S + 1) ^ 3 := by
  have h2 : (ell + 1) ^ 2 ≤ (ell + 1) ^ 4 := by nlinarith
  have h3 : (ell + 1) ^ 3 ≤ (ell + 1) ^ 4 := by nlinarith
  have hS : (S + 1) ^ 2 ≤ (S + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hS1 : 1 ≤ (S + 1) ^ 3 := by
    have hpos : 0 < (S + 1) ^ 3 := by positivity
    omega
  have a := Nat.mul_le_mul h2 hS1
  have b := Nat.mul_le_mul h3 hS1
  have c := Nat.mul_le_mul h3 hS
  have d : 1 ≤ (ell + 1) ^ 4 * (S + 1) ^ 3 := by
    have hpos : 0 < (ell + 1) ^ 4 * (S + 1) ^ 3 := by positivity
    omega
  nlinarith only [hp, hv, hs, ho, a, b, c, d]

set_option maxRecDepth 4096 in
/-- No phase-cost bound is a hypothesis; both hypotheses are checked decoding
equations for the actual input. The size is the length of that input. -/
theorem execute_steps (bits : Bits) (I : RawInput) (J : Input)
    (hp : parseInput bits = some I) (hj : decodeRaw I = some J) :
    (execute bits).steps ≤ 1048576 * (bits.length + 1) ^ 4 * (states J + 1) ^ 3 := by
  have hcanon := parseInput_canonical bits I hp
  have hparser := parseInputD_steps bits
  have hvalidator := decodeRawCost_work_encoded I hcanon.2
  have hprepared := preparedSearch_work I J hj
  have houtput := preparedSearch_output_steps I J hj
  rw [← hcanon.1] at hvalidator hprepared houtput
  have hvalidator' := (Nat.le_add_right (decodeRawCost I).steps
    (decodeRawCost I).allocations).trans hvalidator
  have he := total_envelope bits.length (states J) _ _ _ _ hparser hvalidator' hprepared houtput
  simpa only [execute, parseInputD_value, hp, executeRaw, decodeRawCost_value, hj,
    executeChecked, executeInput, Nat.add_assoc] using he

theorem states_positive (J : Input) : 1 ≤ states J := by
  exact (Nat.le_add_left 1 (mass J)).trans (totalMultiplicity_add_one_le_stateBound _ _)

theorem cube_add_one_le (S : ℕ) (hS : 1 ≤ S) : (S + 1) ^ 3 ≤ 8 * S ^ 3 := by
  have h : S + 1 ≤ 2 * S := by omega
  have hp := Nat.pow_le_pow_left h 3
  nlinarith only [hp]

theorem execute_steps_state_cube (bits : Bits) (I : RawInput) (J : Input)
    (hp : parseInput bits = some I) (hj : decodeRaw I = some J) :
    (execute bits).steps ≤ 8388608 * (states J) ^ 3 * (bits.length + 1) ^ 4 := by
  have h := execute_steps bits I J hp hj
  have hc := Nat.mul_le_mul_left (1048576 * (bits.length + 1) ^ 4)
    (cube_add_one_le (states J) (states_positive J))
  exact h.trans (by convert hc using 1; ring)

/-- Parameter substitution for intrinsic work; not yet a machine-time FPT claim. -/
theorem execute_steps_mass (bits : Bits) (I : RawInput) (J : Input)
    (hp : parseInput bits = some I) (hj : decodeRaw I = some J) :
    (execute bits).steps ≤ 8388608 * 2 ^ (3 * mass J) * (bits.length + 1) ^ 4 := by
  have h := execute_steps_state_cube bits I J hp hj
  have hS : states J ≤ 2 ^ mass J := stateBound_le_two_pow_totalMultiplicity _ _
  have hc := Nat.mul_le_mul_right ((bits.length + 1) ^ 4)
    (Nat.mul_le_mul_left 8388608 (Nat.pow_le_pow_left hS 3))
  exact h.trans (by simpa only [← pow_mul, Nat.mul_comm (mass J) 3] using hc)

theorem execute_steps_support_maximum (bits : Bits) (I : RawInput) (J : Input)
    (hp : parseInput bits = some I) (hj : decodeRaw I = some J) :
    (execute bits).steps ≤ 8388608 * (maximum J + 1) ^ (3 * support J) * (bits.length + 1) ^ 4 := by
  have h := execute_steps_state_cube bits I J hp hj
  have hS : states J ≤ (maximum J + 1) ^ support J :=
    stateBound_le_maxMultiplicity_pow_positiveCount _ _
  have hc := Nat.mul_le_mul_right ((bits.length + 1) ^ 4)
    (Nat.mul_le_mul_left 8388608 (Nat.pow_le_pow_left hS 3))
  exact h.trans (by simpa only [← pow_mul, Nat.mul_comm (support J) 3] using hc)

end UAVProof.TreeBudgetBinaryTotalWork
