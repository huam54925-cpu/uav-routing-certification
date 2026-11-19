import LeanCompletion.UAV.TreeBudgetSparseCodec
import LeanCompletion.UAV.TreeBudgetCostedParsing
import LeanCompletion.UAV.TreeBudgetSparseVerifier

/-! Executed scan/length/guard/decrement costs for compressed certificate
parsing, including every failure branch. These are reference word costs;
a standard finite-alphabet machine simulation is a separate obligation. -/
namespace UAVProof.TreeBudgetSparseCostedParsing
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetBitMachine
open TreeBudgetBitPrimitives TreeBudgetCostedCodec TreeBudgetCostedParsing

def parseEntryD (input : Bits) : Costed (Option (RawEntry × Bits)) :=
  thenD (parseNatD input) fun (count, rest) =>
    thenD (parseNatsD rest) fun (row, tail) =>
      ⟨some ((count, row), tail), 1, 1⟩

@[simp] theorem parseEntryD_value (input : Bits) :
    (parseEntryD input).value = parseEntry input := by
  simp [parseEntryD, parseEntry]

theorem parseEntryD_steps (input : Bits) :
    (parseEntryD input).steps ≤ 2048 * (input.length + 1) ^ 2 := by
  have hn := parseNatD_steps input
  cases hp : (parseNatD input).value with
  | none => simp only [parseEntryD, thenD, hp]; nlinarith
  | some out =>
    rcases out with ⟨count, rest⟩
    have hl := congrArg List.length (parseNat_canonical input rest count (by simpa using hp))
    simp only [List.length_append] at hl
    have hr : rest.length ≤ input.length := by omega
    have hs := parseNatsD_steps rest
    have hm : (rest.length + 1) ^ 2 ≤ (input.length + 1) ^ 2 := by gcongr
    simp only [parseEntryD, thenD, hp]
    cases (parseNatsD rest).value <;> dsimp only <;> nlinarith

theorem parseEntryD_allocations_le_steps (input : Bits) :
    (parseEntryD input).allocations ≤ (parseEntryD input).steps := by
  apply thenD_allocations_le_steps _ _ (parseNatD_allocations_le_steps _)
  rintro ⟨count, rest⟩ _
  apply thenD_allocations_le_steps _ _ (parseNatsD_allocations_le_steps _)
  rintro ⟨row, tail⟩ _
  exact Nat.le_refl _

/-- A uniform local budget allows the existing counted loop to be used with
quadratic entry parsers. The count must have passed the remaining-length guard. -/
theorem parseManyD_steps_bounded {α : Type} (p : CostParser α)
    (count : ℕ) (input : Bits) (L S : ℕ) (hi : input.length ≤ L) (hc : count ≤ L)
    (hs : ∀ s, s.length ≤ L → (p s).steps ≤ S)
    (hr : ∀ s x rest, (p s).value = some (x, rest) → rest.length ≤ s.length) :
    (parseManyD p count input).steps ≤ (count + 1) * (S + 256 * (L + 1) + 8) := by
  induction count generalizing input with
  | zero =>
    have hz := (dynamic_steps 0 0 L (by simp) (by simp)).1
    change (zeroNatD 0).steps ≤ _ at hz
    rw [parseManyD_zero]
    dsimp only
    nlinarith
  | succ count ih =>
    have hw : (count + 1).size ≤ L := (nat_size_le _).trans hc
    have hz := (dynamic_steps (count + 1) 0 L hw (by simp)).1
    change (zeroNatD (count + 1)).steps ≤ _ at hz
    have hd := (dynamic_steps (count + 1) 1 L hw (by simp; omega)).2.2.1
    have hh := hs input hi
    rw [parseManyD_succ]
    cases hp : (p input).value with
    | none => dsimp only; nlinarith
    | some out =>
      rcases out with ⟨x, rest⟩
      have ht := ih rest ((hr input x rest hp).trans hi) (by omega)
      dsimp only
      nlinarith

theorem parseListD_steps_bounded {α : Type} (p : CostParser α)
    (input : Bits) (L S : ℕ) (hi : input.length ≤ L)
    (hs : ∀ s, s.length ≤ L → (p s).steps ≤ S)
    (hr : ∀ s x rest, (p s).value = some (x, rest) → rest.length ≤ s.length) :
    (parseListD p input).steps ≤ (L + 1) * (S + 1024 * (L + 1)) := by
  have hh := parseNatD_steps input
  cases hp : (parseNatD input).value with
  | none => simp only [parseListD, hp]; nlinarith
  | some out =>
    rcases out with ⟨count, rest⟩
    have hl := congrArg List.length (parseNat_canonical input rest count (by simpa using hp))
    simp only [List.length_append, encodeNat_length] at hl
    have hc : count.size ≤ L := by omega
    have hrest : rest.length ≤ L := by omega
    have hlen := lengthD_steps rest
    have hm : (rest.length + 1) ^ 2 ≤ (L + 1) ^ 2 := by gcongr
    have hf := (dynamic_steps count rest.length L hc ((nat_size_le _).trans hrest)).2.1
    simp only [parseListD, hp, lengthD_value, leNatD_value]
    split_ifs with hfit
    · have hfit' : count ≤ rest.length := by simpa using hfit
      have ht := parseManyD_steps_bounded p count rest L S hrest (hfit'.trans hrest) hs hr
      have hmul : (count + 1) * (S + 256 * (L + 1) + 8) ≤
          (L + 1) * (S + 256 * (L + 1) + 8) := by gcongr; omega
      dsimp only
      nlinarith only [hh, hi, hlen, hm, hf, ht, hmul, Nat.zero_le L]
    · dsimp only
      nlinarith only [hh, hi, hlen, hm, hf, Nat.zero_le L, Nat.zero_le (L * S), Nat.zero_le S]

def parseRawPrefixD : CostParser RawCertificate := parseListD parseEntryD
def parseRawD (input : Bits) : Costed (Option RawCertificate) :=
  thenD (parseRawPrefixD input) fun (xs, rest) =>
    match rest with
    | [] => ⟨some xs, 1, 0⟩
    | _ :: _ => ⟨none, 1, 0⟩

@[simp] theorem parseRawPrefixD_value (input : Bits) :
    (parseRawPrefixD input).value = parseRawPrefix input := by
  simp [parseRawPrefixD, parseRawPrefix]

@[simp] theorem parseRawD_value (input : Bits) : (parseRawD input).value = parseRaw input := by
  simp only [parseRawD, thenD_value, parseRawPrefixD_value, parseRaw]
  cases parseRawPrefix input with
  | none => rfl
  | some out => rcases out with ⟨xs, rest⟩; cases rest <;> rfl

theorem parseRawPrefixD_steps (input : Bits) :
    (parseRawPrefixD input).steps ≤ 3072 * (input.length + 1) ^ 3 := by
  have ht := parseListD_steps_bounded parseEntryD input input.length
    (2048 * (input.length + 1) ^ 2) (by rfl) (fun s hs =>
      (parseEntryD_steps s).trans (by gcongr)) (by
        intro s e rest h
        have hl := congrArg List.length (parseEntry_canonical s rest e (by simpa using h))
        simp only [List.length_append] at hl
        omega)
  change (parseListD parseEntryD input).steps ≤ _
  nlinarith [Nat.zero_le (input.length ^ 3), Nat.zero_le (input.length ^ 2)]

theorem parseRawD_steps (input : Bits) :
    (parseRawD input).steps ≤ 3072 * (input.length + 1) ^ 3 + 2 := by
  have ht := parseRawPrefixD_steps input
  simp only [parseRawD, thenD]
  cases (parseRawPrefixD input).value with
  | none => dsimp only; omega
  | some out => rcases out with ⟨xs, rest⟩; cases rest <;> dsimp only <;> omega

theorem parseRawD_allocations_le_steps (input : Bits) :
    (parseRawD input).allocations ≤ (parseRawD input).steps := by
  apply thenD_allocations_le_steps _ _
    (parseListD_allocations_le_steps _ _ parseEntryD_allocations_le_steps)
  rintro ⟨xs, rest⟩ _
  cases rest <;> simp

/-- Unconditional: includes noncanonical fields, enormous declared lengths,
truncated rows/entries, and trailing-bit rejection. -/
theorem parseRawD_work (input : Bits) :
    (parseRawD input).steps + (parseRawD input).allocations ≤
      6144 * (input.length + 1) ^ 3 + 4 := by
  have := parseRawD_steps input
  have := parseRawD_allocations_le_steps input
  omega

def parseSpecifiedD (input : Bits) : Costed (Option (ℕ × RawInput)) :=
  thenD (parseNatD input) fun (m, rest) =>
    thenD (parseInputD rest) fun raw => ⟨some (m, raw), 1, 1⟩

@[simp] theorem parseSpecifiedD_value (input : Bits) :
    (parseSpecifiedD input).value = TreeBudgetSparseVerifier.parseSpecifiedRaw input := by
  simp [parseSpecifiedD, TreeBudgetSparseVerifier.parseSpecifiedRaw]

theorem parseSpecifiedD_steps (input : Bits) :
    (parseSpecifiedD input).steps ≤ 66048 * (input.length + 1) ^ 2 := by
  have hn := parseNatD_steps input
  cases hp : (parseNatD input).value with
  | none => simp only [parseSpecifiedD, thenD, hp]; nlinarith
  | some out =>
    rcases out with ⟨m, rest⟩
    have hl := congrArg List.length (parseNat_canonical input rest m (by simpa using hp))
    simp only [List.length_append] at hl
    have hr : rest.length ≤ input.length := by omega
    have hs := parseInputD_steps rest
    have hm : (rest.length + 1) ^ 2 ≤ (input.length + 1) ^ 2 := by gcongr
    simp only [parseSpecifiedD, thenD, hp]
    cases (parseInputD rest).value <;> dsimp only <;> nlinarith

theorem parseSpecifiedD_allocations_le_steps (input : Bits) :
    (parseSpecifiedD input).allocations ≤ (parseSpecifiedD input).steps := by
  apply thenD_allocations_le_steps _ _ (parseNatD_allocations_le_steps _)
  rintro ⟨m, rest⟩ _
  apply thenD_allocations_le_steps _ _ (parseInputD_allocations_le_steps _)
  intro raw _
  exact Nat.le_refl _

theorem parseSpecifiedD_work (input : Bits) :
    (parseSpecifiedD input).steps + (parseSpecifiedD input).allocations ≤
      132096 * (input.length + 1) ^ 2 := by
  have := parseSpecifiedD_steps input
  have := parseSpecifiedD_allocations_le_steps input
  omega

end UAVProof.TreeBudgetSparseCostedParsing
