import LeanCompletion.UAV.TreeBudgetSparseCodec
import LeanCompletion.UAV.TreeBudgetBinaryInput
import LeanCompletion.UAV.TreeBudgetCostedCandidates

/-! Specified-route binary input and a compressed signed-integer verifier.
The route-count guard precedes certificate decoding. Runtime loops use actual
vertices and certificate entries; neither m nor an entry count is expanded. -/
namespace UAVProof.TreeBudgetSparseVerifier

open TreeBudgetBinaryCodec TreeBudgetBinaryInput TreeBudgetParentArray
open TreeBudgetVector TreeBudgetVectorChecker TreeBudgetCostedCandidates
open TreeBudgetCertificate TreeBudgetSparseCodec

def encodeSpecified (m : ℕ) (raw : RawInput) : Bits := encodeNat m ++ encodeInput raw

def parseSpecifiedRaw (bits : Bits) : Option (ℕ × RawInput) := do
  let (m, rest) ← parseNat bits
  let raw ← parseInput rest
  pure (m, raw)

@[simp] theorem parseSpecifiedRaw_encode (m : ℕ) (raw : RawInput) (hs : Shape raw) :
    parseSpecifiedRaw (encodeSpecified m raw) = some (m, raw) := by
  simp [parseSpecifiedRaw, encodeSpecified, parseNat_append, parseInput_encode raw hs]

theorem parseSpecifiedRaw_canonical (bits : Bits) (m : ℕ) (raw : RawInput)
    (h : parseSpecifiedRaw bits = some (m, raw)) : bits = encodeSpecified m raw ∧ Shape raw := by
  simp only [parseSpecifiedRaw, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨k, rest⟩, hk, ⟨r, hr, he⟩⟩ := h
  cases he
  obtain ⟨hr', hs⟩ := parseInput_canonical rest raw hr
  exact ⟨by rw [parseNat_canonical bits rest k hk, hr']; rfl, hs⟩

theorem parseSpecifiedRaw_trailing (m : ℕ) (raw : RawInput) (hs : Shape raw)
    (tail : Bits) (ht : tail ≠ []) : parseSpecifiedRaw (encodeSpecified m raw ++ tail) = none := by
  simp [parseSpecifiedRaw, encodeSpecified, List.append_assoc, parseNat_append,
    parseInput_rejects_trailing raw hs tail ht]

structure Instance where
  data : Input
  routes : ℕ
  compatible : routes = (rootCountCost data.parents data.H).value

def decodeSpecified (m : ℕ) (raw : RawInput) : Option Instance := do
  let I ← decodeRaw raw
  if h : m = (rootCountCost I.parents I.H).value then some ⟨I, m, h⟩ else none

def parseInstance (bits : Bits) : Option Instance := do
  let (m, raw) ← parseSpecifiedRaw bits
  decodeSpecified m raw

@[simp] theorem parseInstance_encode (m : ℕ) (raw : RawInput) (hs : Shape raw) :
    parseInstance (encodeSpecified m raw) = decodeSpecified m raw := by
  simp [parseInstance, parseSpecifiedRaw_encode m raw hs]

theorem decodeSpecified_fields (m : ℕ) (raw : RawInput) (I : Instance)
    (h : decodeSpecified m raw = some I) : I.routes = m ∧ decodeRaw raw = some I.data := by
  cases hd : decodeRaw raw with
  | none => simp [decodeSpecified, hd] at h
  | some J =>
    simp only [decodeSpecified, hd, bind, Option.bind_some] at h
    split_ifs at h with hm
    cases h
    exact ⟨rfl, rfl⟩

theorem parseInstance_canonical (bits : Bits) (I : Instance)
    (h : parseInstance bits = some I) :
    ∃ raw, bits = encodeSpecified I.routes raw ∧ Shape raw ∧ decodeRaw raw = some I.data := by
  simp only [parseInstance, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨m, raw⟩, hp, hd⟩ := h
  obtain ⟨he, hs⟩ := parseSpecifiedRaw_canonical bits m raw hp
  obtain ⟨hm, hr⟩ := decodeSpecified_fields m raw I hd
  exact ⟨raw, by simpa only [hm] using he, hs, hr⟩

theorem wrong_routes_rejected (m : ℕ) (raw : RawInput) (J : Input)
    (hd : decodeRaw raw = some J) (hm : m ≠ (rootCountCost J.parents J.H).value) :
    decodeSpecified m raw = none := by simp [decodeSpecified, hd, hm]

theorem malformed_input_rejected (m : ℕ) (raw : RawInput) (hd : decodeRaw raw = none) :
    decodeSpecified m raw = none := by simp [decodeSpecified, hd]

noncomputable def tree (I : Instance) := toRootedTree I.data.parents I.data.valid
def fees (I : Instance) (v : Fin I.data.n) : ℚ :=
  (I.data.numerators[v] : ℚ) / (I.data.denominators[v] : ℚ)
def budget (I : Instance) : ℚ := (I.data.budgetNumerator : ℚ) / (I.data.budgetDenominator : ℚ)

/-- All rows are checked, including rows whose count is zero. -/
def check (I : Instance) (C : Certificate (Fin I.data.n)) : Bool :=
  let A := scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator
  let AT := scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator
  (List.finRange C.size).all (fun i =>
    (rowCheck I.data.parents I.data.H A AT (Vector.ofFn (C.row i))).value) &&
  decide ((List.ofFn C.count).sum = I.routes) &&
  (List.finRange I.data.n).all (fun v => decide (v ≠ I.data.parents.root →
    (List.ofFn (fun i => C.count i * C.row i v)).sum = I.data.H[v]))

theorem check_eq_true_iff (I : Instance) (C : Certificate (Fin I.data.n)) :
    check I C = true ↔
      TreeBudgetCertificate.Valid (tree I) (decode I.data.H) I.routes (fees I) (budget I) C := by
  have hdecode (p : Fin I.data.n → ℕ) : decode (Vector.ofFn p) = p := by
    funext v
    simp [decode]
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq, List.sum_ofFn, rowCheck_value _ I.data.valid,
    rowValidB_scaled_eq_true_iff _ _ _ _ _ _ _ I.data.positive I.data.budgetPositive]
  simp only [TreeBudgetCertificate.Valid, tree, budget, hdecode, toRootedTree_root, and_assoc]
  rfl

def checkWire (I : Instance) (bits : Bits) : Bool :=
  match decodeCertificate I.data.n bits with
  | none => false
  | some C => check I C

theorem checkWire_iff (I : Instance) (bits : Bits) : checkWire I bits = true ↔
    ∃ C : Certificate (Fin I.data.n), decodeCertificate I.data.n bits = some C ∧
      checkCertificate (tree I) (decode I.data.H) I.routes (fees I) (budget I) C = true := by
  cases hd : decodeCertificate I.data.n bits with
  | none => simp [checkWire, hd]
  | some C => simp [checkWire, hd, checkCertificate_eq_true_iff, check_eq_true_iff]

theorem checkWire_encode (I : Instance) (C : Certificate (Fin I.data.n)) :
    checkWire I (encodeCert C) = true ↔
      checkCertificate (tree I) (decode I.data.H) I.routes (fees I) (budget I) C = true := by
  simp [checkWire_iff]

def verify (input certificate : Bits) : Bool :=
  match parseInstance input with
  | none => false
  | some I => checkWire I certificate

/-- Main A3 refinement, for arbitrary input and certificate bitstrings. -/
theorem verify_refines (input certificate : Bits) : verify input certificate = true ↔
    ∃ I : Instance, parseInstance input = some I ∧
      ∃ C : Certificate (Fin I.data.n), decodeCertificate I.data.n certificate = some C ∧
        checkCertificate (tree I) (decode I.data.H) I.routes (fees I) (budget I) C = true := by
  cases hp : parseInstance input with
  | none => simp [verify, hp]
  | some I => simp [verify, hp, checkWire_iff]

theorem verify_parsed_iff (input certificate : Bits) (I : Instance)
    (hp : parseInstance input = some I) : verify input certificate = true ↔
    ∃ C : Certificate (Fin I.data.n), certificate = encodeCert C ∧
      checkCertificate (tree I) (decode I.data.H) I.routes (fees I) (budget I) C = true := by
  simp [verify, hp, checkWire_iff, decodeCertificate_iff]

theorem verify_invalid_input (input certificate : Bits) (hp : parseInstance input = none) :
    verify input certificate = false := by simp [verify, hp]

end UAVProof.TreeBudgetSparseVerifier
