import LeanCompletion.UAV.TreeBudgetCostedCodec

/-! Counted parsers execute binary zero tests and decrements. List counts are
checked against the scanned remaining input length before entering the loop. -/
namespace UAVProof.TreeBudgetCostedParsing
set_option maxRecDepth 4096
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetBinaryCodec TreeBudgetCostedCodec

abbrev CostParser (α : Type) := Bits → Costed (Option (α × Bits))

def parseManyD {α : Type} (p : CostParser α) (count : ℕ) (input : Bits) :
    Costed (Option (List α × Bits)) :=
  let test := zeroNatD count
  if hzero : test.value then ⟨some ([], input), test.steps + 1, test.allocations⟩ else
    let head := p input
    match head.value with
    | none => ⟨none, test.steps + head.steps + 2, test.allocations + head.allocations⟩
    | some (x, rest) =>
      let dec := subNatD count 1
      let tail := parseManyD p dec.value rest
      ⟨tail.value.map (fun out => (x :: out.1, out.2)),
        test.steps + head.steps + dec.steps + tail.steps + 3,
        test.allocations + head.allocations + dec.allocations + tail.allocations + 1⟩
termination_by count
decreasing_by
  simp_wf
  have hz : count ≠ 0 := by
    simpa only [test, zeroNatD_value, decide_eq_true_eq] using hzero
  omega

theorem parseManyD_zero {α : Type} (p : CostParser α) (input : Bits) :
    parseManyD p 0 input = ⟨some ([], input), (zeroNatD 0).steps + 1,
      (zeroNatD 0).allocations⟩ := by rw [parseManyD]; simp only [zeroNatD_value]; rfl

theorem parseManyD_succ {α : Type} (p : CostParser α) (count : ℕ) (input : Bits) :
    parseManyD p (count + 1) input =
      match (p input).value with
      | none => ⟨none, (zeroNatD (count + 1)).steps + (p input).steps + 2,
          (zeroNatD (count + 1)).allocations + (p input).allocations⟩
      | some (x, rest) =>
        ⟨(parseManyD p count rest).value.map (fun out => (x :: out.1, out.2)),
          (zeroNatD (count + 1)).steps + (p input).steps +
            (subNatD (count + 1) 1).steps + (parseManyD p count rest).steps + 3,
          (zeroNatD (count + 1)).allocations + (p input).allocations +
            (subNatD (count + 1) 1).allocations + (parseManyD p count rest).allocations + 1⟩ := by
  rw [parseManyD]
  simp only [zeroNatD_value, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    decide_false, Bool.false_eq_true, ↓reduceDIte, subNatD_value, Nat.add_sub_cancel]

@[simp] theorem parseManyD_value {α : Type} (p : CostParser α) (count : ℕ) (input : Bits) :
    (parseManyD p count input).value = parseMany (fun s => (p s).value) count input := by
  induction count generalizing input with
  | zero => rw [parseManyD_zero]; rfl
  | succ count ih =>
    rw [parseManyD_succ]
    cases hp : (p input).value with
    | none => simp [parseMany, hp]
    | some out =>
      rcases out with ⟨x, rest⟩
      simp only [ih, parseMany, hp, Bind.bind, Option.bind_some]
      cases parseMany (fun s => (p s).value) count rest <;> rfl

theorem parseManyD_steps {α : Type} (p : CostParser α) (count : ℕ) (input : Bits) (L K : ℕ)
    (hi : input.length ≤ L) (hc : count ≤ L)
    (hs : ∀ s, (p s).steps ≤ K * (s.length + 1))
    (hr : ∀ s x rest, (p s).value = some (x, rest) → rest.length ≤ s.length) :
    (parseManyD p count input).steps ≤ (count + 1) * (K * (L + 1) + 256 * (L + 1) + 8) := by
  induction count generalizing input with
  | zero =>
    have hz := (dynamic_steps 0 0 L (by simp) (by simp)).1
    rw [parseManyD_zero]
    change (zeroNatD 0).steps ≤ _ at hz
    dsimp only
    nlinarith
  | succ count ih =>
    have hc' : count ≤ L := by omega
    have hw : (count + 1).size ≤ L := (nat_size_le _).trans hc
    have hz := (dynamic_steps (count + 1) 0 L hw (by simp)).1
    change (zeroNatD (count + 1)).steps ≤ _ at hz
    have hd := (dynamic_steps (count + 1) 1 L hw (by simp; omega)).2.2.1
    have hh := (hs input).trans (Nat.mul_le_mul_left K (by omega : input.length + 1 ≤ L + 1))
    rw [parseManyD_succ]
    cases hp : (p input).value with
    | none => dsimp only; nlinarith
    | some out =>
      rcases out with ⟨x, rest⟩
      have ht := ih rest ((hr input x rest hp).trans hi) hc'
      dsimp only
      nlinarith

theorem parseManyD_allocations_le_steps {α : Type} (p : CostParser α) (count : ℕ)
    (input : Bits) (h : ∀ s, (p s).allocations ≤ (p s).steps) :
    (parseManyD p count input).allocations ≤ (parseManyD p count input).steps := by
  induction count generalizing input with
  | zero =>
    have hz := (dynamic_allocations_le_steps 0 0).1
    rw [parseManyD_zero]
    change (zeroNatD 0).allocations ≤ (zeroNatD 0).steps at hz
    dsimp only
    omega
  | succ count ih =>
    have hz := (dynamic_allocations_le_steps (count + 1) 0).1
    change (zeroNatD (count + 1)).allocations ≤ (zeroNatD (count + 1)).steps at hz
    have hd := (dynamic_allocations_le_steps (count + 1) 1).2.2.1
    have hh := h input
    rw [parseManyD_succ]
    cases hp : (p input).value with
    | none => dsimp only; omega
    | some out =>
      rcases out with ⟨x, rest⟩
      have ht := ih rest
      dsimp only
      omega

def parseListD {α : Type} (p : CostParser α) (input : Bits) :
    Costed (Option (List α × Bits)) :=
  let head := parseNatD input
  match head.value with
  | none => ⟨none, head.steps + 1, head.allocations⟩
  | some (count, rest) =>
    let len := lengthD rest
    let fits := leNatD count len.value
    if fits.value then
      let out := parseManyD p count rest
      ⟨out.value, head.steps + len.steps + fits.steps + out.steps + 2,
        head.allocations + len.allocations + fits.allocations + out.allocations⟩
    else ⟨none, head.steps + len.steps + fits.steps + 2,
      head.allocations + len.allocations + fits.allocations⟩

@[simp] theorem parseListD_value {α : Type} (p : CostParser α) (input : Bits) :
    (parseListD p input).value = parseList (fun s => (p s).value) input := by
  simp only [parseListD, parseNatD_value]
  cases hp : parseNat input with
  | none => simp [parseList, hp]
  | some out =>
    rcases out with ⟨count, rest⟩
    simp only [parseList, hp, lengthD_value, leNatD_value, parseManyD_value,
      Bind.bind, Option.bind_some]
    by_cases h : count ≤ rest.length <;> simp [h]

theorem parseListD_steps {α : Type} (p : CostParser α) (input : Bits) (K : ℕ)
    (hs : ∀ s, (p s).steps ≤ K * (s.length + 1))
    (hr : ∀ s x rest, (p s).value = some (x, rest) → rest.length ≤ s.length) :
    (parseListD p input).steps ≤ (K + 1024) * (input.length + 1) ^ 2 := by
  have hh := parseNatD_steps input
  cases hp : (parseNatD input).value with
  | none => simp only [parseListD, hp]; nlinarith
  | some out =>
    rcases out with ⟨count, rest⟩
    have he := parseNat_canonical input rest count (by simpa using hp)
    have hl := congrArg List.length he
    simp only [List.length_append, encodeNat_length] at hl
    have hc : count.size ≤ input.length := by omega
    have hrlen : rest.length ≤ input.length := by omega
    have hlen := lengthD_steps rest
    have hlen' : (rest.length + 1) ^ 2 ≤ (input.length + 1) ^ 2 := by gcongr
    have hfits := (dynamic_steps count rest.length input.length hc
      ((nat_size_le _).trans hrlen)).2.1
    simp only [parseListD, hp, lengthD_value, leNatD_value]
    split_ifs with hfit
    · have hfit' : count ≤ rest.length := by simpa using hfit
      have hm := parseManyD_steps p count rest input.length K hrlen (hfit'.trans hrlen) hs hr
      have hmul : (count + 1) * (K * (input.length + 1) + 256 * (input.length + 1) + 8) ≤
          (input.length + 1) * (K * (input.length + 1) + 256 * (input.length + 1) + 8) := by
        exact Nat.mul_le_mul_right _ (by omega)
      dsimp only
      nlinarith only [hh, hlen, hlen', hfits, hm, hmul,
        Nat.zero_le input.length, Nat.zero_le (input.length ^ 2)]
    · dsimp only
      nlinarith only [hh, hlen, hlen', hfits, Nat.zero_le input.length,
        Nat.zero_le (input.length ^ 2), Nat.zero_le (K * (input.length + 1) ^ 2)]

theorem parseListD_allocations_le_steps {α : Type} (p : CostParser α) (input : Bits)
    (h : ∀ s, (p s).allocations ≤ (p s).steps) :
    (parseListD p input).allocations ≤ (parseListD p input).steps := by
  have hh := parseNatD_allocations_le_steps input
  cases hp : (parseNatD input).value with
  | none => simp only [parseListD, hp]; omega
  | some out =>
    rcases out with ⟨count, rest⟩
    have hl := lengthD_allocations_le_steps rest
    have hf := (dynamic_allocations_le_steps count (lengthD rest).value).2.1
    have hm := parseManyD_allocations_le_steps p count rest h
    simp only [parseListD, hp]
    split_ifs <;> dsimp only <;> omega

def parseNatsD : CostParser (List ℕ) := parseListD parseNatD
def parseIntsD : CostParser (List ℤ) := parseListD parseIntD

@[simp] theorem parseNatsD_value (input : Bits) : (parseNatsD input).value = parseNats input := by
  simp [parseNatsD]

@[simp] theorem parseIntsD_value (input : Bits) : (parseIntsD input).value = parseInts input := by
  simp [parseIntsD]

theorem parseNatsD_steps (input : Bits) :
    (parseNatsD input).steps ≤ 1088 * (input.length + 1) ^ 2 := by
  apply parseListD_steps parseNatD input 64 parseNatD_steps
  intro s n rest h
  have hc := congrArg List.length (parseNat_canonical s rest n (by simpa using h))
  simp only [List.length_append] at hc
  omega

theorem parseIntsD_steps (input : Bits) :
    (parseIntsD input).steps ≤ 1280 * (input.length + 1) ^ 2 := by
  apply parseListD_steps parseIntD input 256 parseIntD_steps
  intro s n rest h
  have hc := congrArg List.length (parseInt_canonical s rest n (by simpa using h))
  simp only [List.length_append] at hc
  omega

theorem parseNatsD_allocations_le_steps (input : Bits) :
    (parseNatsD input).allocations ≤ (parseNatsD input).steps :=
  parseListD_allocations_le_steps _ _ parseNatD_allocations_le_steps

theorem parseIntsD_allocations_le_steps (input : Bits) :
    (parseIntsD input).allocations ≤ (parseIntsD input).steps :=
  parseListD_allocations_le_steps _ _ parseIntD_allocations_le_steps

def thenD {α β : Type} (out : Costed (Option α)) (f : α → Costed (Option β)) :
    Costed (Option β) :=
  match out.value with
  | none => ⟨none, out.steps + 1, out.allocations⟩
  | some x =>
    let next := f x
    ⟨next.value, out.steps + next.steps + 1, out.allocations + next.allocations⟩

@[simp] theorem thenD_value {α β : Type} (out : Costed (Option α))
    (f : α → Costed (Option β)) :
    (thenD out f).value = out.value.bind (fun x => (f x).value) := by
  cases h : out.value <;> simp [thenD, h]

theorem thenD_budget {α β : Type} (out : Costed (Option α))
    (f : α → Costed (Option β)) (Q k : ℕ)
    (ho : out.steps ≤ 2048 * Q)
    (hf : ∀ x, out.value = some x → (f x).steps ≤ k * (2048 * Q) + k) :
    (thenD out f).steps ≤ (k + 1) * (2048 * Q) + (k + 1) := by
  cases h : out.value with
  | none => simp only [thenD, h]; nlinarith
  | some x =>
    have hx := hf x h
    simp only [thenD, h]
    nlinarith

theorem thenD_allocations_le_steps {α β : Type} (out : Costed (Option α))
    (f : α → Costed (Option β))
    (ho : out.allocations ≤ out.steps)
    (hf : ∀ x, out.value = some x → (f x).allocations ≤ (f x).steps) :
    (thenD out f).allocations ≤ (thenD out f).steps := by
  cases h : out.value with
  | none => simp only [thenD, h]; omega
  | some x =>
    have hx := hf x h
    simp only [thenD, h]
    omega

def shapeD (I : RawInput) : Costed Bool :=
  let p := lengthD I.parents
  let m := lengthD I.multiplicities
  let a := lengthD I.numerators
  let b := lengthD I.denominators
  let ep := eqNatD p.value I.n
  let em := eqNatD m.value I.n
  let ea := eqNatD a.value I.n
  let eb := eqNatD b.value I.n
  ⟨ep.value && em.value && ea.value && eb.value,
    p.steps + m.steps + a.steps + b.steps + ep.steps + em.steps + ea.steps + eb.steps + 4,
    p.allocations + m.allocations + a.allocations + b.allocations +
      ep.allocations + em.allocations + ea.allocations + eb.allocations⟩

@[simp] theorem shapeD_value (I : RawInput) : (shapeD I).value = decide (Shape I) := by
  simp [shapeD, Shape, Bool.and_assoc]

theorem shapeD_steps (I : RawInput) (L : ℕ) (hn : I.n.size ≤ L)
    (hp : I.parents.length ≤ L) (hm : I.multiplicities.length ≤ L)
    (ha : I.numerators.length ≤ L) (hb : I.denominators.length ≤ L) :
    (shapeD I).steps ≤ 1024 * (L + 1) ^ 2 := by
  have lp := lengthD_steps I.parents
  have lm := lengthD_steps I.multiplicities
  have la := lengthD_steps I.numerators
  have lb := lengthD_steps I.denominators
  have lps : (I.parents.length + 1) ^ 2 ≤ (L + 1) ^ 2 := by gcongr
  have lms : (I.multiplicities.length + 1) ^ 2 ≤ (L + 1) ^ 2 := by gcongr
  have las : (I.numerators.length + 1) ^ 2 ≤ (L + 1) ^ 2 := by gcongr
  have lbs : (I.denominators.length + 1) ^ 2 ≤ (L + 1) ^ 2 := by gcongr
  have ep := (dynamic_steps I.parents.length I.n L ((nat_size_le _).trans hp) hn).1
  have em := (dynamic_steps I.multiplicities.length I.n L ((nat_size_le _).trans hm) hn).1
  have ea := (dynamic_steps I.numerators.length I.n L ((nat_size_le _).trans ha) hn).1
  have eb := (dynamic_steps I.denominators.length I.n L ((nat_size_le _).trans hb) hn).1
  simp only [shapeD, lengthD_value]
  nlinarith

theorem shapeD_allocations_le_steps (I : RawInput) :
    (shapeD I).allocations ≤ (shapeD I).steps := by
  have lp := lengthD_allocations_le_steps I.parents
  have lm := lengthD_allocations_le_steps I.multiplicities
  have la := lengthD_allocations_le_steps I.numerators
  have lb := lengthD_allocations_le_steps I.denominators
  have ep := (dynamic_allocations_le_steps (lengthD I.parents).value I.n).1
  have em := (dynamic_allocations_le_steps (lengthD I.multiplicities).value I.n).1
  have ea := (dynamic_allocations_le_steps (lengthD I.numerators).value I.n).1
  have eb := (dynamic_allocations_le_steps (lengthD I.denominators).value I.n).1
  simp only [shapeD]
  omega

def finishRawD (I : RawInput) (rest : Bits) : Costed (Option (RawInput × Bits)) :=
  let good := shapeD I
  ⟨if good.value then some (I, rest) else none, good.steps + 9, good.allocations + 8⟩

@[simp] theorem finishRawD_value (I : RawInput) (rest : Bits) :
    (finishRawD I rest).value = if Shape I then some (I, rest) else none := by
  simp [finishRawD]

def parseInputPrefixD (input : Bits) : Costed (Option (RawInput × Bits)) :=
  thenD (parseNatD input) fun (n, s₁) =>
  thenD (parseNatD s₁) fun (root, s₂) =>
  thenD (parseNatsD s₂) fun (parents, s₃) =>
  thenD (parseNatsD s₃) fun (multiplicities, s₄) =>
  thenD (parseIntsD s₄) fun (numerators, s₅) =>
  thenD (parseNatsD s₅) fun (denominators, s₆) =>
  thenD (parseIntD s₆) fun (budgetNumerator, s₇) =>
  thenD (parseNatD s₇) fun (budgetDenominator, rest) =>
  finishRawD ⟨n, root, parents, multiplicities, numerators, denominators,
    budgetNumerator, budgetDenominator⟩ rest

@[simp] theorem parseInputPrefixD_value (input : Bits) :
    (parseInputPrefixD input).value = parseInputPrefix input := by
  simp only [parseInputPrefixD, thenD_value, parseNatD_value, parseNatsD_value,
    parseIntsD_value, parseIntD_value, finishRawD_value, parseInputPrefix, Bind.bind]

theorem nat_result_bounds (input rest : Bits) (n : ℕ)
    (h : (parseNatD input).value = some (n, rest)) :
    n.size ≤ input.length ∧ rest.length ≤ input.length := by
  have hc := congrArg List.length (parseNat_canonical input rest n (by simpa using h))
  simp only [List.length_append, encodeNat_length] at hc
  omega

theorem nats_result_bounds (input rest : Bits) (xs : List ℕ)
    (h : (parseNatsD input).value = some (xs, rest)) :
    xs.length ≤ input.length ∧ rest.length ≤ input.length := by
  have hp : parseNats input = some (xs, rest) := by simpa using h
  have hl := parseList_output_length_le parseNat input xs rest hp
  have hc := congrArg List.length
    (parseList_canonical encodeNat parseNat parseNat_canonical input rest xs hp)
  simp only [List.length_append] at hc
  exact ⟨hl, by omega⟩

theorem ints_result_bounds (input rest : Bits) (xs : List ℤ)
    (h : (parseIntsD input).value = some (xs, rest)) :
    xs.length ≤ input.length ∧ rest.length ≤ input.length := by
  have hp : parseInts input = some (xs, rest) := by simpa using h
  have hl := parseList_output_length_le parseInt input xs rest hp
  have hc := congrArg List.length
    (parseList_canonical encodeInt parseInt parseInt_canonical input rest xs hp)
  simp only [List.length_append] at hc
  exact ⟨hl, by omega⟩

theorem int_result_rest (input rest : Bits) (z : ℤ)
    (h : (parseIntD input).value = some (z, rest)) : rest.length ≤ input.length := by
  have hc := congrArg List.length (parseInt_canonical input rest z (by simpa using h))
  simp only [List.length_append] at hc
  omega

theorem nat_cap (input : Bits) (L : ℕ) (h : input.length ≤ L) :
    (parseNatD input).steps ≤ 2048 * (L + 1) ^ 2 := by
  have hp := parseNatD_steps input
  nlinarith

theorem int_cap (input : Bits) (L : ℕ) (h : input.length ≤ L) :
    (parseIntD input).steps ≤ 2048 * (L + 1) ^ 2 := by
  have hp := parseIntD_steps input
  nlinarith

theorem nats_cap (input : Bits) (L : ℕ) (h : input.length ≤ L) :
    (parseNatsD input).steps ≤ 2048 * (L + 1) ^ 2 := by
  have hp := parseNatsD_steps input
  have hs : (input.length + 1) ^ 2 ≤ (L + 1) ^ 2 := by gcongr
  nlinarith

theorem ints_cap (input : Bits) (L : ℕ) (h : input.length ≤ L) :
    (parseIntsD input).steps ≤ 2048 * (L + 1) ^ 2 := by
  have hp := parseIntsD_steps input
  have hs : (input.length + 1) ^ 2 ≤ (L + 1) ^ 2 := by gcongr
  nlinarith

theorem parseInputPrefixD_steps (input : Bits) :
    (parseInputPrefixD input).steps ≤ 32768 * (input.length + 1) ^ 2 := by
  let L := input.length
  have hQ : 0 < (input.length + 1) ^ 2 := by positivity
  suffices h : (parseInputPrefixD input).steps ≤ 9 * (2048 * (L + 1) ^ 2) + 9 by
    dsimp [L] at h
    omega
  unfold parseInputPrefixD
  apply thenD_budget _ _ ((L + 1) ^ 2) 8 (nat_cap _ _ (by rfl))
  rintro ⟨n, s₁⟩ h₁
  have b₁ := nat_result_bounds input s₁ n h₁
  have l₁ : s₁.length ≤ L := b₁.2
  apply thenD_budget _ _ ((L + 1) ^ 2) 7 (nat_cap _ _ l₁)
  rintro ⟨root, s₂⟩ h₂
  have l₂ := (nat_result_bounds s₁ s₂ root h₂).2.trans l₁
  apply thenD_budget _ _ ((L + 1) ^ 2) 6 (nats_cap _ _ l₂)
  rintro ⟨parents, s₃⟩ h₃
  have b₃ := nats_result_bounds s₂ s₃ parents h₃
  have l₃ := b₃.2.trans l₂
  apply thenD_budget _ _ ((L + 1) ^ 2) 5 (nats_cap _ _ l₃)
  rintro ⟨multiplicities, s₄⟩ h₄
  have b₄ := nats_result_bounds s₃ s₄ multiplicities h₄
  have l₄ := b₄.2.trans l₃
  apply thenD_budget _ _ ((L + 1) ^ 2) 4 (ints_cap _ _ l₄)
  rintro ⟨numerators, s₅⟩ h₅
  have b₅ := ints_result_bounds s₄ s₅ numerators h₅
  have l₅ := b₅.2.trans l₄
  apply thenD_budget _ _ ((L + 1) ^ 2) 3 (nats_cap _ _ l₅)
  rintro ⟨denominators, s₆⟩ h₆
  have b₆ := nats_result_bounds s₅ s₆ denominators h₆
  have l₆ := b₆.2.trans l₅
  apply thenD_budget _ _ ((L + 1) ^ 2) 2 (int_cap _ _ l₆)
  rintro ⟨budgetNumerator, s₇⟩ h₇
  have l₇ := (int_result_rest s₆ s₇ budgetNumerator h₇).trans l₆
  apply thenD_budget _ _ ((L + 1) ^ 2) 1 (nat_cap _ _ l₇)
  rintro ⟨budgetDenominator, rest⟩ _
  have hshape := shapeD_steps
    ⟨n, root, parents, multiplicities, numerators, denominators, budgetNumerator, budgetDenominator⟩
    L b₁.1 (b₃.1.trans l₂) (b₄.1.trans l₃) (b₅.1.trans l₄) (b₆.1.trans l₅)
  simp only [finishRawD]
  nlinarith

theorem parseInputPrefixD_allocations_le_steps (input : Bits) :
    (parseInputPrefixD input).allocations ≤ (parseInputPrefixD input).steps := by
  unfold parseInputPrefixD
  apply thenD_allocations_le_steps _ _ (parseNatD_allocations_le_steps _)
  rintro ⟨n, s₁⟩ _
  apply thenD_allocations_le_steps _ _ (parseNatD_allocations_le_steps _)
  rintro ⟨root, s₂⟩ _
  apply thenD_allocations_le_steps _ _ (parseNatsD_allocations_le_steps _)
  rintro ⟨parents, s₃⟩ _
  apply thenD_allocations_le_steps _ _ (parseNatsD_allocations_le_steps _)
  rintro ⟨multiplicities, s₄⟩ _
  apply thenD_allocations_le_steps _ _ (parseIntsD_allocations_le_steps _)
  rintro ⟨numerators, s₅⟩ _
  apply thenD_allocations_le_steps _ _ (parseNatsD_allocations_le_steps _)
  rintro ⟨denominators, s₆⟩ _
  apply thenD_allocations_le_steps _ _ (parseIntD_allocations_le_steps _)
  rintro ⟨budgetNumerator, s₇⟩ _
  apply thenD_allocations_le_steps _ _ (parseNatD_allocations_le_steps _)
  rintro ⟨budgetDenominator, rest⟩ _
  have hs := shapeD_allocations_le_steps
    ⟨n, root, parents, multiplicities, numerators, denominators, budgetNumerator, budgetDenominator⟩
  simp only [finishRawD]
  omega

def parseInputD (input : Bits) : Costed (Option RawInput) :=
  thenD (parseInputPrefixD input) fun (I, rest) =>
    match rest with
    | [] => ⟨some I, 1, 0⟩
    | _ :: _ => ⟨none, 1, 0⟩

@[simp] theorem parseInputD_value (input : Bits) : (parseInputD input).value = parseInput input := by
  simp only [parseInputD, thenD_value, parseInputPrefixD_value, parseInput, Bind.bind]
  congr 1
  funext out
  rcases out with ⟨I, rest⟩
  cases rest <;> simp

theorem parseInputD_steps (input : Bits) :
    (parseInputD input).steps ≤ 65536 * (input.length + 1) ^ 2 := by
  have hp := parseInputPrefixD_steps input
  have hQ : 0 < (input.length + 1) ^ 2 := by positivity
  unfold parseInputD thenD
  cases h : (parseInputPrefixD input).value with
  | none => dsimp only; omega
  | some out =>
    rcases out with ⟨I, rest⟩
    cases rest <;> dsimp only <;> omega

theorem parseInputD_allocations_le_steps (input : Bits) :
    (parseInputD input).allocations ≤ (parseInputD input).steps := by
  apply thenD_allocations_le_steps _ _ (parseInputPrefixD_allocations_le_steps _)
  rintro ⟨I, rest⟩ _
  cases rest <;> simp

theorem parseInputD_encode (I : RawInput) (h : Shape I) :
    (parseInputD (encodeInput I)).value = some I := by simp [parseInput_encode I h]

end UAVProof.TreeBudgetCostedParsing
