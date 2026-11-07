import LeanCompletion.UAV.TreeBudgetBitPrimitives
import LeanCompletion.UAV.TreeBudgetBinaryCodec

/-! Costed wire routines. The counters are accumulated by digit extraction,
framing writes, binary length increments, and copying append loops. -/
namespace UAVProof.TreeBudgetCostedCodec
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetBinaryCodec

theorem nat_size_le (a : ℕ) : a.size ≤ a := Nat.size_le.mpr a.lt_two_pow_self

def bitsNatD (a : ℕ) : Costed Bits :=
  if a = 0 then ⟨[], 1, 0⟩ else
    let out := bitsNatD (a / 2)
    ⟨a.bodd :: out.value, out.steps + 3, out.allocations + 1⟩
termination_by a

theorem bitsNatD_spec (a : ℕ) :
    (bitsNatD a).value = a.bits ∧ (bitsNatD a).steps = 3 * a.size + 1 ∧
      (bitsNatD a).allocations = a.size := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases hz : a = 0
    · subst a; simp [bitsNatD]
    · have ha : a / 2 < a := Nat.div_lt_self (by omega) (by omega)
      have hh := ih (a / 2) ha
      have hb : a / 2 = 0 → a.bodd = true := by
        intro ht
        have he := Nat.bit_bodd_div2 a
        rw [Nat.div2_val, ht] at he
        cases h : a.bodd <;> simp_all
      have hs : a.size = (a / 2).size + 1 := by
        have hne : Nat.bit a.bodd a.div2 ≠ 0 := by simpa using hz
        have ht := Nat.size_bit hne
        rw [Nat.bit_bodd_div2, Nat.div2_val] at ht
        exact ht
      have hbits : a.bits = a.bodd :: (a / 2).bits := by
        have h := Nat.bits_append_bit (a / 2) a.bodd hb
        simpa only [← Nat.div2_val, Nat.bit_bodd_div2] using h
      have he : bitsNatD a = ⟨a.bodd :: (bitsNatD (a / 2)).value,
          (bitsNatD (a / 2)).steps + 3, (bitsNatD (a / 2)).allocations + 1⟩ := by
        rw [bitsNatD, if_neg hz]
      simp only [he, hh.1, hh.2.1, hh.2.2, hs, hbits]
      simp only [true_and, and_true]
      ring

def wordD : Bits → Costed Bits
  | [] => ⟨[false], 1, 1⟩
  | b :: bs =>
    let out := wordD bs
    ⟨true :: b :: out.value, out.steps + 4, out.allocations + 2⟩

@[simp] theorem wordD_value (bs : Bits) : (wordD bs).value = word bs := by
  induction bs <;> simp [wordD, word, *]

@[simp] theorem wordD_steps (bs : Bits) : (wordD bs).steps = 4 * bs.length + 1 := by
  induction bs <;> simp [wordD, *] <;> omega

@[simp] theorem wordD_allocations (bs : Bits) :
    (wordD bs).allocations = 2 * bs.length + 1 := by
  induction bs <;> simp [wordD, *] <;> omega

def encodeNatD (a : ℕ) : Costed Bits :=
  let bs := bitsNatD a
  let out := wordD bs.value
  ⟨out.value, bs.steps + out.steps + 1, bs.allocations + out.allocations⟩

@[simp] theorem encodeNatD_value (a : ℕ) : (encodeNatD a).value = encodeNat a := by
  simp [encodeNatD, (bitsNatD_spec a).1, encodeNat]

theorem encodeNatD_steps (a : ℕ) : (encodeNatD a).steps ≤ 8 * (a.size + 1) := by
  simp only [encodeNatD, (bitsNatD_spec a).1, (bitsNatD_spec a).2.1, wordD_steps,
    ← Nat.size_eq_bits_len]
  omega

theorem encodeNatD_allocations_le_steps (a : ℕ) :
    (encodeNatD a).allocations ≤ (encodeNatD a).steps := by
  simp only [encodeNatD, (bitsNatD_spec a).1, (bitsNatD_spec a).2.1,
    (bitsNatD_spec a).2.2, wordD_steps, wordD_allocations, ← Nat.size_eq_bits_len]
  omega

def encodeIntD (a : ℤ) : Costed Bits :=
  let out := encodeNatD a.natAbs
  ⟨decide (a < 0) :: out.value, out.steps + 1, out.allocations + 1⟩

@[simp] theorem encodeIntD_value (a : ℤ) : (encodeIntD a).value = encodeInt a := by
  simp [encodeIntD, encodeInt]

theorem encodeIntD_steps (a : ℤ) : (encodeIntD a).steps ≤ 10 * (a.natAbs.size + 1) := by
  have h := encodeNatD_steps a.natAbs
  simp only [encodeIntD]
  omega

theorem encodeIntD_allocations_le_steps (a : ℤ) :
    (encodeIntD a).allocations ≤ (encodeIntD a).steps := by
  have h := encodeNatD_allocations_le_steps a.natAbs
  simpa only [encodeIntD, Nat.add_le_add_iff_right] using h

def appendD {α : Type} : List α → List α → Costed (List α)
  | [], ys => ⟨ys, 1, 0⟩
  | x :: xs, ys =>
    let out := appendD xs ys
    ⟨x :: out.value, out.steps + 1, out.allocations + 1⟩

@[simp] theorem appendD_value {α : Type} (xs ys : List α) :
    (appendD xs ys).value = xs ++ ys := by induction xs <;> simp [appendD, *]

@[simp] theorem appendD_steps {α : Type} (xs ys : List α) :
    (appendD xs ys).steps = xs.length + 1 := by induction xs <;> simp [appendD, *]

@[simp] theorem appendD_allocations {α : Type} (xs ys : List α) :
    (appendD xs ys).allocations = xs.length := by induction xs <;> simp [appendD, *]

/-- List length is computed by actual binary increments, not an uncharged
host-language `List.length` used in the executable encoder. -/
def lengthD {α : Type} : List α → Costed ℕ
  | [] => ⟨0, 1, 0⟩
  | _ :: xs =>
    let tail := lengthD xs
    let inc := addNatD tail.value 1
    ⟨inc.value, tail.steps + inc.steps + 1, tail.allocations + inc.allocations⟩

@[simp] theorem lengthD_value {α : Type} (xs : List α) :
    (lengthD xs).value = xs.length := by induction xs <;> simp [lengthD, *]

theorem lengthD_steps {α : Type} (xs : List α) :
    (lengthD xs).steps ≤ 128 * (xs.length + 1) ^ 2 := by
  induction xs with
  | nil => simp [lengthD]
  | cons x xs ih =>
    have h := (dynamic_steps xs.length 1 (xs.length + 1)
      (by have := nat_size_le xs.length; omega) (by simp)).2.2.2
    simp only [lengthD, lengthD_value, List.length_cons]
    nlinarith

theorem lengthD_allocations_le_steps {α : Type} (xs : List α) :
    (lengthD xs).allocations ≤ (lengthD xs).steps := by
  induction xs with
  | nil => simp [lengthD]
  | cons x xs ih =>
    have h := (dynamic_allocations_le_steps (lengthD xs).value 1).2.2.2
    simp only [lengthD]
    omega

def flatEncodeD {α : Type} (enc : α → Costed Bits) : List α → Costed Bits
  | [] => ⟨[], 1, 0⟩
  | x :: xs =>
    let head := enc x
    let tail := flatEncodeD enc xs
    let out := appendD head.value tail.value
    ⟨out.value, head.steps + tail.steps + out.steps + 1,
      head.allocations + tail.allocations + out.allocations⟩

@[simp] theorem flatEncodeD_value {α : Type} (enc : α → Costed Bits) (xs : List α) :
    (flatEncodeD enc xs).value = xs.flatMap (fun x => (enc x).value) := by
  induction xs <;> simp [flatEncodeD, *]

theorem flatEncodeD_steps {α : Type} (enc : α → Costed Bits) (xs : List α) (S L : ℕ)
    (hS : ∀ x ∈ xs, (enc x).steps ≤ S) (hL : ∀ x ∈ xs, (enc x).value.length ≤ L) :
    (flatEncodeD enc xs).steps ≤ (xs.length + 1) * (S + L + 3) := by
  induction xs with
  | nil => simp [flatEncodeD]
  | cons x xs ih =>
    have hs := hS x (by simp)
    have hl := hL x (by simp)
    have ht := ih (fun y hy => hS y (by simp [hy])) (fun y hy => hL y (by simp [hy]))
    simp only [flatEncodeD, appendD_steps, List.length_cons]
    nlinarith

theorem flatEncodeD_allocations_le_steps {α : Type} (enc : α → Costed Bits) (xs : List α)
    (h : ∀ x ∈ xs, (enc x).allocations ≤ (enc x).steps) :
    (flatEncodeD enc xs).allocations ≤ (flatEncodeD enc xs).steps := by
  induction xs with
  | nil => simp [flatEncodeD]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [flatEncodeD, appendD_steps, appendD_allocations]
    omega

def encodeListD {α : Type} (enc : α → Costed Bits) (xs : List α) : Costed Bits :=
  let len := lengthD xs
  let header := encodeNatD len.value
  let payload := flatEncodeD enc xs
  let out := appendD header.value payload.value
  ⟨out.value, len.steps + header.steps + payload.steps + out.steps + 1,
    len.allocations + header.allocations + payload.allocations + out.allocations⟩

@[simp] theorem encodeListD_value {α : Type} (enc : α → Costed Bits) (xs : List α) :
    (encodeListD enc xs).value = encodeList (fun x => (enc x).value) xs := by
  simp [encodeListD, encodeList]

theorem encodeListD_steps {α : Type} (enc : α → Costed Bits) (xs : List α) (n S L : ℕ)
    (hn : xs.length ≤ n) (hS : ∀ x ∈ xs, (enc x).steps ≤ S)
    (hL : ∀ x ∈ xs, (enc x).value.length ≤ L) :
    (encodeListD enc xs).steps ≤ 256 * (n + 1) ^ 2 + (n + 1) * (S + L + 3) := by
  have hc := lengthD_steps xs
  have hp := encodeNatD_steps xs.length
  have ht := flatEncodeD_steps enc xs S L hS hL
  have hsize := nat_size_le xs.length
  have hm : (xs.length + 1) * (S + L + 3) ≤ (n + 1) * (S + L + 3) := by gcongr
  have hs : (xs.length + 1) ^ 2 ≤ (n + 1) ^ 2 := by gcongr
  simp only [encodeListD, lengthD_value, appendD_steps, encodeNatD_value, encodeNat_length]
  nlinarith

theorem encodeListD_allocations_le_steps {α : Type} (enc : α → Costed Bits) (xs : List α)
    (h : ∀ x ∈ xs, (enc x).allocations ≤ (enc x).steps) :
    (encodeListD enc xs).allocations ≤ (encodeListD enc xs).steps := by
  have hc := lengthD_allocations_le_steps xs
  have hp := encodeNatD_allocations_le_steps (lengthD xs).value
  have ht := flatEncodeD_allocations_le_steps enc xs h
  simp only [encodeListD, appendD_steps, appendD_allocations]
  omega

def encodeNatsD : List ℕ → Costed Bits := encodeListD encodeNatD
def encodeMatrixD : Matrix → Costed Bits := encodeListD encodeNatsD

@[simp] theorem encodeNatsD_value (xs : List ℕ) : (encodeNatsD xs).value = encodeNats xs := by
  simp [encodeNatsD]

@[simp] theorem encodeMatrixD_value (rows : Matrix) :
    (encodeMatrixD rows).value = encodeMatrix rows := by simp [encodeMatrixD, encodeMatrix]

theorem encodeNatsD_steps (xs : List ℕ) (n B : ℕ)
    (hn : xs.length ≤ n) (hB : ∀ x ∈ xs, x.size ≤ B) :
    (encodeNatsD xs).steps ≤ 512 * (n + 1) ^ 2 * (B + 1) := by
  have h := encodeListD_steps encodeNatD xs n (8 * (B + 1)) (2 * B + 1) hn
    (fun x hx => (encodeNatD_steps x).trans (by have := hB x hx; omega))
    (by intro x hx; simp only [encodeNatD_value, encodeNat_length]; have := hB x hx; omega)
  change (encodeListD encodeNatD xs).steps ≤ _
  nlinarith [Nat.zero_le (n * n * B)]

theorem encodeMatrixD_steps (rows : Matrix) (m n B : ℕ)
    (hm : rows.length ≤ m) (hn : ∀ row ∈ rows, row.length ≤ n)
    (hB : ∀ row ∈ rows, ∀ x ∈ row, x.size ≤ B) :
    (encodeMatrixD rows).steps ≤ 256 * (m + 1) ^ 2 +
      (m + 1) * (512 * (n + 1) ^ 2 * (B + 1) + 8 * (n + 1) * (B + 1) + 3) := by
  apply encodeListD_steps encodeNatsD rows m _ _ hm
  · intro row hr
    exact encodeNatsD_steps row n B (hn row hr) (hB row hr)
  · intro row hr
    have h := encodeNats_length_bound row n B (hn row hr) (hB row hr)
    have hs := nat_size_le n
    rw [encodeNatsD_value]
    nlinarith

theorem encodeMatrixD_allocations_le_steps (rows : Matrix) :
    (encodeMatrixD rows).allocations ≤ (encodeMatrixD rows).steps := by
  apply encodeListD_allocations_le_steps
  intro row _
  apply encodeListD_allocations_le_steps
  exact fun x _ => encodeNatD_allocations_le_steps x

theorem encodeMatrixD_roundtrip (rows : Matrix) :
    parseMatrix (encodeMatrixD rows).value = some rows := by simp

def decodeBitsD : Bits → Costed ℕ
  | [] => ⟨0, 1, 0⟩
  | b :: bs =>
    let out := decodeBitsD bs
    ⟨Nat.bit b out.value, out.steps + 3, out.allocations + 1⟩

@[simp] theorem decodeBitsD_value (bs : Bits) :
    (decodeBitsD bs).value = value bs := by induction bs <;> simp [decodeBitsD, value, *]

@[simp] theorem decodeBitsD_steps (bs : Bits) :
    (decodeBitsD bs).steps = 3 * bs.length + 1 := by
  induction bs <;> simp [decodeBitsD, *] <;> omega

@[simp] theorem decodeBitsD_allocations (bs : Bits) :
    (decodeBitsD bs).allocations = bs.length := by induction bs <;> simp [decodeBitsD, *]

theorem value_size_le (bs : Bits) : (value bs).size ≤ bs.length := by
  apply Nat.size_le.mpr
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
    rw [List.length_cons, pow_succ]
    cases b <;> simp only [value, Nat.bit_val, Bool.toNat_false, Bool.toNat_true] <;> omega

def eqBitsD : Bits → Bits → Costed Bool
  | [], [] => ⟨true, 1, 0⟩
  | [], _ :: _ => ⟨false, 1, 0⟩
  | _ :: _, [] => ⟨false, 1, 0⟩
  | x :: xs, y :: ys =>
    if x = y then
      let out := eqBitsD xs ys
      ⟨out.value, out.steps + 3, out.allocations⟩
    else ⟨false, 3, 0⟩

@[simp] theorem eqBitsD_value (xs ys : Bits) :
    (eqBitsD xs ys).value = decide (xs = ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [eqBitsD]
  | cons x xs ih =>
    cases ys with
    | nil => simp [eqBitsD]
    | cons y ys => by_cases h : x = y <;> simp [eqBitsD, h, ih]

theorem eqBitsD_steps (xs ys : Bits) :
    (eqBitsD xs ys).steps ≤ 3 * (xs.length + ys.length + 1) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [eqBitsD] <;> omega
  | cons x xs ih =>
    cases ys with
    | nil => simp [eqBitsD]; omega
    | cons y ys =>
      have h := ih ys
      simp only [eqBitsD]
      split_ifs <;> dsimp only <;> simp only [List.length_cons] <;> omega

@[simp] theorem eqBitsD_allocations (xs ys : Bits) : (eqBitsD xs ys).allocations = 0 := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys => by_cases h : x = y <;> simp [eqBitsD, ih, h]

def parseWordD : Bits → Costed (Option (Bits × Bits))
  | [] => ⟨none, 1, 0⟩
  | false :: rest => ⟨some ([], rest), 2, 0⟩
  | true :: [] => ⟨none, 2, 0⟩
  | true :: b :: rest =>
    let out := parseWordD rest
    ⟨out.value.map (fun pair => (b :: pair.1, pair.2)), out.steps + 4, out.allocations + 1⟩

@[simp] theorem parseWordD_value (input : Bits) : (parseWordD input).value = parseWord input := by
  induction input using parseWordD.induct with
  | case1 => rfl
  | case2 xs => rfl
  | case3 => rfl
  | case4 b xs ih => simp [parseWordD, parseWord, ih]

theorem parseWordD_steps (input : Bits) : (parseWordD input).steps ≤ 4 * input.length + 1 := by
  induction input using parseWordD.induct with
  | case1 => rfl
  | case2 xs => simp [parseWordD]; omega
  | case3 => simp [parseWordD]
  | case4 b xs ih => simp only [parseWordD, List.length_cons]; omega

theorem parseWordD_allocations_le_steps (input : Bits) :
    (parseWordD input).allocations ≤ (parseWordD input).steps := by
  induction input using parseWordD.induct with
  | case1 => simp [parseWordD]
  | case2 xs => simp [parseWordD]
  | case3 => simp [parseWordD]
  | case4 b xs ih => simp only [parseWordD]; omega

def parseNatD (input : Bits) : Costed (Option (ℕ × Bits)) :=
  let out := parseWordD input
  match out.value with
  | none => ⟨none, out.steps + 1, out.allocations⟩
  | some (bs, rest) =>
    let n := decodeBitsD bs
    let canonical := bitsNatD n.value
    let ok := eqBitsD canonical.value bs
    ⟨if ok.value then some (n.value, rest) else none,
      out.steps + n.steps + canonical.steps + ok.steps + 2,
      out.allocations + n.allocations + canonical.allocations + ok.allocations⟩

@[simp] theorem parseNatD_value (input : Bits) : (parseNatD input).value = parseNat input := by
  simp only [parseNatD, parseWordD_value]
  cases hp : parseWord input with
  | none => simp [parseNat, hp]
  | some out =>
    rcases out with ⟨bs, rest⟩
    simp [parseNat, hp, (bitsNatD_spec (value bs)).1]

theorem parseNatD_steps (input : Bits) : (parseNatD input).steps ≤ 64 * (input.length + 1) := by
  have hw := parseWordD_steps input
  cases hp : (parseWordD input).value with
  | none => simp only [parseNatD, hp]; omega
  | some out =>
    rcases out with ⟨bs, rest⟩
    have hc := parseWord_consumed input bs rest (by simpa using hp)
    have hl := congrArg List.length hc
    simp only [List.length_append, word_length] at hl
    have hn := value_size_le bs
    have he := eqBitsD_steps (value bs).bits bs
    have hb := Nat.size_eq_bits_len (value bs)
    simp only [parseNatD, hp, decodeBitsD_value, decodeBitsD_steps,
      (bitsNatD_spec (value bs)).1, (bitsNatD_spec (value bs)).2.1]
    omega

theorem parseNatD_allocations_le_steps (input : Bits) :
    (parseNatD input).allocations ≤ (parseNatD input).steps := by
  have hw := parseWordD_allocations_le_steps input
  cases hp : (parseWordD input).value with
  | none => simp only [parseNatD, hp]; omega
  | some out =>
    rcases out with ⟨bs, rest⟩
    simp only [parseNatD, hp, decodeBitsD_value, decodeBitsD_steps, decodeBitsD_allocations,
      (bitsNatD_spec (value bs)).1, (bitsNatD_spec (value bs)).2.1,
      (bitsNatD_spec (value bs)).2.2, eqBitsD_allocations]
    omega

def parseIntD : Bits → Costed (Option (ℤ × Bits))
  | [] => ⟨none, 1, 0⟩
  | sign :: input =>
    let out := parseNatD input
    match out.value with
    | none => ⟨none, out.steps + 2, out.allocations⟩
    | some (n, rest) =>
      if sign then
        let zero := zeroNatD n
        ⟨if zero.value then none else some (-(n : ℤ), rest),
          out.steps + zero.steps + 3, out.allocations + zero.allocations + 1⟩
      else ⟨some ((n : ℤ), rest), out.steps + 3, out.allocations + 1⟩

@[simp] theorem parseIntD_value (input : Bits) : (parseIntD input).value = parseInt input := by
  cases input with
  | nil => rfl
  | cons sign input =>
    simp only [parseIntD, parseNatD_value]
    cases hp : parseNat input with
    | none => simp [parseInt, hp]
    | some out =>
      rcases out with ⟨n, rest⟩
      cases sign <;> simp [parseInt, hp]

theorem parseIntD_steps (input : Bits) : (parseIntD input).steps ≤ 256 * (input.length + 1) := by
  cases input with
  | nil => simp [parseIntD]
  | cons sign input =>
    have hn := parseNatD_steps input
    cases hp : (parseNatD input).value with
    | none => simp only [parseIntD, hp, List.length_cons]; omega
    | some out =>
      rcases out with ⟨n, rest⟩
      have hc := parseNat_canonical input rest n (by simpa using hp)
      have hl := congrArg List.length hc
      simp only [List.length_append, encodeNat_length] at hl
      have hz := (dynamic_steps n 0 input.length (by omega) (by simp)).1
      change (zeroNatD n).steps ≤ _ at hz
      cases sign <;> simp only [parseIntD, hp, Bool.false_eq_true,
        ↓reduceIte, List.length_cons] <;> omega

theorem parseIntD_allocations_le_steps (input : Bits) :
    (parseIntD input).allocations ≤ (parseIntD input).steps := by
  cases input with
  | nil => simp [parseIntD]
  | cons sign input =>
    have hn := parseNatD_allocations_le_steps input
    cases hp : (parseNatD input).value with
    | none => simp only [parseIntD, hp]; omega
    | some out =>
      rcases out with ⟨n, rest⟩
      have hz := (dynamic_allocations_le_steps n 0).1
      change (zeroNatD n).allocations ≤ (zeroNatD n).steps at hz
      cases sign <;> simp only [parseIntD, hp, Bool.false_eq_true,
        ↓reduceIte] <;> omega

end UAVProof.TreeBudgetCostedCodec
