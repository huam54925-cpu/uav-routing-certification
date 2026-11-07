import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! A concrete binary wire format. A payload bit `b` is stored as `true,b`;
`false` terminates a word. Natural payloads are canonical least-significant-bit
first binary digits. Every scalar and list has a nonempty, self-delimiting code.
Counted parsers reject a count larger than the remaining bit string before
recursing, so an enormous encoded count cannot request an enormous allocation. -/
namespace UAVProof.TreeBudgetBinaryCodec

abbrev Bits := List Bool
abbrev Parser (α : Type) := Bits → Option (α × Bits)

def word (bs : Bits) : Bits := bs.flatMap (fun b => [true, b]) ++ [false]

def parseWord : Parser Bits
  | [] => none
  | false :: rest => some ([], rest)
  | true :: [] => none
  | true :: b :: rest => (parseWord rest).map fun out => (b :: out.1, out.2)

theorem word_length (bs : Bits) : (word bs).length = 2 * bs.length + 1 := by
  induction bs with
  | nil => simp [word]
  | cons b bs ih => simp_all [word, Nat.mul_add, Nat.add_assoc]

theorem parseWord_append (bs suffix : Bits) :
    parseWord (word bs ++ suffix) = some (bs, suffix) := by
  induction bs with
  | nil => simp [word, parseWord]
  | cons b bs ih => simpa [word, parseWord, List.append_assoc] using ih

theorem parseWord_consumed (input bs rest : Bits) (h : parseWord input = some (bs, rest)) :
    input = word bs ++ rest := by
  induction input using parseWord.induct generalizing bs rest with
  | case1 => simp [parseWord] at h
  | case2 xs =>
    simp only [parseWord, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | case3 => simp [parseWord] at h
  | case4 b xs ih =>
    simp only [parseWord, Option.map_eq_some_iff] at h
    obtain ⟨⟨ys, tail⟩, hy, he⟩ := h
    cases he
    simpa [word, List.append_assoc] using congrArg (fun zs => true :: b :: zs) (ih _ _ hy)

def value : Bits → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (value bs)

@[simp] theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n hn ih => simp [Nat.bits_append_bit n b hn, value, ih]

def encodeNat (n : ℕ) : Bits := word n.bits

def parseNat (input : Bits) : Option (ℕ × Bits) := do
  let (bs, rest) ← parseWord input
  let n := value bs
  if n.bits = bs then some (n, rest) else none

theorem encodeNat_length (n : ℕ) : (encodeNat n).length = 2 * n.size + 1 := by
  simp [encodeNat, word_length, Nat.size_eq_bits_len]

theorem encodeNat_nonempty (n : ℕ) : 1 ≤ (encodeNat n).length := by
  rw [encodeNat_length]; omega

theorem parseNat_append (n : ℕ) (suffix : Bits) :
    parseNat (encodeNat n ++ suffix) = some (n, suffix) := by
  simp [parseNat, encodeNat, parseWord_append]

theorem parseNat_canonical (input rest : Bits) (n : ℕ)
    (h : parseNat input = some (n, rest)) : input = encodeNat n ++ rest := by
  cases hp : parseWord input with
  | none => simp [parseNat, hp] at h
  | some out =>
    rcases out with ⟨bs, tail⟩
    by_cases hc : (value bs).bits = bs
    · simp [parseNat, hp, hc] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa only [encodeNat, hc] using parseWord_consumed input bs tail hp
    · simp [parseNat, hp, hc] at h

def encodeInt (z : ℤ) : Bits := decide (z < 0) :: encodeNat z.natAbs

def parseInt : Parser ℤ
  | [] => none
  | sign :: input => do
      let (n, rest) ← parseNat input
      if sign then
        if n = 0 then none else some (-(n : ℤ), rest)
      else some ((n : ℤ), rest)

theorem encodeInt_length (z : ℤ) :
    (encodeInt z).length = 2 * z.natAbs.size + 2 := by
  simp [encodeInt, encodeNat_length, Nat.add_assoc]

theorem encodeInt_nonempty (z : ℤ) : 1 ≤ (encodeInt z).length := by
  rw [encodeInt_length]; omega

theorem parseInt_append (z : ℤ) (suffix : Bits) :
    parseInt (encodeInt z ++ suffix) = some (z, suffix) := by
  cases z with
  | ofNat n => simp [encodeInt, parseInt, parseNat_append]
  | negSucc n => simp [encodeInt, parseInt, parseNat_append]; omega

def parseMany {α : Type} (p : Parser α) : ℕ → Parser (List α)
  | 0, input => some ([], input)
  | n + 1, input => do
      let (x, rest) ← p input
      let (xs, tail) ← parseMany p n rest
      some (x :: xs, tail)

def encodeList {α : Type} (enc : α → Bits) (xs : List α) : Bits :=
  encodeNat xs.length ++ xs.flatMap enc

def parseList {α : Type} (p : Parser α) (input : Bits) : Option (List α × Bits) := do
  let (count, rest) ← parseNat input
  if count ≤ rest.length then parseMany p count rest else none

theorem length_le_flatMap {α : Type} (enc : α → Bits)
    (hn : ∀ x, 1 ≤ (enc x).length) (xs : List α) : xs.length ≤ (xs.flatMap enc).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have := hn x
    omega

theorem parseMany_append {α : Type} (enc : α → Bits) (p : Parser α)
    (hp : ∀ x suffix, p (enc x ++ suffix) = some (x, suffix))
    (xs : List α) (suffix : Bits) :
    parseMany p xs.length (xs.flatMap enc ++ suffix) = some (xs, suffix) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [parseMany, hp, ih, List.append_assoc]

theorem encodeList_nonempty {α : Type} (enc : α → Bits) (xs : List α) :
    1 ≤ (encodeList enc xs).length := by
  have := encodeNat_nonempty xs.length
  simpa only [encodeList, List.length_append] using
    (le_trans this (Nat.le_add_right (encodeNat xs.length).length (xs.flatMap enc).length))

theorem parseList_append {α : Type} (enc : α → Bits) (p : Parser α)
    (hp : ∀ x suffix, p (enc x ++ suffix) = some (x, suffix))
    (hn : ∀ x, 1 ≤ (enc x).length) (xs : List α) (suffix : Bits) :
    parseList p (encodeList enc xs ++ suffix) = some (xs, suffix) := by
  have hl : xs.length ≤ (xs.flatMap enc ++ suffix).length := by
    simpa only [List.length_append] using
      le_trans (length_le_flatMap enc hn xs) (Nat.le_add_right _ suffix.length)
  simp only [parseList, encodeList, List.append_assoc, parseNat_append]
  change (if xs.length ≤ (xs.flatMap enc ++ suffix).length then
    parseMany p xs.length (xs.flatMap enc ++ suffix) else none) = some (xs, suffix)
  rw [if_pos hl]
  exact parseMany_append enc p hp xs suffix

abbrev encodeNats := encodeList encodeNat
abbrev parseNats := parseList parseNat
abbrev encodeInts := encodeList encodeInt
abbrev parseInts := parseList parseInt

@[simp] theorem parseNats_append (xs : List ℕ) (suffix : Bits) :
    parseNats (encodeNats xs ++ suffix) = some (xs, suffix) :=
  parseList_append _ _ parseNat_append encodeNat_nonempty xs suffix

@[simp] theorem parseInts_append (xs : List ℤ) (suffix : Bits) :
    parseInts (encodeInts xs ++ suffix) = some (xs, suffix) :=
  parseList_append _ _ parseInt_append encodeInt_nonempty xs suffix

structure RawInput where
  n : ℕ
  root : ℕ
  parents : List ℕ
  multiplicities : List ℕ
  numerators : List ℤ
  denominators : List ℕ
  budgetNumerator : ℤ
  budgetDenominator : ℕ
  deriving DecidableEq, Repr

def Shape (I : RawInput) : Prop :=
  I.parents.length = I.n ∧ I.multiplicities.length = I.n ∧
  I.numerators.length = I.n ∧ I.denominators.length = I.n

instance (I : RawInput) : Decidable (Shape I) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def encodeInput (I : RawInput) : Bits :=
  encodeNat I.n ++ encodeNat I.root ++ encodeNats I.parents ++ encodeNats I.multiplicities ++
  encodeInts I.numerators ++ encodeNats I.denominators ++
  encodeInt I.budgetNumerator ++ encodeNat I.budgetDenominator

def parseInputPrefix (input : Bits) : Option (RawInput × Bits) := do
  let (n, input) ← parseNat input
  let (root, input) ← parseNat input
  let (parents, input) ← parseNats input
  let (multiplicities, input) ← parseNats input
  let (numerators, input) ← parseInts input
  let (denominators, input) ← parseNats input
  let (budgetNumerator, input) ← parseInt input
  let (budgetDenominator, rest) ← parseNat input
  let I := RawInput.mk n root parents multiplicities numerators denominators
    budgetNumerator budgetDenominator
  if Shape I then some (I, rest) else none

def parseInput (input : Bits) : Option RawInput := do
  let (I, rest) ← parseInputPrefix input
  if rest = [] then some I else none

theorem parseInputPrefix_append (I : RawInput) (h : Shape I) (suffix : Bits) :
    parseInputPrefix (encodeInput I ++ suffix) = some (I, suffix) := by
  cases I
  simp [encodeInput, parseInputPrefix, List.append_assoc, parseNat_append,
    parseInt_append, h]

@[simp] theorem parseInput_encode (I : RawInput) (h : Shape I) :
    parseInput (encodeInput I) = some I := by
  have he := parseInputPrefix_append I h []
  simp only [List.append_nil] at he
  simp [parseInput, he]

theorem parseInput_rejects_trailing (I : RawInput) (h : Shape I)
    (suffix : Bits) (hs : suffix ≠ []) : parseInput (encodeInput I ++ suffix) = none := by
  simp [parseInput, parseInputPrefix_append I h, hs]

abbrev Matrix := List (List ℕ)
def encodeMatrix : Matrix → Bits := encodeList encodeNats
def parseMatrixPrefix : Parser Matrix := parseList parseNats
def parseMatrix (input : Bits) : Option Matrix := do
  let (rows, rest) ← parseMatrixPrefix input
  if rest = [] then some rows else none

theorem parseMatrixPrefix_append (rows : Matrix) (suffix : Bits) :
    parseMatrixPrefix (encodeMatrix rows ++ suffix) = some (rows, suffix) :=
  parseList_append _ _ parseNats_append (encodeList_nonempty encodeNat) rows suffix

@[simp] theorem parseMatrix_encode (rows : Matrix) :
    parseMatrix (encodeMatrix rows) = some rows := by
  have he := parseMatrixPrefix_append rows []
  simp only [List.append_nil] at he
  simp [parseMatrix, he]

theorem parseMany_length {α : Type} (p : Parser α) (count : ℕ)
    (input : Bits) (xs : List α) (rest : Bits)
    (h : parseMany p count input = some (xs, rest)) : xs.length = count := by
  induction count generalizing input xs rest with
  | zero =>
    simp only [parseMany, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ count ih =>
    cases hp : p input with
    | none => simp [parseMany, hp] at h
    | some out =>
      rcases out with ⟨x, tail⟩
      cases ht : parseMany p count tail with
      | none => simp [parseMany, hp, ht] at h
      | some out =>
        rcases out with ⟨ys, tail'⟩
        simp [parseMany, hp, ht] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa using congrArg Nat.succ (ih tail ys tail' ht)

theorem parseList_count_bound {α : Type} (p : Parser α) (input : Bits)
    (out : List α × Bits) (h : parseList p input = some out) :
    ∃ count rest, parseNat input = some (count, rest) ∧ count ≤ rest.length ∧
      parseMany p count rest = some out := by
  cases hp : parseNat input with
  | none => simp [parseList, hp] at h
  | some found =>
    rcases found with ⟨count, rest⟩
    by_cases hl : count ≤ rest.length
    · exact ⟨count, rest, rfl, hl, by simpa [parseList, hp, hl] using h⟩
    · simp [parseList, hp, hl] at h

theorem parseList_output_length_le {α : Type} (p : Parser α) (input : Bits)
    (xs : List α) (rest : Bits) (h : parseList p input = some (xs, rest)) :
    xs.length ≤ input.length := by
  obtain ⟨count, tail, hp, hl, hm⟩ := parseList_count_bound p input _ h
  have hx := parseMany_length p count tail xs rest hm
  have hi := congrArg List.length (parseNat_canonical input tail count hp)
  simp only [List.length_append] at hi
  omega

theorem parseList_large_count {α : Type} (p : Parser α) (count : ℕ) (rest : Bits)
    (h : rest.length < count) : parseList p (encodeNat count ++ rest) = none := by
  simp [parseList, parseNat_append, Nat.not_le.mpr h]

theorem sum_size_encodeNat (xs : List ℕ) :
    ((xs.flatMap encodeNat).length) = 2 * (xs.map Nat.size).sum + xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, encodeNat_length, List.map_cons,
      List.sum_cons, List.length_cons, ih]
    omega

theorem sum_size_encodeInt (xs : List ℤ) :
    ((xs.flatMap encodeInt).length) =
      2 * (xs.map fun z => z.natAbs.size).sum + 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, encodeInt_length, List.map_cons,
      List.sum_cons, List.length_cons, ih]
    omega

theorem encodeNats_length (xs : List ℕ) :
    (encodeNats xs).length = 2 * xs.length.size + 1 +
      2 * (xs.map Nat.size).sum + xs.length := by
  simp only [encodeNats, encodeList, List.length_append, encodeNat_length, sum_size_encodeNat]
  omega

theorem encodeInts_length (xs : List ℤ) :
    (encodeInts xs).length = 2 * xs.length.size + 1 +
      2 * (xs.map fun z => z.natAbs.size).sum + 2 * xs.length := by
  simp only [encodeInts, encodeList, List.length_append, encodeNat_length, sum_size_encodeInt]
  omega

/-- The width budget is derived from actual fields; its upper bound below is
the length of the emitted bit string, rather than an independently chosen size. -/
def inputWeight (I : RawInput) : ℕ :=
  I.n.size + I.root.size + (I.parents.map Nat.size).sum +
  (I.multiplicities.map Nat.size).sum + (I.numerators.map fun z => z.natAbs.size).sum +
  (I.denominators.map Nat.size).sum + I.budgetNumerator.natAbs.size + I.budgetDenominator.size

theorem inputWeight_le_length (I : RawInput) : inputWeight I ≤ (encodeInput I).length := by
  simp only [inputWeight, encodeInput, List.length_append, encodeNat_length,
    encodeInt_length, encodeNats_length, encodeInts_length]
  omega

theorem vertexCount_le_length (I : RawInput) (h : Shape I) :
    I.n ≤ (encodeInput I).length := by
  have hp := h.1
  simp only [encodeInput, List.length_append, encodeNat_length,
    encodeInt_length, encodeNats_length, encodeInts_length]
  omega

theorem encodeMatrix_length (rows : Matrix) :
    (encodeMatrix rows).length = 2 * rows.length.size + 1 +
      (rows.map fun row => 2 * row.length.size + 1 +
        2 * (row.map Nat.size).sum + row.length).sum := by
  change (encodeNat rows.length ++ rows.flatMap encodeNats).length = _
  simp only [List.length_append, encodeNat_length, List.length_flatMap, encodeNats_length]

theorem negative_zero_rejected (suffix : Bits) :
    parseInt (true :: (encodeNat 0 ++ suffix)) = none := by
  simp [parseInt, parseNat_append]

theorem truncated_word_rejected (bs : Bits) :
    parseWord (bs.flatMap fun b => [true, b]) = none := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [parseWord] using ih

theorem input_encode_injective {I J : RawInput} (hI : Shape I) (hJ : Shape J)
    (h : encodeInput I = encodeInput J) : I = J := by
  have he := congrArg parseInput h
  simpa [parseInput_encode I hI, parseInput_encode J hJ] using he

theorem matrix_encode_injective : Function.Injective encodeMatrix := by
  intro rows rows' h
  have he := congrArg parseMatrix h
  simpa using he

/-- Actual bit writes in the framing loop; scalar digit extraction is separate. -/
def writeWord : Bits → Bits × ℕ
  | [] => ([false], 1)
  | b :: bs =>
      let out := writeWord bs
      (true :: b :: out.1, out.2 + 2)

theorem writeWord_value (bs : Bits) : (writeWord bs).1 = word bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [writeWord, word, ih]

theorem writeWord_cost (bs : Bits) : (writeWord bs).2 = 2 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [writeWord, ih]; omega

/-- Each inspected framing or payload bit is charged, including failed/truncated
inputs. This is wire scanning work, not arithmetic or allocated-address cost. -/
def scanWord : Bits → Option (Bits × Bits) × ℕ
  | [] => (none, 0)
  | false :: rest => (some ([], rest), 1)
  | true :: [] => (none, 1)
  | true :: b :: rest =>
      let out := scanWord rest
      (out.1.map (fun pair => (b :: pair.1, pair.2)), out.2 + 2)

theorem scanWord_value (input : Bits) : (scanWord input).1 = parseWord input := by
  induction input using scanWord.induct with
  | case1 => rfl
  | case2 xs => rfl
  | case3 => rfl
  | case4 b xs ih => simp [scanWord, parseWord, ih]

theorem scanWord_cost_le (input : Bits) : (scanWord input).2 ≤ input.length := by
  induction input using scanWord.induct with
  | case1 => rfl
  | case2 xs => simp [scanWord]
  | case3 => rfl
  | case4 b xs ih => simp only [scanWord, List.length_cons]; omega

theorem scanWord_cost_encoded (bs suffix : Bits) :
    (scanWord (word bs ++ suffix)).2 = (word bs).length := by
  induction bs with
  | nil => simp [word, scanWord]
  | cons b bs ih =>
    simpa [word, scanWord, List.append_assoc, Nat.add_assoc] using ih

theorem scanWord_consumption (input bs rest : Bits)
    (h : (scanWord input).1 = some (bs, rest)) :
    (scanWord input).2 + rest.length = input.length := by
  have hp := parseWord_consumed input bs rest (by simpa [scanWord_value] using h)
  rw [hp, scanWord_cost_encoded, List.length_append]

theorem sum_size_le (xs : List ℕ) (B : ℕ) (h : ∀ x ∈ xs, x.size ≤ B) :
    (xs.map Nat.size).sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem encodeNats_length_bound (xs : List ℕ) (n B : ℕ)
    (hn : xs.length ≤ n) (hB : ∀ x ∈ xs, x.size ≤ B) :
    (encodeNats xs).length ≤ 2 * n.size + 1 + 2 * n * B + n := by
  have hs := sum_size_le xs B hB
  have hn' := Nat.size_le_size hn
  rw [encodeNats_length]
  nlinarith

theorem encodeMatrix_length_bound (rows : Matrix) (m n B : ℕ)
    (hm : rows.length ≤ m) (hn : ∀ row ∈ rows, row.length ≤ n)
    (hB : ∀ row ∈ rows, ∀ x ∈ row, x.size ≤ B) :
    (encodeMatrix rows).length ≤
      2 * m.size + 1 + m * (2 * n.size + 1 + 2 * n * B + n) := by
  have hs : (rows.map fun row => (encodeNats row).length).sum ≤
      rows.length * (2 * n.size + 1 + 2 * n * B + n) := by
    have hb := List.sum_le_card_nsmul
      (rows.map fun row => (encodeNats row).length) (2 * n.size + 1 + 2 * n * B + n)
      (by
        intro x hx
        obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hx
        exact encodeNats_length_bound row n B (hn row hr) (hB row hr))
    simpa only [List.length_map, nsmul_eq_mul] using hb
  have hm' := Nat.size_le_size hm
  change (encodeNat rows.length ++ rows.flatMap encodeNats).length ≤ _
  simp only [List.length_append, encodeNat_length, List.length_flatMap]
  exact Nat.add_le_add (by omega) (hs.trans (Nat.mul_le_mul_right _ hm))

theorem parseInt_canonical (input rest : Bits) (z : ℤ)
    (h : parseInt input = some (z, rest)) : input = encodeInt z ++ rest := by
  cases input with
  | nil => simp [parseInt] at h
  | cons sign input =>
    cases hn : parseNat input with
    | none => simp [parseInt, hn] at h
    | some out =>
      rcases out with ⟨n, tail⟩
      have hc := parseNat_canonical input tail n hn
      cases sign with
      | false =>
        simp [parseInt, hn] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa [encodeInt] using congrArg (List.cons false) hc
      | true =>
        by_cases hz : n = 0
        · simp [parseInt, hn, hz] at h
        · simp [parseInt, hn, hz] at h
          obtain ⟨rfl, rfl⟩ := h
          simpa [encodeInt, hz, Nat.pos_of_ne_zero hz] using congrArg (List.cons true) hc

theorem parseMany_canonical {α : Type} (enc : α → Bits) (p : Parser α)
    (hp : ∀ input rest x, p input = some (x, rest) → input = enc x ++ rest)
    (count : ℕ) (input rest : Bits) (xs : List α)
    (h : parseMany p count input = some (xs, rest)) : input = xs.flatMap enc ++ rest := by
  induction count generalizing input rest xs with
  | zero =>
    simp [parseMany] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ count ih =>
    cases hx : p input with
    | none => simp [parseMany, hx] at h
    | some out =>
      rcases out with ⟨x, tail⟩
      cases ht : parseMany p count tail with
      | none => simp [parseMany, hx, ht] at h
      | some out =>
        rcases out with ⟨ys, tail'⟩
        simp [parseMany, hx, ht] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [hp input tail x hx, ih tail tail' ys ht]
        simp [List.append_assoc]

theorem parseList_canonical {α : Type} (enc : α → Bits) (p : Parser α)
    (hp : ∀ input rest x, p input = some (x, rest) → input = enc x ++ rest)
    (input rest : Bits) (xs : List α)
    (h : parseList p input = some (xs, rest)) : input = encodeList enc xs ++ rest := by
  obtain ⟨count, tail, hc, _, hm⟩ := parseList_count_bound p input (xs, rest) h
  have hl := parseMany_length p count tail xs rest hm
  rw [parseNat_canonical input tail count hc, parseMany_canonical enc p hp count tail rest xs hm]
  simp [encodeList, hl, List.append_assoc]

theorem parseInputPrefix_canonical (input rest : Bits) (I : RawInput)
    (h : parseInputPrefix input = some (I, rest)) :
    input = encodeInput I ++ rest ∧ Shape I := by
  simp only [parseInputPrefix, bind, Option.bind_eq_some_iff] at h
  rcases h with ⟨⟨n, s₁⟩, h₁, ⟨⟨root, s₂⟩, h₂, ⟨⟨parents, s₃⟩, h₃,
    ⟨⟨multiplicities, s₄⟩, h₄, ⟨⟨numerators, s₅⟩, h₅, ⟨⟨denominators, s₆⟩, h₆,
    ⟨⟨budgetNumerator, s₇⟩, h₇, ⟨⟨budgetDenominator, s₈⟩, h₈, h⟩⟩⟩⟩⟩⟩⟩⟩
  dsimp only at *
  split_ifs at h with hs
  obtain ⟨rfl, rfl⟩ := Option.some.inj h
  constructor
  · rw [parseNat_canonical _ _ _ h₁, parseNat_canonical _ _ _ h₂,
      parseList_canonical encodeNat parseNat parseNat_canonical _ _ _ h₃,
      parseList_canonical encodeNat parseNat parseNat_canonical _ _ _ h₄,
      parseList_canonical encodeInt parseInt parseInt_canonical _ _ _ h₅,
      parseList_canonical encodeNat parseNat parseNat_canonical _ _ _ h₆,
      parseInt_canonical _ _ _ h₇, parseNat_canonical _ _ _ h₈]
    simp [encodeInput, List.append_assoc]
  · exact hs

theorem parseInput_canonical (input : Bits) (I : RawInput)
    (h : parseInput input = some I) : input = encodeInput I ∧ Shape I := by
  simp only [parseInput, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨J, rest⟩, hp, h⟩ := h
  dsimp only at *
  split_ifs at h with hr
  subst rest
  cases h
  simpa using parseInputPrefix_canonical input [] I hp

end UAVProof.TreeBudgetBinaryCodec
#print axioms UAVProof.TreeBudgetBinaryCodec.Bits
#print axioms UAVProof.TreeBudgetBinaryCodec.Parser
#print axioms UAVProof.TreeBudgetBinaryCodec.word
#print axioms UAVProof.TreeBudgetBinaryCodec.parseWord
#print axioms UAVProof.TreeBudgetBinaryCodec.word_length
#print axioms UAVProof.TreeBudgetBinaryCodec.parseWord_append
#print axioms UAVProof.TreeBudgetBinaryCodec.parseWord_consumed
#print axioms UAVProof.TreeBudgetBinaryCodec.value
#print axioms UAVProof.TreeBudgetBinaryCodec.value_bits
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeNat
#print axioms UAVProof.TreeBudgetBinaryCodec.parseNat
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeNat_length
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeNat_nonempty
#print axioms UAVProof.TreeBudgetBinaryCodec.parseNat_append
#print axioms UAVProof.TreeBudgetBinaryCodec.parseNat_canonical
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeInt
#print axioms UAVProof.TreeBudgetBinaryCodec.parseInt
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeInt_length
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeInt_nonempty
#print axioms UAVProof.TreeBudgetBinaryCodec.parseInt_append
#print axioms UAVProof.TreeBudgetBinaryCodec.parseMany
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeList
#print axioms UAVProof.TreeBudgetBinaryCodec.parseList
#print axioms UAVProof.TreeBudgetBinaryCodec.length_le_flatMap
#print axioms UAVProof.TreeBudgetBinaryCodec.parseMany_append
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeList_nonempty
#print axioms UAVProof.TreeBudgetBinaryCodec.parseList_append
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeNats
#print axioms UAVProof.TreeBudgetBinaryCodec.parseNats
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeInts
#print axioms UAVProof.TreeBudgetBinaryCodec.parseInts
#print axioms UAVProof.TreeBudgetBinaryCodec.parseNats_append
#print axioms UAVProof.TreeBudgetBinaryCodec.parseInts_append
#print axioms UAVProof.TreeBudgetBinaryCodec.RawInput
#print axioms UAVProof.TreeBudgetBinaryCodec.Shape
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeInput
#print axioms UAVProof.TreeBudgetBinaryCodec.parseInputPrefix
#print axioms UAVProof.TreeBudgetBinaryCodec.parseInput
#print axioms UAVProof.TreeBudgetBinaryCodec.parseInputPrefix_append
#print axioms UAVProof.TreeBudgetBinaryCodec.parseInput_encode
#print axioms UAVProof.TreeBudgetBinaryCodec.parseInput_rejects_trailing
#print axioms UAVProof.TreeBudgetBinaryCodec.Matrix
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeMatrix
#print axioms UAVProof.TreeBudgetBinaryCodec.parseMatrixPrefix
#print axioms UAVProof.TreeBudgetBinaryCodec.parseMatrix
#print axioms UAVProof.TreeBudgetBinaryCodec.parseMatrixPrefix_append
#print axioms UAVProof.TreeBudgetBinaryCodec.parseMatrix_encode
#print axioms UAVProof.TreeBudgetBinaryCodec.parseMany_length
#print axioms UAVProof.TreeBudgetBinaryCodec.parseList_count_bound
#print axioms UAVProof.TreeBudgetBinaryCodec.parseList_output_length_le
#print axioms UAVProof.TreeBudgetBinaryCodec.parseList_large_count
#print axioms UAVProof.TreeBudgetBinaryCodec.sum_size_encodeNat
#print axioms UAVProof.TreeBudgetBinaryCodec.sum_size_encodeInt
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeNats_length
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeInts_length
#print axioms UAVProof.TreeBudgetBinaryCodec.inputWeight
#print axioms UAVProof.TreeBudgetBinaryCodec.inputWeight_le_length
#print axioms UAVProof.TreeBudgetBinaryCodec.vertexCount_le_length
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeMatrix_length
#print axioms UAVProof.TreeBudgetBinaryCodec.negative_zero_rejected
#print axioms UAVProof.TreeBudgetBinaryCodec.truncated_word_rejected
#print axioms UAVProof.TreeBudgetBinaryCodec.input_encode_injective
#print axioms UAVProof.TreeBudgetBinaryCodec.matrix_encode_injective
#print axioms UAVProof.TreeBudgetBinaryCodec.writeWord
#print axioms UAVProof.TreeBudgetBinaryCodec.writeWord_value
#print axioms UAVProof.TreeBudgetBinaryCodec.writeWord_cost
#print axioms UAVProof.TreeBudgetBinaryCodec.scanWord
#print axioms UAVProof.TreeBudgetBinaryCodec.scanWord_value
#print axioms UAVProof.TreeBudgetBinaryCodec.scanWord_cost_le
#print axioms UAVProof.TreeBudgetBinaryCodec.scanWord_cost_encoded
#print axioms UAVProof.TreeBudgetBinaryCodec.scanWord_consumption
#print axioms UAVProof.TreeBudgetBinaryCodec.sum_size_le
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeNats_length_bound
#print axioms UAVProof.TreeBudgetBinaryCodec.encodeMatrix_length_bound

#print axioms UAVProof.TreeBudgetBinaryCodec.parseInt_canonical
#print axioms UAVProof.TreeBudgetBinaryCodec.parseMany_canonical
#print axioms UAVProof.TreeBudgetBinaryCodec.parseList_canonical
#print axioms UAVProof.TreeBudgetBinaryCodec.parseInputPrefix_canonical
#print axioms UAVProof.TreeBudgetBinaryCodec.parseInput_canonical
