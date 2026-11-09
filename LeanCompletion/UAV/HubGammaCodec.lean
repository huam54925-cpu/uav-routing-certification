import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! The paper's MSB-first gamma code of `n+1`.  No list length headers.
The parser scans actual input; its final canonicality check is executable.
No machine running-time bound is asserted here. -/
namespace UAVProof.HubGammaCodec

abbrev Bits := List Bool

def value : Bits → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (value bs)

@[simp] theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n hn ih => simp [Nat.bits_append_bit n b hn, value, ih]

theorem bits_msb {n : ℕ} (hn : n ≠ 0) : ∃ w, n.bits.reverse = true :: w := by
  induction n using Nat.binaryRec' with
  | zero => contradiction
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h, List.reverse_cons]
    by_cases hz : n = 0
    · subst n
      simp [h rfl]
    · obtain ⟨w, hw⟩ := ih hz
      exact ⟨w ++ [b], by simp [hw]⟩

def encodeGamma (n : ℕ) : Bits :=
  List.replicate ((n+1).size - 1) false ++ (n+1).bits.reverse

def gammaLength (n : ℕ) : ℕ := 2 * (n+1).size - 1

@[simp] theorem encodeGamma_length (n : ℕ) :
    (encodeGamma n).length = gammaLength n := by
  have hp : 0 < (n+1).size := Nat.size_pos.mpr (by omega)
  simp [encodeGamma, gammaLength, Nat.size_eq_bits_len]
  omega

theorem encodeGamma_nonempty (n : ℕ) : 0 < (encodeGamma n).length := by
  have hp : 0 < (n+1).size := Nat.size_pos.mpr (by omega)
  rw [encodeGamma_length]; unfold gammaLength; omega

/-- Scan only the supplied bits for the first one. -/
def scan : Bits → Option (ℕ × Bits)
  | [] => none
  | true :: bs => some (0, bs)
  | false :: bs => (scan bs).map (fun p => (p.1+1, p.2))

theorem scan_append (z : ℕ) (r : Bits) :
    scan (List.replicate z false ++ true :: r) = some (z, r) := by
  induction z with
  | zero => rfl
  | succ z ih => simpa [List.replicate_succ, scan] using ih

theorem scan_sound (x : Bits) (z : ℕ) (r : Bits)
    (h : scan x = some (z, r)) : x = List.replicate z false ++ true :: r := by
  induction x generalizing z r with
  | nil => simp [scan] at h
  | cons b bs ih =>
    cases b with
    | true =>
      simp only [scan, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rfl
    | false =>
      simp only [scan, Option.map_eq_some_iff] at h
      obtain ⟨⟨k,t⟩, ht, he⟩ := h
      cases he
      simp [List.replicate_succ, ← ih k t ht]

def parseGamma (x : Bits) : Option (ℕ × Bits) := do
  let (z,r) ← scan x
  if z ≤ r.length then
    let n := value (true :: r.take z).reverse - 1
    if encodeGamma n = List.replicate z false ++ true :: r.take z then
      some (n, r.drop z)
    else none
  else none

theorem parseGamma_append (n : ℕ) (r : Bits) :
    parseGamma (encodeGamma n ++ r) = some (n,r) := by
  obtain ⟨w, hw⟩ := bits_msb (Nat.succ_ne_zero n)
  have hl : w.length = (n+1).size - 1 := by
    have := congrArg List.length hw
    simp [Nat.size_eq_bits_len] at this
    omega
  have hv : value (true :: w).reverse = n+1 := by
    rw [← hw, List.reverse_reverse, value_bits]
  have he : encodeGamma n = List.replicate w.length false ++ true :: w := by
    simp [encodeGamma, hw, hl]
  simp only [he, List.append_assoc, List.cons_append, parseGamma, scan_append]
  simp only [List.reverse_cons] at hv
  simp [hv, ← he]

theorem parseGamma_canonical (x : Bits) (n : ℕ) (r : Bits)
    (h : parseGamma x = some (n, r)) : x = encodeGamma n ++ r := by
  unfold parseGamma at h
  cases hs : scan x with
  | none => simp [hs] at h
  | some p =>
    obtain ⟨z,t⟩ := p
    simp only [hs, Option.bind_eq_bind', Option.bind_some] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    rw [scan_sound x z t hs, he]
    simp [List.append_assoc]

theorem parseGamma_eq_some_iff (x : Bits) (n : ℕ) (r : Bits) :
    parseGamma x = some (n,r) ↔ x = encodeGamma n ++ r :=
  ⟨parseGamma_canonical x n r, fun h => h ▸ parseGamma_append n r⟩

theorem parseGamma_consumes (x : Bits) (n : ℕ) (r : Bits)
    (h : parseGamma x = some (n, r)) : r.length < x.length := by
  rw [parseGamma_canonical x n r h, List.length_append]
  have := encodeGamma_nonempty n
  omega

theorem encodeGamma_prefix_free (m n : ℕ) (r : Bits)
    (h : encodeGamma m = encodeGamma n ++ r) : m = n ∧ r = [] := by
  have hm := parseGamma_append m []
  rw [List.append_nil, h, parseGamma_append] at hm
  simpa using hm.symm

def encodeAll (xs : List ℕ) : Bits := xs.flatMap encodeGamma

theorem encodeAll_count_le (xs : List ℕ) : xs.length ≤ (encodeAll xs).length := by
  induction xs with
  | nil => simp [encodeAll]
  | cons n xs ih =>
    have := encodeGamma_nonempty n
    simp only [encodeAll, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

/-- Fuel is the actual input bit length, never a decoded field value. -/
def decodeFuel : ℕ → Bits → Option (List ℕ)
  | _, [] => some []
  | 0, _ :: _ => none
  | k+1, b :: bs => do
    let (n,r) ← parseGamma (b::bs)
    let ns ← decodeFuel k r
    some (n::ns)

theorem decodeFuel_sound (k : ℕ) (x : Bits) (xs : List ℕ)
    (h : decodeFuel k x = some xs) : x = encodeAll xs := by
  induction k generalizing x xs with
  | zero =>
    cases x <;> simp_all [decodeFuel, encodeAll]
  | succ k ih =>
    cases x with
    | nil =>
      have he : xs = [] := by simpa [decodeFuel] using h.symm
      subst xs; rfl
    | cons b bs =>
      simp only [decodeFuel, Option.bind_eq_bind', Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨n,r⟩, hp, ns, hd, he⟩ := h
      cases he
      rw [parseGamma_canonical _ _ _ hp, ih r ns hd]
      rfl

theorem decodeFuel_encode (xs : List ℕ) (k : ℕ) (hk : xs.length ≤ k) :
    decodeFuel k (encodeAll xs) = some xs := by
  induction xs generalizing k with
  | nil => cases k <;> rfl
  | cons n xs ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      have hx : encodeAll (n::xs) ≠ [] := by
        have := encodeGamma_nonempty n
        simp only [encodeAll, List.flatMap_cons, ne_eq, List.append_eq_nil_iff]
        intro hn
        have := congrArg List.length hn.1
        simp_all
      obtain ⟨b,bs,hbs⟩ := List.exists_cons_of_ne_nil hx
      rw [hbs, decodeFuel, ← hbs]
      change (parseGamma (encodeGamma n ++ encodeAll xs) >>= _) = _
      rw [parseGamma_append]
      simp [ih k (by simpa using hk)]

def decodeAll (x : Bits) : Option (List ℕ) := decodeFuel x.length x

theorem decodeAll_eq_some_iff (x : Bits) (xs : List ℕ) :
    decodeAll x = some xs ↔ x = encodeAll xs := by
  constructor
  · exact decodeFuel_sound x.length x xs
  · rintro rfl
    exact decodeFuel_encode xs _ (encodeAll_count_le xs)

@[simp] theorem decodeAll_encode (xs : List ℕ) : decodeAll (encodeAll xs) = some xs :=
  (decodeAll_eq_some_iff _ _).2 rfl

theorem encodeAll_injective : Function.Injective encodeAll := by
  intro xs ys h
  have := congrArg decodeAll h
  simpa using this

theorem decodeAll_count_le_length (x : Bits) (xs : List ℕ)
    (h : decodeAll x = some xs) : xs.length ≤ x.length := by
  rw [(decodeAll_eq_some_iff _ _).1 h]
  exact encodeAll_count_le xs

theorem encodeAll_prefix_head (a b : ℕ) (xs ys : List ℕ) (r : Bits)
    (h : encodeAll (a::xs) ++ r = encodeAll (b::ys)) :
    a = b ∧ encodeAll xs ++ r = encodeAll ys := by
  have hp := congrArg parseGamma h
  simpa only [encodeAll, List.flatMap_cons, List.append_assoc,
    parseGamma_append, Option.some.injEq, Prod.mk.injEq] using hp

theorem encodeAll_prefix_same_count (xs ys : List ℕ) (r : Bits)
    (hc : xs.length = ys.length) (h : encodeAll xs ++ r = encodeAll ys) :
    xs = ys ∧ r = [] := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hc.symm
    subst ys
    simpa [encodeAll] using h
  | cons a xs ih =>
    cases ys with
    | nil => simp at hc
    | cons b ys =>
      obtain ⟨rfl,ht⟩ := encodeAll_prefix_head a b xs ys r h
      obtain ⟨rfl,hr⟩ := ih ys (by simpa using hc) ht
      exact ⟨rfl,hr⟩

end UAVProof.HubGammaCodec
