import LeanCompletion.UAV.TreeBudgetSparseCodec

/-! Width bounds from consumed wire fragments alone. No semantic validity,
target multiplicity, completed parse, or successful verification is assumed. -/
namespace UAVProof.TreeBudgetSparsePrefixBounds
open TreeBudgetBinaryCodec TreeBudgetSparseCodec

def fieldBits (e : RawEntry) : ℕ := e.1.size + (e.2.map Nat.size).sum
def prefixBits (xs : RawCertificate) : ℕ := (xs.map fieldBits).sum

/-- The consumed entries occur between an arbitrary already-read header and an
arbitrary unread tail. In particular the tail may be truncated or malformed. -/
def Occupies (wire : Bits) (xs : RawCertificate) : Prop :=
  ∃ before after, wire = before ++ xs.flatMap encodeEntry ++ after

theorem parsed_prefix_occupies (before input rest : Bits) (count : ℕ)
    (xs : RawCertificate) (h : parseMany parseEntry count input = some (xs, rest)) :
    Occupies (before ++ input) xs := by
  refine ⟨before, rest, ?_⟩
  rw [parseMany_canonical encodeEntry parseEntry parseEntry_canonical count input rest xs h]
  simp [List.append_assoc]

theorem certificate_prefix_occupies (wire payload rest : Bits) (declared read : ℕ)
    (xs : RawCertificate) (hh : parseNat wire = some (declared, payload))
    (hp : parseMany parseEntry read payload = some (xs, rest)) : Occupies wire xs := by
  rw [parseNat_canonical wire payload declared hh]
  exact parsed_prefix_occupies _ _ _ _ _ hp

theorem occupies_take (wire : Bits) (xs : RawCertificate) (j : ℕ)
    (h : Occupies wire xs) : Occupies wire (xs.take j) := by
  obtain ⟨before, after, rfl⟩ := h
  refine ⟨before, (xs.drop j).flatMap encodeEntry ++ after, ?_⟩
  conv_lhs => rw [← List.take_append_drop j xs]
  simp only [List.flatMap_append, List.append_assoc]

theorem fields_fit_entry (e : RawEntry) : 2 * fieldBits e ≤ (encodeEntry e).length := by
  simp only [fieldBits, encodeEntry, List.length_append, encodeNat_length, encodeNats_length]
  omega

theorem fields_fit_payload (xs : RawCertificate) :
    2 * prefixBits xs ≤ (xs.flatMap encodeEntry).length := by
  induction xs with
  | nil => simp [prefixBits]
  | cons e xs ih =>
    have he := fields_fit_entry e
    simp only [prefixBits, List.map_cons, List.sum_cons] at *
    simp only [List.flatMap_cons, List.length_append]
    omega

theorem occupied_field_bits (wire : Bits) (xs : RawCertificate) (h : Occupies wire xs) :
    prefixBits xs ≤ wire.length / 2 := by
  obtain ⟨before, after, rfl⟩ := h
  have := fields_fit_payload xs
  simp only [List.length_append]
  omega

theorem occupied_entry_count (wire : Bits) (xs : RawCertificate) (h : Occupies wire xs) :
    xs.length ≤ wire.length := by
  obtain ⟨before, after, rfl⟩ := h
  have := length_le_flatMap encodeEntry encodeEntry_nonempty xs
  simp only [List.length_append]
  omega

theorem size_add_le (a b : ℕ) : (a + b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have hm : (a + 1) * (b + 1) ≤ 2 ^ a.size * 2 ^ b.size :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [pow_add]
  nlinarith

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

def weightedSum (xs : List (ℕ × ℕ)) : ℕ := (xs.map fun e => e.1 * e.2).sum
def pairBits (xs : List (ℕ × ℕ)) : ℕ := (xs.map fun e => e.1.size + e.2.size).sum

theorem weightedSum_size (xs : List (ℕ × ℕ)) : (weightedSum xs).size ≤ pairBits xs := by
  induction xs with
  | nil => simp [weightedSum, pairBits]
  | cons e xs ih =>
    have ha := size_add_le (e.1 * e.2) (weightedSum xs)
    have hm := size_mul_le e.1 e.2
    simp only [weightedSum, pairBits, List.map_cons, List.sum_cons] at *
    omega

/-- Missing coordinates are interpreted as zero for this bound only. The
certificate decoder still rejects every row with an incorrect length. -/
def columnPairs (xs : RawCertificate) (v : ℕ) : List (ℕ × ℕ) :=
  xs.map fun e => (e.1, e.2[v]?.getD 0)

theorem coordinate_size_le (row : List ℕ) (v : ℕ) :
    (row[v]?.getD 0).size ≤ (row.map Nat.size).sum := by
  induction row generalizing v with
  | nil => simp
  | cons a row ih =>
    cases v with
    | zero => simp
    | succ v => simpa using (ih v).trans (Nat.le_add_left _ a.size)

theorem column_field_bits (xs : RawCertificate) (v : ℕ) :
    pairBits (columnPairs xs v) ≤ prefixBits xs := by
  induction xs with
  | nil => simp [pairBits, columnPairs, prefixBits]
  | cons e xs ih =>
    have := coordinate_size_le e.2 v
    simp only [pairBits, columnPairs, prefixBits, List.map_cons, List.sum_cons, fieldBits] at *
    omega

theorem column_accumulator_width (wire : Bits) (xs : RawCertificate) (v : ℕ)
    (h : Occupies wire xs) :
    (weightedSum (columnPairs xs v)).size ≤ wire.length / 2 :=
  (weightedSum_size _).trans ((column_field_bits xs v).trans (occupied_field_bits wire xs h))

theorem parsed_column_accumulator_width (before input rest : Bits) (count : ℕ)
    (xs : RawCertificate) (v : ℕ)
    (h : parseMany parseEntry count input = some (xs, rest)) :
    (weightedSum (columnPairs xs v)).size ≤ (before ++ input).length / 2 :=
  column_accumulator_width _ xs v (parsed_prefix_occupies before input rest count xs h)

theorem every_partial_accumulator_width (wire : Bits) (xs : RawCertificate) (j v : ℕ)
    (h : Occupies wire xs) :
    (weightedSum (columnPairs (xs.take j) v)).size ≤ wire.length / 2 :=
  column_accumulator_width wire (xs.take j) v (occupies_take wire xs j h)

end UAVProof.TreeBudgetSparsePrefixBounds
