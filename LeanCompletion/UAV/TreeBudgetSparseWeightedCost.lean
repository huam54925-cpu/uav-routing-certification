import LeanCompletion.UAV.TreeBudgetSparsePrefixBounds
import LeanCompletion.UAV.TreeBudgetBitPrimitives

/-! Dynamic binary multiply/add and column extraction costs. Tree validation,
scaling, and the full verifier are separate obligations. -/
namespace UAVProof.TreeBudgetSparseWeightedCost
open TreeBudgetBitMachine TreeBudgetBitPrimitives TreeBudgetSparsePrefixBounds
open TreeBudgetBinaryCodec TreeBudgetSparseCodec

def accumulateD : ℕ → List (ℕ × ℕ) → Costed ℕ
  | acc, [] => ⟨acc, 1, 0⟩
  | acc, e :: xs =>
    let product := mulNatD e.1 e.2
    let next := addNatD acc product.value
    let tail := accumulateD next.value xs
    ⟨tail.value, product.steps + next.steps + tail.steps + 3,
      product.allocations + next.allocations + tail.allocations⟩

@[simp] theorem accumulateD_value (acc : ℕ) (xs : List (ℕ × ℕ)) :
    (accumulateD acc xs).value = acc + weightedSum xs := by
  induction xs generalizing acc with
  | nil => simp [accumulateD, weightedSum]
  | cons e xs ih => simp [accumulateD, ih, weightedSum, Nat.add_assoc]

theorem accumulator_width (acc : ℕ) (xs : List (ℕ × ℕ)) :
    (accumulateD acc xs).value.size ≤ acc.size + pairBits xs := by
  rw [accumulateD_value]
  exact (size_add_le _ _).trans (Nat.add_le_add_left (weightedSum_size xs) _)

/-- The budget includes every remaining field and the current accumulator.
It is preserved after each multiply/add, without a target-value hypothesis. -/
theorem accumulateD_work (acc : ℕ) (xs : List (ℕ × ℕ)) (B : ℕ)
    (h : acc.size + pairBits xs ≤ B) :
    (accumulateD acc xs).steps + (accumulateD acc xs).allocations ≤
      xs.length * (320 * (B + 1) ^ 2) + 1 := by
  induction xs generalizing acc with
  | nil => simp [accumulateD]
  | cons e xs ih =>
    have hf : acc.size + (e.1.size + e.2.size + pairBits xs) ≤ B := by
      simpa [pairBits] using h
    have ha : acc.size ≤ B := by omega
    have hc : e.1.size ≤ B := by omega
    have hp : e.2.size ≤ B := by omega
    have hprod : (e.1 * e.2).size ≤ B := (size_mul_le _ _).trans (by omega)
    have hn := size_add_le acc (e.1 * e.2)
    have hm := size_mul_le e.1 e.2
    have ht := ih (acc + e.1 * e.2) (by omega)
    have ms := mulNatD_steps e.1 e.2 B hc hp
    have ma := mulNatD_allocations e.1 e.2 B hc hp
    have ads := (dynamic_steps acc (e.1 * e.2) B ha hprod).2.2.2
    have ada := (dynamic_allocations acc (e.1 * e.2) B ha hprod).2.2.2
    simp only [accumulateD, mulNatD_value, addNatD_value, List.length_cons]
    nlinarith

theorem occupied_column_arithmetic_work (wire : Bits) (xs : RawCertificate) (v : ℕ)
    (h : Occupies wire xs) :
    (accumulateD 0 (columnPairs xs v)).steps +
      (accumulateD 0 (columnPairs xs v)).allocations ≤
      wire.length * (320 * (wire.length / 2 + 1) ^ 2) + 1 := by
  have hb := (column_field_bits xs v).trans (occupied_field_bits wire xs h)
  have ht := accumulateD_work 0 (columnPairs xs v) (wire.length / 2) (by simpa using hb)
  have hn := occupied_entry_count wire xs h
  simp only [columnPairs, List.length_map] at ht
  exact ht.trans (by gcongr)

/-- Sequential row access with a binary counter; no unit-cost random access. -/
def coordinateD : List ℕ → ℕ → Costed ℕ
  | [], _ => ⟨0, 1, 0⟩
  | a :: row, v =>
    let test := zeroNatD v
    if test.value then ⟨a, test.steps + 1, test.allocations⟩ else
      let dec := subNatD v 1
      let tail := coordinateD row dec.value
      ⟨tail.value, test.steps + dec.steps + tail.steps + 2,
        test.allocations + dec.allocations + tail.allocations⟩

@[simp] theorem coordinateD_value (row : List ℕ) (v : ℕ) :
    (coordinateD row v).value = row[v]?.getD 0 := by
  induction row generalizing v with
  | nil => simp [coordinateD]
  | cons a row ih => cases v <;> simp [coordinateD, ih]

theorem coordinateD_work (row : List ℕ) (v B : ℕ) (hB : 1 ≤ B) (hv : v.size ≤ B) :
    (coordinateD row v).steps + (coordinateD row v).allocations ≤
      (row.length + 1) * (160 * (B + 1)) := by
  induction row generalizing v with
  | nil => simp only [coordinateD, List.length_nil]; omega
  | cons a row ih =>
    have zs := (dynamic_steps v 0 B hv (by simp)).1
    have za := (dynamic_allocations v 0 B hv (by simp)).1
    change (zeroNatD v).steps ≤ _ at zs
    change (zeroNatD v).allocations ≤ _ at za
    have ds := (dynamic_steps v 1 B hv (by simpa using hB)).2.2.1
    have da := (dynamic_allocations v 1 B hv (by simpa using hB)).2.2.1
    have ht := ih (v - 1) ((Nat.size_le_size (Nat.sub_le _ _)).trans hv)
    simp only [coordinateD, subNatD_value, List.length_cons]
    split_ifs <;> dsimp only <;> nlinarith

def extractD : RawCertificate → ℕ → Costed (List (ℕ × ℕ))
  | [], _ => ⟨[], 1, 0⟩
  | e :: xs, v =>
    let head := coordinateD e.2 v
    let tail := extractD xs v
    ⟨(e.1, head.value) :: tail.value, head.steps + tail.steps + 2,
      head.allocations + tail.allocations + 2⟩

@[simp] theorem extractD_value (xs : RawCertificate) (v : ℕ) :
    (extractD xs v).value = columnPairs xs v := by
  induction xs <;> simp [extractD, columnPairs, *]

theorem extractD_work (xs : RawCertificate) (v B : ℕ) (hB : 1 ≤ B) (hv : v.size ≤ B) :
    (extractD xs v).steps + (extractD xs v).allocations ≤
      (xs.flatMap encodeEntry).length * (164 * (B + 1)) + 1 := by
  induction xs with
  | nil => simp [extractD]
  | cons e xs ih =>
    have hc := coordinateD_work e.2 v B hB hv
    have he : e.2.length + 1 ≤ (encodeEntry e).length := by
      simp only [encodeEntry, List.length_append, encodeNat_length, encodeNats_length]
      omega
    have hm := Nat.mul_le_mul_right (164 * (B + 1)) he
    simp only [extractD, List.flatMap_cons, List.length_append]
    nlinarith

def columnD (xs : RawCertificate) (v : ℕ) : Costed ℕ :=
  let pairs := extractD xs v
  let out := accumulateD 0 pairs.value
  ⟨out.value, pairs.steps + out.steps + 1, pairs.allocations + out.allocations⟩

@[simp] theorem columnD_value (xs : RawCertificate) (v : ℕ) :
    (columnD xs v).value = weightedSum (columnPairs xs v) := by simp [columnD]

/-- All fields may exceed the input targets. The only extra size bound is on
the coordinate index; in the complete verifier this comes from input length. -/
theorem occupied_column_work (wire : Bits) (xs : RawCertificate) (v B : ℕ)
    (h : Occupies wire xs) (hB : 1 ≤ B) (hv : v.size ≤ B) :
    (columnD xs v).steps + (columnD xs v).allocations ≤
      wire.length * (164 * (B + 1)) +
      wire.length * (320 * (wire.length / 2 + 1) ^ 2) + 3 := by
  have he := extractD_work xs v B hB hv
  have ha := occupied_column_arithmetic_work wire xs v h
  have hl : (xs.flatMap encodeEntry).length ≤ wire.length := by
    obtain ⟨before, after, rfl⟩ := h
    simp only [List.length_append]
    omega
  have hm := Nat.mul_le_mul_right (164 * (B + 1)) hl
  simp only [columnD, extractD_value]
  omega

theorem columnD_toRaw {n : ℕ} (C : TreeBudgetCertificate.Certificate (Fin n)) (v : Fin n) :
    (columnD (toRaw C) v.val).value =
      (List.ofFn fun i => C.count i * C.row i v).sum := by
  simp [columnD_value, weightedSum, columnPairs, toRaw, List.map_ofFn, Function.comp_def]

theorem decoded_occupation {n : ℕ} (wire : Bits)
    (C : TreeBudgetCertificate.Certificate (Fin n))
    (h : decodeCertificate n wire = some C) : Occupies wire (toRaw C) := by
  rw [decodeCertificate_canonical wire C h]
  exact ⟨encodeNat C.size, [], by simp [encodeCert, encodeRaw, encodeList]⟩

/-- Refinement to the original weighted column expression, on every decoded
certificate, even when counts, rows, budget or column totals are invalid. -/
theorem decoded_column_work {n : ℕ} (wire : Bits)
    (C : TreeBudgetCertificate.Certificate (Fin n)) (v : Fin n) (B : ℕ)
    (h : decodeCertificate n wire = some C) (hB : 1 ≤ B) (hv : v.val.size ≤ B) :
    (columnD (toRaw C) v.val).value = (List.ofFn fun i => C.count i * C.row i v).sum ∧
    (columnD (toRaw C) v.val).steps + (columnD (toRaw C) v.val).allocations ≤
      wire.length * (164 * (B + 1)) +
      wire.length * (320 * (wire.length / 2 + 1) ^ 2) + 3 :=
  ⟨columnD_toRaw C v,
    occupied_column_work wire (toRaw C) v.val B (decoded_occupation wire C h) hB hv⟩

theorem decoded_dimension_le_wire {n : ℕ} (wire : Bits)
    (C : TreeBudgetCertificate.Certificate (Fin n))
    (h : decodeCertificate n wire = some C) (hc : 0 < C.size) : n ≤ wire.length := by
  let i : Fin C.size := ⟨0, hc⟩
  let e : RawEntry := (C.count i, List.ofFn (C.row i))
  have he : e ∈ toRaw C := List.mem_ofFn.mpr ⟨i, rfl⟩
  have hn : n ≤ (encodeEntry e).length := by
    simp only [e, encodeEntry, List.length_append, encodeNat_length, encodeNats_length,
      List.length_ofFn]
    omega
  have hm : (encodeEntry e).length ≤ ((toRaw C).flatMap encodeEntry).length := by
    rw [List.length_flatMap]
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨e, he, rfl⟩)
  obtain ⟨before, after, hw⟩ := decoded_occupation wire C h
  have hl := congrArg List.length hw
  simp only [List.length_append] at hl
  omega

/-- A single decoded column costs a polynomial of the certificate length
alone. For a nonempty certificate its rows encode n coordinates, bounding
the index; an empty certificate is handled without traversing any row. -/
theorem decoded_column_wire_work {n : ℕ} (wire : Bits)
    (C : TreeBudgetCertificate.Certificate (Fin n)) (v : Fin n)
    (h : decodeCertificate n wire = some C) :
    (columnD (toRaw C) v.val).steps + (columnD (toRaw C) v.val).allocations ≤
      512 * (wire.length + 1) ^ 3 := by
  by_cases hz : C.size = 0
  · have he : toRaw C = [] := by simpa only [← List.length_eq_zero_iff, toRaw_length] using hz
    simp only [he, columnD, extractD, accumulateD]
    nlinarith [Nat.zero_le (wire.length ^ 2), Nat.zero_le (wire.length ^ 3)]
  · have hn := decoded_dimension_le_wire wire C h (by omega)
    have hv : v.val.size ≤ wire.length + 1 := by
      have hs : v.val.size ≤ v.val := Nat.size_le.mpr (Nat.lt_two_pow_self (n := v.val))
      have := v.isLt
      omega
    have ht := (decoded_column_work wire C v (wire.length + 1) h (by omega) hv).2
    have hs : (wire.length / 2 + 1) ^ 2 ≤ (wire.length + 1) ^ 2 := by
      gcongr
      exact Nat.div_le_self _ _
    have hm := Nat.mul_le_mul_left (320 * wire.length) hs
    nlinarith [Nat.zero_le (wire.length ^ 2), Nat.zero_le (wire.length ^ 3)]

end UAVProof.TreeBudgetSparseWeightedCost
