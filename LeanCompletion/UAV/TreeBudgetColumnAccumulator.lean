import LeanCompletion.UAV.TreeBudgetWeightedWidth
import LeanCompletion.UAV.TreeBudgetSparseCodec

namespace UAVProof.A4ColumnAccumulator
open TreeBudgetBinaryCodec TreeBudgetSparseCodec

def coord (v : ℕ) (e : RawEntry) : ℕ := e.2[v]?.getD 0
def countWidth (xs : RawCertificate) := (xs.map fun e => e.1.bits.length).sum
def coordMax (v : ℕ) : RawCertificate → ℕ
  | [] => 0
  | e::es => max (coord v e).bits.length (coordMax v es)

/-- The multiplier is the record count, so its occupied bit width is charged once. -/
def columnWord (v : ℕ) : RawCertificate → Bits → Bits
  | [],a => a
  | e::es,a => columnWord v es
      (TreeBudgetWeightedTM2.weighted e.1.bits (coord v e).bits a)

def columnSum (v : ℕ) (xs : RawCertificate) := (xs.map fun e => e.1*coord v e).sum

theorem columnWord_value (v : ℕ) (xs : RawCertificate) (a : Bits) :
    value (columnWord v xs a)=value a+columnSum v xs := by
  induction xs generalizing a <;>
    simp_all [columnWord,columnSum,TreeBudgetWeightedTM2.weighted_value,Nat.add_assoc]

theorem columnWord_width (v : ℕ) (xs : RawCertificate) (a : Bits) :
    (columnWord v xs a).length ≤ countWidth xs+max a.length (coordMax v xs) := by
  induction xs generalizing a with
  | nil => simp [columnWord,countWidth,coordMax]
  | cons e es ih =>
    have h := ih (TreeBudgetWeightedTM2.weighted e.1.bits (coord v e).bits a)
    have hw := TreeBudgetWeightedTM2.weighted_length e.1.bits (coord v e).bits a
    simp only [columnWord,countWidth,List.map_cons,List.sum_cons,coordMax] at *
    omega

theorem coord_width (v : ℕ) (xs : List ℕ) :
    (xs[v]?.getD 0).bits.length ≤ (xs.map fun n => n.bits.length).sum := by
  induction xs generalizing v with
  | nil => simp
  | cons x xs ih =>
    cases v with
    | zero => simp
    | succ v =>
      have h := ih v
      simp only [List.getElem?_cons_succ,List.map_cons,List.sum_cons]
      omega

theorem entry_width (v : ℕ) (e : RawEntry) :
    e.1.bits.length+(coord v e).bits.length ≤ (encodeEntry e).length := by
  have h := coord_width v e.2
  simp only [Nat.size_eq_bits_len] at h
  change (e.2[v]?.getD 0).size ≤ (e.2.map Nat.size).sum at h
  simp only [encodeEntry,List.length_append,encodeNat_length,encodeNats_length,
    coord,Nat.size_eq_bits_len]
  omega

/-- Counts and the selected coordinates occupy disjoint fields of the same raw body. -/
theorem occupied_width (v : ℕ) (xs : RawCertificate) :
    countWidth xs+coordMax v xs ≤ (xs.flatMap encodeEntry).length := by
  induction xs with
  | nil => simp [countWidth,coordMax]
  | cons e es ih =>
    have h := entry_width v e
    simp only [countWidth,List.map_cons,List.sum_cons,coordMax,
      List.flatMap_cons,List.length_append] at *
    omega

theorem columnWord_body_bound (v : ℕ) (xs : RawCertificate) :
    (columnWord v xs []).length ≤ (xs.flatMap encodeEntry).length := by
  have h := columnWord_width v xs []
  have occupied := occupied_width v xs
  simp only [List.length_nil, Nat.zero_max] at h
  omega

theorem prefix_value (v j : ℕ) (xs : RawCertificate) (a : Bits) :
    value (columnWord v (xs.take j) a)=value a+columnSum v (xs.take j) :=
  columnWord_value v (xs.take j) a

theorem prefix_width (v j : ℕ) (xs : RawCertificate) :
    (columnWord v (xs.take j) []).length ≤ (xs.flatMap encodeEntry).length := by
  have h := columnWord_body_bound v (xs.take j)
  have he := congrArg (fun es : RawCertificate => (es.flatMap encodeEntry).length)
    (List.take_append_drop j xs)
  simp only [List.flatMap_append,List.length_append] at he
  omega

/-- Binary addition likewise preserves a prefix invariant for total multiplicity. -/
def countWord : RawCertificate → Bits → Bits
  | [],a => a
  | e::es,a => countWord es (TreeBudgetAddWordsTM2.addWords a e.1.bits false)

theorem countWord_value (xs : RawCertificate) (a : Bits) :
    value (countWord xs a)=value a+(xs.map Prod.fst).sum := by
  induction xs generalizing a <;>
    simp_all [countWord,TreeBudgetAddWordsTM2.addWords_value,Nat.add_assoc]

theorem countWord_width (xs : RawCertificate) (a : Bits) :
    (countWord xs a).length ≤ a.length+countWidth xs+xs.length := by
  induction xs generalizing a with
  | nil => simp [countWord,countWidth]
  | cons e es ih =>
    have h := ih (TreeBudgetAddWordsTM2.addWords a e.1.bits false)
    have hw := TreeBudgetAddWordsTM2.addWords_length a e.1.bits false
    simp only [countWord,countWidth,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

theorem count_occupied (xs : RawCertificate) :
    countWidth xs+xs.length ≤ (xs.flatMap encodeEntry).length := by
  induction xs with
  | nil => simp [countWidth]
  | cons e es ih =>
    have he : e.1.bits.length+1 ≤ (encodeEntry e).length := by
      simp only [encodeEntry,List.length_append,encodeNat_length,Nat.size_eq_bits_len]
      omega
    simp only [countWidth,List.map_cons,List.sum_cons,List.length_cons,
      List.flatMap_cons,List.length_append] at *
    omega

theorem countWord_body_bound (xs : RawCertificate) :
    (countWord xs []).length ≤ (xs.flatMap encodeEntry).length := by
  have h := countWord_width xs []
  have occupied := count_occupied xs
  simp only [List.length_nil,Nat.zero_add] at h
  omega

end UAVProof.A4ColumnAccumulator
