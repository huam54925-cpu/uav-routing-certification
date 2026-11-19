import LeanCompletion.UAV.TreeBudgetBinaryCodec
import LeanCompletion.UAV.TreeBudgetCertificate

/-! Canonical count/row entries, length-checked certificate decoding, and EOF.
List parsers retain the existing remaining-bit guard. Counts are never expanded. -/
namespace UAVProof.TreeBudgetSparseCodec

open TreeBudgetBinaryCodec TreeBudgetCertificate

abbrev RawEntry := ℕ × List ℕ
abbrev RawCertificate := List RawEntry

def encodeEntry (e : RawEntry) : Bits := encodeNat e.1 ++ encodeNats e.2

def parseEntry (bits : Bits) : Option (RawEntry × Bits) := do
  let (count, rest) ← parseNat bits
  let (row, tail) ← parseNats rest
  pure ((count, row), tail)

theorem encodeEntry_nonempty (e : RawEntry) : 1 ≤ (encodeEntry e).length := by
  have := encodeNat_nonempty e.1
  simp only [encodeEntry, List.length_append]
  omega

theorem parseEntry_append (e : RawEntry) (suffix : Bits) :
    parseEntry (encodeEntry e ++ suffix) = some (e, suffix) := by
  rcases e with ⟨count, row⟩
  simp [parseEntry, encodeEntry, List.append_assoc, parseNat_append]

theorem parseEntry_canonical (bits rest : Bits) (e : RawEntry)
    (h : parseEntry bits = some (e, rest)) : bits = encodeEntry e ++ rest := by
  simp only [parseEntry, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨count, tail⟩, hc, ⟨⟨row, tail'⟩, hr, he⟩⟩ := h
  cases he
  dsimp only at hr ⊢
  rw [parseNat_canonical bits tail count hc,
    parseList_canonical encodeNat parseNat parseNat_canonical tail tail' row hr]
  simp [encodeEntry, List.append_assoc]

def encodeRaw (xs : RawCertificate) : Bits := encodeList encodeEntry xs
def parseRawPrefix : Parser RawCertificate := parseList parseEntry

def parseRaw (bits : Bits) : Option RawCertificate := do
  let (xs, tail) ← parseRawPrefix bits
  if tail = [] then some xs else none

theorem parseRawPrefix_append (xs : RawCertificate) (suffix : Bits) :
    parseRawPrefix (encodeRaw xs ++ suffix) = some (xs, suffix) :=
  parseList_append _ _ parseEntry_append encodeEntry_nonempty xs suffix

theorem parseRawPrefix_canonical (bits rest : Bits) (xs : RawCertificate)
    (h : parseRawPrefix bits = some (xs, rest)) : bits = encodeRaw xs ++ rest :=
  parseList_canonical _ _ parseEntry_canonical bits rest xs h

@[simp] theorem parseRaw_encode (xs : RawCertificate) : parseRaw (encodeRaw xs) = some xs := by
  have h := parseRawPrefix_append xs []
  simp only [List.append_nil] at h
  simp [parseRaw, h]

theorem parseRaw_canonical (bits : Bits) (xs : RawCertificate)
    (h : parseRaw bits = some xs) : bits = encodeRaw xs := by
  simp only [parseRaw, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ys, rest⟩, hp, h⟩ := h
  dsimp only at h
  split_ifs at h with ht
  subst rest
  cases h
  simpa using parseRawPrefix_canonical bits [] xs hp

theorem parseRaw_trailing_rejected (xs : RawCertificate) (tail : Bits) (ht : tail ≠ []) :
    parseRaw (encodeRaw xs ++ tail) = none := by
  simp [parseRaw, parseRawPrefix_append, ht]

def Sized (n : ℕ) (xs : RawCertificate) : Prop := ∀ e ∈ xs, e.2.length = n
instance (n : ℕ) (xs : RawCertificate) : Decidable (Sized n xs) :=
  inferInstanceAs (Decidable (∀ e ∈ xs, e.2.length = n))

def ofRaw (n : ℕ) (xs : RawCertificate) (h : Sized n xs) : Certificate (Fin n) where
  size := xs.length
  count i := xs[i].1
  row i v := xs[i].2[v.val]'(by
    change v.val < xs[i.val].2.length
    rw [h _ (List.getElem_mem i.isLt)]
    exact v.isLt)

def toRaw {n : ℕ} (C : Certificate (Fin n)) : RawCertificate :=
  List.ofFn fun i => (C.count i, List.ofFn (C.row i))

@[simp] theorem toRaw_length {n : ℕ} (C : Certificate (Fin n)) : (toRaw C).length = C.size := by
  simp [toRaw]

theorem toRaw_sized {n : ℕ} (C : Certificate (Fin n)) : Sized n (toRaw C) := by
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  simp

@[simp] theorem toRaw_ofRaw (n : ℕ) (xs : RawCertificate) (h : Sized n xs) :
    toRaw (ofRaw n xs h) = xs := by
  apply List.ext_getElem
  · simp [toRaw, ofRaw]
  · intro i hi hj
    simp only [toRaw, List.getElem_ofFn]
    apply Prod.ext
    · rfl
    · apply List.ext_getElem
      · simpa using (h _ (List.getElem_mem hj)).symm
      · intro v hv hv'
        simp [ofRaw]

theorem toRaw_injective {n : ℕ} : Function.Injective (@toRaw n) := by
  rintro ⟨k, p, z⟩ ⟨l, q, w⟩ h
  have hk : k = l := by simpa using congrArg List.length h
  subst l
  have he := List.ofFn_injective h
  have hz : z = w := funext fun i => congrArg Prod.fst (congrFun he i)
  have hp : p = q := funext fun i => List.ofFn_injective (congrArg Prod.snd (congrFun he i))
  cases hz
  cases hp
  rfl

@[simp] theorem ofRaw_toRaw {n : ℕ} (C : Certificate (Fin n)) :
    ofRaw n (toRaw C) (toRaw_sized C) = C :=
  toRaw_injective (toRaw_ofRaw n (toRaw C) (toRaw_sized C))

def decodeRawCertificate (n : ℕ) (xs : RawCertificate) : Option (Certificate (Fin n)) :=
  if h : Sized n xs then some (ofRaw n xs h) else none

def decodeCertificate (n : ℕ) (bits : Bits) : Option (Certificate (Fin n)) :=
  (parseRaw bits).bind (decodeRawCertificate n)

def encodeCert {n : ℕ} (C : Certificate (Fin n)) : Bits := encodeRaw (toRaw C)

@[simp] theorem decodeCertificate_encode {n : ℕ} (C : Certificate (Fin n)) :
    decodeCertificate n (encodeCert C) = some C := by
  simp [decodeCertificate, encodeCert, decodeRawCertificate, toRaw_sized]

theorem decodeCertificate_canonical {n : ℕ} (bits : Bits) (C : Certificate (Fin n))
    (h : decodeCertificate n bits = some C) : bits = encodeCert C := by
  simp only [decodeCertificate, Option.bind_eq_some_iff] at h
  obtain ⟨xs, hx, hc⟩ := h
  unfold decodeRawCertificate at hc
  split_ifs at hc with hs
  cases hc
  simpa [encodeCert] using parseRaw_canonical bits xs hx

theorem decodeCertificate_iff {n : ℕ} (bits : Bits) (C : Certificate (Fin n)) :
    decodeCertificate n bits = some C ↔ bits = encodeCert C :=
  ⟨decodeCertificate_canonical bits C, fun h => h ▸ decodeCertificate_encode C⟩

theorem decodeCertificate_trailing_rejected {n : ℕ} (C : Certificate (Fin n))
    (tail : Bits) (ht : tail ≠ []) : decodeCertificate n (encodeCert C ++ tail) = none := by
  simp [decodeCertificate, encodeCert, parseRaw_trailing_rejected _ tail ht]

theorem wrong_row_length_rejected (n : ℕ) (xs : RawCertificate) (h : ¬ Sized n xs) :
    decodeCertificate n (encodeRaw xs) = none := by
  simp [decodeCertificate, decodeRawCertificate, h]

theorem excessive_entry_count_rejected (n count : ℕ) (tail : Bits) (h : tail.length < count) :
    decodeCertificate n (encodeNat count ++ tail) = none := by
  simp [decodeCertificate, parseRaw, parseRawPrefix, parseList_large_count _ count tail h]

theorem encodeCert_length {n : ℕ} (C : Certificate (Fin n)) :
    (encodeCert C).length = (encodeNat C.size).length +
      ∑ i, ((encodeNat (C.count i)).length + (encodeNats (List.ofFn (C.row i))).length) := by
  simp [encodeCert, encodeRaw, encodeList, toRaw, encodeEntry, List.length_flatMap,
    List.map_ofFn, List.sum_ofFn]

end UAVProof.TreeBudgetSparseCodec
