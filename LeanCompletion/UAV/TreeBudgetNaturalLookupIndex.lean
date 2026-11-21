import LeanCompletion.UAV.TreeBudgetNaturalLookupRuns

namespace UAVProof.A4NaturalLookup
open TreeBudgetBinaryCodec

def lookup_index (xs : List ℕ) (i : ℕ) (hi : i<xs.length) :
    Run (start (xs.flatMap encodeNat) i.bits)
      (stopped (xs.flatMap encodeNat) i.bits xs[i].bits)
      (256*((xs.flatMap encodeNat).length+i.bits.length+1)^2) := by
  have he : xs.take i++xs[i]::xs.drop (i+1)=xs := by
    rw [← List.drop_eq_getElem_cons hi,List.take_append_drop]
  have hl : (xs.take i).length=i := List.length_take_of_le (by omega)
  simpa only [he,hl] using lookup_run (xs.take i) (xs.drop (i+1)) xs[i]

def lookup_getD (xs : List ℕ) (i : ℕ) (hi : i<xs.length) :
    Run (start (xs.flatMap encodeNat) i.bits)
      (stopped (xs.flatMap encodeNat) i.bits (xs[i]?.getD 0).bits)
      (256*((xs.flatMap encodeNat).length+i.bits.length+1)^2) := by
  simpa only [List.getElem?_eq_getElem hi,Option.getD_some] using lookup_index xs i hi

end UAVProof.A4NaturalLookup
