import LeanCompletion.UAV.TreeBudgetColumnCheckRuns
import LeanCompletion.UAV.TreeBudgetNaturalLookupIndex

namespace UAVProof.A4ColumnCheck
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn
open A4ColumnAccumulator Turing StateTransition

set_option synthInstance.maxSize 4096
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def records_round (s : Input) (v : ℕ) (h t : Bits) (e : RawEntry) (es : RawCertificate)
    (a : Bits) (B : ℕ) (hv : v<e.2.length)
    (hbody : ((e::es).flatMap encodeEntry).length≤B)
    (hindex : v.bits.length≤B)
    (hacc : countWidth (e::es)+max a.length (coordMax v (e::es))≤B) :
    Run (cfg .entry (state s v.bits h t ((e::es).flatMap encodeEntry) a))
      (cfg .entry (state s v.bits h t (es.flatMap encodeEntry)
        (TreeBudgetWeightedTM2.weighted e.1.bits (coord v e).bits a)))
      (4096*(B+1)^2) := by
  let d0 := state s v.bits h t ((e::es).flatMap encodeEntry) a
  have test := testData .entry .sumA .lookup (wr .cursor) rfl d0
  have ht : (store d0 (wr .cursor)).isEmpty=false := by
    change ((word e.1.bits++encodeNats e.2)++es.flatMap encodeEntry).isEmpty=false
    cases e.1.bits <;> rfl
  simp only [ht,Bool.false_eq_true,ite_false] at test
  let d1 := put (put (put d0 (wr .cursor) (es.flatMap encodeEntry)) (wr .row)
    (e.2.flatMap encodeNat)) (wr .count) e.1.bits
  have h1 : Run (cfg .lookup d0) (cfg .update d1)
      (24*(((e::es).flatMap encodeEntry).length+1)^2+2) :=
    entryData d0 e (es.flatMap encodeEntry) (by intro c; rfl) rfl rfl
      (parseEntry_append e (es.flatMap encodeEntry))
  let d2 := put d1 (wr .coord) (coord v e).bits
  have h2 : Run (cfg .update d1) (cfg .clearRow d2)
      (256*((e.2.flatMap encodeNat).length+v.bits.length+1)^2+2) :=
    lookupData d1 (coord v e).bits _ (by intro c; rfl) rfl rfl (A4NaturalLookup.lookup_getD e.2 v hv)
  let d3 := put (put (put d2 (wr .count) []) (wr .coord) []) (wr .acc)
    (TreeBudgetWeightedTM2.weighted e.1.bits (coord v e).bits a)
  have h3 : Run (cfg .clearRow d2) (cfg .sumB d3)
      (16*(e.1.bits.length+(coord v e).bits.length+a.length+1)^2+3) := weightedData d2 rfl rfl
  let d4 := put d3 (wr .row) []
  have h4 : Run (cfg .sumB d3) (cfg .entry d4) ((e.2.flatMap encodeNat).length+2) :=
    clearData .sumB .entry _ rfl d3 rfl
  have he : d4=state s v.bits h t (es.flatMap encodeEntry)
      (TreeBudgetWeightedTM2.weighted e.1.bits (coord v e).bits a) := by
    apply data_ext
    · rfl
    · funext r; cases r <;> simp [d0,d1,d2,d3,d4,state,put,Function.update_apply]
  have run := seq (seq (seq (seq test h1) h2) h3) h4
  rw [he] at run
  apply weaken run
  have hr : (e.2.flatMap encodeNat).length≤B := by
    simp only [List.flatMap_cons,List.length_append,encodeEntry,encodeNats,encodeList] at hbody
    omega
  have ha : e.1.bits.length+(coord v e).bits.length+a.length≤2*B := by
    simp only [countWidth,List.map_cons,List.sum_cons,coordMax] at hacc
    omega
  have hsq₁ := Nat.pow_le_pow_left (show ((e::es).flatMap encodeEntry).length+1≤B+1 by omega) 2
  have hsq₂ := Nat.pow_le_pow_left (show (e.2.flatMap encodeNat).length+v.bits.length+1≤2*(B+1) by omega) 2
  have hsq₃ := Nat.pow_le_pow_left (show e.1.bits.length+(coord v e).bits.length+a.length+1≤2*(B+1) by omega) 2
  nlinarith

def records_loop (s : Input) (v : ℕ) (h t : Bits) (es : RawCertificate)
    (a : Bits) (B : ℕ) (hv : ∀ e∈es, v<e.2.length)
    (hbody : (es.flatMap encodeEntry).length≤B)
    (hindex : v.bits.length≤B)
    (hacc : countWidth es+max a.length (coordMax v es)≤B) :
    Run (cfg .entry (state s v.bits h t (es.flatMap encodeEntry) a))
      (cfg .sumA (state s v.bits h t [] (columnWord v es a)))
      (4096*es.length*(B+1)^2+1) := by
  induction es generalizing a with
  | nil =>
    simpa [columnWord,state,store] using
      testData .entry .sumA .lookup (wr .cursor) rfl (state s v.bits h t [] a)
  | cons e es ih =>
    have head := records_round s v h t e es a B (hv e (by simp)) hbody hindex hacc
    have hb : (es.flatMap encodeEntry).length≤B := by
      simp only [List.flatMap_cons,List.length_append] at hbody
      omega
    have ha : countWidth es+max (TreeBudgetWeightedTM2.weighted e.1.bits (coord v e).bits a).length
        (coordMax v es)≤B := by
      have hw := TreeBudgetWeightedTM2.weighted_length e.1.bits (coord v e).bits a
      simp only [countWidth,List.map_cons,List.sum_cons,coordMax] at hacc ⊢
      omega
    have tail := ih _ (by intro e he; exact hv e (by simp [he])) hb ha
    simpa [columnWord,Nat.add_mul,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using seq head tail

end UAVProof.A4ColumnCheck
