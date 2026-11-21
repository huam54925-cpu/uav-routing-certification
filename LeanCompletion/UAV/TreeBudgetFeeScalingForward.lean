import LeanCompletion.UAV.TreeBudgetFeeScalingOps

namespace UAVProof.A4FeeScaling
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition

set_option synthInstance.maxSize 4096
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-- One forward vertex: save the three fields, then update the prefix product. -/
def forward_round (saved : A4PairedParser.K → Bits) (bn bd : Bits)
    (e : Row) (es : List Row) (p : Bits) (hist : List Item) (B : ℕ)
    (hb : p.length+e.1.natAbs.bits.length+e.2.bits.length ≤ B) :
    Run (cfg .fTest (forwardState saved bn bd (e::es) p hist))
      (cfg .fTest (forwardState saved bn bd es (mulWord p e.2.bits) (⟨e.1,e.2,p⟩::hist)))
      (512*(B+1)^2) := by
  let d0 := forwardState saved bn bd (e::es) p hist
  let d1 := put (put d0 (wr .nums) (word e.1.natAbs.bits++(es.map Prod.fst).flatMap encodeInt)) (wr .signRev) ((decide (e.1<0))::store d0 (wr .signRev))
  have h1 : Run (cfg .fSign d0) (cfg .fA d1) (1) :=
    bitData .fSign .fA (wr .nums) (wr .signRev) rfl d0 (decide (e.1<0)) (word e.1.natAbs.bits++(es.map Prod.fst).flatMap encodeInt) rfl (by decide)
  let d2 := put (put d1 (wr .nums) ((es.map Prod.fst).flatMap encodeInt)) (wr .a) (e.1.natAbs.bits)
  have h2 : Run (cfg .fA d1) (cfg .fB d2) (3*(e.1.natAbs.bits).length+3) :=
    readData .fA .fB _ rfl d1 (e.1.natAbs.bits) ((es.map Prod.fst).flatMap encodeInt) rfl rfl rfl
  let d3 := put (put d2 (wr .dens) ((es.map Prod.snd).flatMap encodeNat)) (wr .b) (e.2.bits)
  have h3 : Run (cfg .fB d2) (cfg .fSaveA d3) (3*(e.2.bits).length+3) :=
    readData .fB .fSaveA _ rfl d2 (e.2.bits) ((es.map Prod.snd).flatMap encodeNat) rfl rfl rfl
  let d4 := put d3 (wr .numRev) (word (store d3 (wr .a))++store d3 (wr .numRev))
  have h4 : Run (cfg .fSaveA d3) (cfg .fSaveB d4) (2*(store d3 (wr .a)).length+3) :=
    copyData .fSaveA .fSaveB _ true rfl d3 rfl
  let d5 := put d4 (wr .denRev) (word (store d4 (wr .b))++store d4 (wr .denRev))
  have h5 : Run (cfg .fSaveB d4) (cfg .fSaveP d5) (2*(store d4 (wr .b)).length+3) :=
    copyData .fSaveB .fSaveP _ true rfl d4 rfl
  let d6 := put d5 (wr .prefixRev) (word (store d5 (wr .pre))++store d5 (wr .prefixRev))
  have h6 : Run (cfg .fSaveP d5) (cfg .fLoadP d6) (2*(store d5 (wr .pre)).length+3) :=
    copyData .fSaveP .fLoadP _ true rfl d5 rfl
  let d7 := put d6 (mr 0) (store d6 (wr .pre)++store d6 (mr 0))
  have h7 : Run (cfg .fLoadP d6) (cfg .fLoadB d7) (2*(store d6 (wr .pre)).length+3) :=
    copyData .fLoadP .fLoadB _ false rfl d6 rfl
  let d8 := put d7 (mr 1) (store d7 (wr .b)++store d7 (mr 1))
  have h8 : Run (cfg .fLoadB d7) (cfg .fMul d8) (2*(store d7 (wr .b)).length+3) :=
    copyData .fLoadB .fMul _ false rfl d7 rfl
  let d9 := multiplied d8
  have h9 : Run (cfg .fMul d8) (cfg .fClearP d9) (16*((d8.mult 0).length+(d8.mult 1).length+1)^2+3) :=
    mulData .fMul .fClearP rfl d8 rfl rfl rfl
  let d10 := put d9 (wr .pre) []
  have h10 : Run (cfg .fClearP d9) (cfg .fKeepP d10) ((store d9 (wr .pre)).length+2) :=
    clearData .fClearP .fKeepP _ rfl d9 rfl
  let d11 := put d10 (wr .pre) (store d10 (mr 2)++store d10 (wr .pre))
  have h11 : Run (cfg .fKeepP d10) (cfg .fClearProduct d11) (2*(store d10 (mr 2)).length+3) :=
    copyData .fKeepP .fClearProduct _ false rfl d10 rfl
  let d12 := put d11 (mr 2) []
  have h12 : Run (cfg .fClearProduct d11) (cfg .fClearA d12) ((store d11 (mr 2)).length+2) :=
    clearData .fClearProduct .fClearA _ rfl d11 rfl
  let d13 := put d12 (wr .a) []
  have h13 : Run (cfg .fClearA d12) (cfg .fClearB d13) ((store d12 (wr .a)).length+2) :=
    clearData .fClearA .fClearB _ rfl d12 rfl
  let d14 := put d13 (wr .b) []
  have h14 : Run (cfg .fClearB d13) (cfg .fTest d14) ((store d13 (wr .b)).length+2) :=
    clearData .fClearB .fTest _ rfl d13 rfl
  have ht : (store d0 (wr .dens)).isEmpty=false := by
    change (word e.2.bits++(es.map Prod.snd).flatMap encodeNat).isEmpty=false
    cases e.2.bits <;> rfl
  have test := testData .fTest .bSign .fSign (wr .dens) rfl d0
  simp only [ht,Bool.false_eq_true,ite_false] at test
  have run := seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (test) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14
  have he : d14=forwardState saved bn bd es (mulWord p e.2.bits) (⟨e.1,e.2,p⟩::hist) := by
    apply data_ext
    · rfl
    · funext r; cases r <;> simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,forwardState,store,put,multiplied,Function.update_apply]
    · funext i; fin_cases i <;> simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,forwardState,store,put,multiplied,Function.update_apply]
  rw [he] at run
  apply weaken run
  have hm := mulWord_length p e.2.bits
  have hp := Nat.pow_le_pow_left (show p.length+e.2.bits.length+1 ≤ B+1 by omega) 2
  simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,forwardState,store,put,multiplied,Function.update_apply]
  nlinarith

def forward_loop (saved : A4PairedParser.K → Bits) (bn bd : Bits)
    (es : List Row) (p : Bits) (hist : List Item) (B : ℕ)
    (hb : p.length+mass es ≤ B) :
    Run (cfg .fTest (forwardState saved bn bd es p hist))
      (cfg .bSign (forwardState saved bn bd [] (prefixEnd p es) (history p es++hist)))
      (512*es.length*(B+1)^2+1) := by
  induction es generalizing p hist with
  | nil =>
    simpa [prefixEnd,history,forwardState,store] using
      testData .fTest .bSign .fSign (wr .dens) rfl (forwardState saved bn bd [] p hist)
  | cons e es ih =>
    have hm := mulWord_length p e.2.bits
    change p.length+(e.1.natAbs.bits.length+e.2.bits.length+mass es) ≤ B at hb
    have a := forward_round saved bn bd e es p hist B (by omega)
    have b := ih (mulWord p e.2.bits) (⟨e.1,e.2,p⟩::hist) (by omega)
    have run := seq a b
    simpa [prefixEnd,history,List.append_assoc,Nat.add_mul,Nat.mul_add,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using run

end UAVProof.A4FeeScaling
