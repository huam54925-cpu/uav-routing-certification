import LeanCompletion.UAV.TreeBudgetFeeScalingOps

namespace UAVProof.A4FeeScaling
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
set_option synthInstance.maxSize 4096
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def budget_run (saved : A4PairedParser.K → Bits) (aT : ℤ) (bT : ℕ)
    (p : Bits) (hist : List Item) (B : ℕ)
    (hb : p.length+aT.natAbs.bits.length+bT.bits.length ≤ B) :
    Run (cfg .bSign (forwardState saved (encodeInt aT) (encodeNat bT) [] p hist))
      (cfg .rTest (backwardState saved (encodeInt (aT*(value p:ℤ))) hist bT.bits []))
      (512*(B+1)^2) := by
  let d0 := forwardState saved (encodeInt aT) (encodeNat bT) [] p hist
  let d1 := put (put d0 (wr .bnum) (word aT.natAbs.bits)) (wr .sign) ((decide (aT<0))::store d0 (wr .sign))
  have h1 : Run (cfg .bSign d0) (cfg .bA d1) (1) :=
    bitData .bSign .bA (wr .bnum) (wr .sign) rfl d0 (decide (aT<0)) (word aT.natAbs.bits) rfl (by decide)
  let d2 := put (put d1 (wr .bnum) ([])) (wr .a) (aT.natAbs.bits)
  have h2 : Run (cfg .bA d1) (cfg .bLoadA d2) (3*(aT.natAbs.bits).length+3) :=
    readData .bA .bLoadA _ rfl d1 (aT.natAbs.bits) ([]) (by simp only [List.append_nil]; rfl) rfl rfl
  let d3 := put d2 (mr 0) (store d2 (wr .a)++store d2 (mr 0))
  have h3 : Run (cfg .bLoadA d2) (cfg .bLoadP d3) (2*(store d2 (wr .a)).length+3) :=
    copyData .bLoadA .bLoadP _ false rfl d2 rfl
  let d4 := put d3 (mr 1) (store d3 (wr .pre)++store d3 (mr 1))
  have h4 : Run (cfg .bLoadP d3) (cfg .bMul d4) (2*(store d3 (wr .pre)).length+3) :=
    copyData .bLoadP .bMul _ false rfl d3 rfl
  let d5 := multiplied d4
  have h5 : Run (cfg .bMul d4) (cfg .bEmit d5) (16*((d4.mult 0).length+(d4.mult 1).length+1)^2+3) :=
    mulData .bMul .bEmit rfl d4 rfl rfl rfl
  let d6 := put (put (put d5 (wr .sign) []) (mr 2) []) (wr .budget) (encodeInt (TreeBudgetSignedWordTM2.signed (decide (aT<0)) (value (store d5 (mr 2))))++store d5 (wr .budget))
  have h6 : Run (cfg .bEmit d5) (cfg .bClearA d6) (2*(store d5 (mr 2)).length+3) :=
    emitData .bEmit .bClearA _ (wr .sign) rfl d5 (decide (aT<0)) [] rfl rfl (by decide)
  let d7 := put d6 (wr .a) []
  have h7 : Run (cfg .bClearA d6) (cfg .bClearP d7) ((store d6 (wr .a)).length+2) :=
    clearData .bClearA .bClearP _ rfl d6 rfl
  let d8 := put d7 (wr .pre) []
  have h8 : Run (cfg .bClearP d7) (cfg .bU d8) ((store d7 (wr .pre)).length+2) :=
    clearData .bClearP .bU _ rfl d7 rfl
  let d9 := put (put d8 (wr .bden) ([])) (wr .suf) (bT.bits)
  have h9 : Run (cfg .bU d8) (cfg .rTest d9) (3*(bT.bits).length+3) :=
    readData .bU .rTest _ rfl d8 (bT.bits) ([]) (by simp only [List.append_nil]; rfl) rfl rfl
  have run := seq (seq (seq (seq (seq (seq (seq (seq (h1) h2) h3) h4) h5) h6) h7) h8) h9
  have he : d9=backwardState saved (encodeInt (aT*(value p:ℤ))) hist bT.bits [] := by
    apply data_ext
    · rfl
    · funext r; cases r <;> simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,forwardState,backwardState,store,put,multiplied,Function.update_apply,TreeBudgetSignedWordTM2.signed_mul]
    · funext i; fin_cases i <;> simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,forwardState,backwardState,store,put,multiplied,Function.update_apply]
  rw [he] at run
  apply weaken run
  have hm := mulWord_length aT.natAbs.bits p
  have hp := Nat.pow_le_pow_left (show aT.natAbs.bits.length+p.length+1 ≤ B+1 by omega) 2
  simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,forwardState,backwardState,store,put,multiplied,Function.update_apply]
  nlinarith

end UAVProof.A4FeeScaling
