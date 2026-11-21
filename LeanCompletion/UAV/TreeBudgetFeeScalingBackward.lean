import LeanCompletion.UAV.TreeBudgetFeeScalingOps
namespace UAVProof.A4FeeScaling
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
set_option synthInstance.maxSize 4096
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-- Each intermediate configuration is explicit, so recursive calls share no
unevaluated chain of register updates. -/
def backward_round (saved : A4PairedParser.K → Bits) (budget : Bits)
    (e : Item) (es : List Item) (u out : Bits) (B : ℕ)
    (hb : e.pre.length+u.length+e.a.natAbs.bits.length+e.b.bits.length ≤ B) :
    Run (cfg .rTest (backwardState saved budget (e::es) u out))
      (cfg .rTest (backwardState saved budget es (mulWord e.b.bits u)
        (encodeInt (coefficient e u)++out))) (1024*(B+1)^2) := by
  let d0 := backwardState saved budget (e::es) u out
  let d1 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => word e.b.bits++es.flatMap (fun x => word x.b.bits)
        | .numRev => word e.a.natAbs.bits++es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => (decide (e.a<0))::es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | _ => []
      mult:=fun i => match i.val with

        | _ => [] }
  have h1 : Run (cfg .rP d0) (cfg .rB d1) (3*(e.pre).length+3) := by
    have step := readData .rP .rB _ rfl d0 (e.pre) (es.flatMap (fun x => word x.pre)) rfl rfl rfl
    have he : put (put d0 (wr .prefixRev) (es.flatMap (fun x => word x.pre))) (wr .pre) (e.pre)=d1 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d0,d1,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d0,d1,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d2 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => word e.a.natAbs.bits++es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => (decide (e.a<0))::es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | _ => []
      mult:=fun i => match i.val with

        | _ => [] }
  have h2 : Run (cfg .rB d1) (cfg .rA d2) (3*(e.b.bits).length+3) := by
    have step := readData .rB .rA _ rfl d1 (e.b.bits) (es.flatMap (fun x => word x.b.bits)) rfl rfl rfl
    have he : put (put d1 (wr .denRev) (es.flatMap (fun x => word x.b.bits))) (wr .b) (e.b.bits)=d2 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d1,d2,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d1,d2,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d3 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => (decide (e.a<0))::es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | _ => []
      mult:=fun i => match i.val with

        | _ => [] }
  have h3 : Run (cfg .rA d2) (cfg .rSign d3) (3*(e.a.natAbs.bits).length+3) := by
    have step := readData .rA .rSign _ rfl d2 (e.a.natAbs.bits) (es.flatMap (fun x => word x.a.natAbs.bits)) rfl rfl rfl
    have he : put (put d2 (wr .numRev) (es.flatMap (fun x => word x.a.natAbs.bits))) (wr .a) (e.a.natAbs.bits)=d3 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d2,d3,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d2,d3,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d4 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | .sign => [decide (e.a<0)]
        | _ => []
      mult:=fun i => match i.val with

        | _ => [] }
  have h4 : Run (cfg .rSign d3) (cfg .rLoadP d4) (1) := by
    have step := bitData .rSign .rLoadP (wr .signRev) (wr .sign) rfl d3 (decide (e.a<0)) (es.map (fun x => decide (x.a<0))) rfl (by decide)
    have he : put (put d3 (wr .signRev) (es.map (fun x => decide (x.a<0)))) (wr .sign) ((decide (e.a<0))::store d3 (wr .sign))=d4 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d3,d4,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d3,d4,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d5 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | .sign => [decide (e.a<0)]
        | _ => []
      mult:=fun i => match i.val with
        | 0 => e.pre
        | _ => [] }
  have h5 : Run (cfg .rLoadP d4) (cfg .rLoadU d5) (2*(e.pre).length+3) := by
    have step := copyData .rLoadP .rLoadU _ false rfl d4 rfl
    have he : put d4 (mr 0) (store d4 (wr .pre)++store d4 (mr 0))=d5 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d4,d5,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d4,d5,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d6 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | .sign => [decide (e.a<0)]
        | _ => []
      mult:=fun i => match i.val with
        | 0 => e.pre
        | 1 => u
        | _ => [] }
  have h6 : Run (cfg .rLoadU d5) (cfg .rFactor d6) (2*(u).length+3) := by
    have step := copyData .rLoadU .rFactor _ false rfl d5 rfl
    have he : put d5 (mr 1) (store d5 (wr .suf)++store d5 (mr 1))=d6 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d5,d6,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d5,d6,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d7 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | .sign => [decide (e.a<0)]
        | _ => []
      mult:=fun i => match i.val with
        | 2 => mulWord (e.pre) (u)
        | _ => [] }
  have h7 : Run (cfg .rFactor d6) (cfg .rLoadA d7) (16*((e.pre).length+(u).length+1)^2+3) := by
    have step := mulData .rFactor .rLoadA rfl d6 rfl rfl rfl
    have he : multiplied d6=d7 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d6,d7,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d6,d7,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d8 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | .sign => [decide (e.a<0)]
        | _ => []
      mult:=fun i => match i.val with
        | 0 => e.a.natAbs.bits
        | 2 => mulWord (e.pre) (u)
        | _ => [] }
  have h8 : Run (cfg .rLoadA d7) (cfg .rLoadFactor d8) (2*(e.a.natAbs.bits).length+3) := by
    have step := copyData .rLoadA .rLoadFactor _ false rfl d7 rfl
    have he : put d7 (mr 0) (store d7 (wr .a)++store d7 (mr 0))=d8 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d7,d8,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d7,d8,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d9 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | .sign => [decide (e.a<0)]
        | _ => []
      mult:=fun i => match i.val with
        | 0 => e.a.natAbs.bits
        | 1 => mulWord (e.pre) (u)
        | 2 => mulWord (e.pre) (u)
        | _ => [] }
  have h9 : Run (cfg .rLoadFactor d8) (cfg .rClearFactor d9) (2*(mulWord (e.pre) (u)).length+3) := by
    have step := copyData .rLoadFactor .rClearFactor _ false rfl d8 rfl
    have he : put d8 (mr 1) (store d8 (mr 2)++store d8 (mr 1))=d9 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d8,d9,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d8,d9,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d10 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | .sign => [decide (e.a<0)]
        | _ => []
      mult:=fun i => match i.val with
        | 0 => e.a.natAbs.bits
        | 1 => mulWord (e.pre) (u)
        | _ => [] }
  have h10 : Run (cfg .rClearFactor d9) (cfg .rFee d10) ((mulWord (e.pre) (u)).length+2) := by
    have step := clearData .rClearFactor .rFee _ rfl d9 rfl
    have he : put d9 (mr 2) []=d10 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d9,d10,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d9,d10,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d11 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | .sign => [decide (e.a<0)]
        | _ => []
      mult:=fun i => match i.val with
        | 2 => mulWord (e.a.natAbs.bits) (mulWord (e.pre) (u))
        | _ => [] }
  have h11 : Run (cfg .rFee d10) (cfg .rEmit d11) (16*((e.a.natAbs.bits).length+(mulWord (e.pre) (u)).length+1)^2+3) := by
    have step := mulData .rFee .rEmit rfl d10 rfl rfl rfl
    have he : multiplied d10=d11 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d10,d11,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d10,d11,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d12 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => encodeInt (coefficient e u)++out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | _ => []
      mult:=fun i => match i.val with

        | _ => [] }
  have h12 : Run (cfg .rEmit d11) (cfg .rLoadB d12) (2*(mulWord (e.a.natAbs.bits) (mulWord (e.pre) (u))).length+3) := by
    have step := emitData .rEmit .rLoadB _ (wr .sign) rfl d11 (decide (e.a<0)) [] rfl rfl (by decide)
    have he : put (put (put d11 (wr .sign) []) (mr 2) []) (wr .fees) (encodeInt (TreeBudgetSignedWordTM2.signed (decide (e.a<0)) (value (store d11 (mr 2))))++store d11 (wr .fees))=d12 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d11,d12,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d11,d12,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d13 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => encodeInt (coefficient e u)++out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | _ => []
      mult:=fun i => match i.val with
        | 0 => e.b.bits
        | _ => [] }
  have h13 : Run (cfg .rLoadB d12) (cfg .rLoadUAgain d13) (2*(e.b.bits).length+3) := by
    have step := copyData .rLoadB .rLoadUAgain _ false rfl d12 rfl
    have he : put d12 (mr 0) (store d12 (wr .b)++store d12 (mr 0))=d13 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d12,d13,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d12,d13,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d14 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => encodeInt (coefficient e u)++out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | _ => []
      mult:=fun i => match i.val with
        | 0 => e.b.bits
        | 1 => u
        | _ => [] }
  have h14 : Run (cfg .rLoadUAgain d13) (cfg .rSuffix d14) (2*(u).length+3) := by
    have step := copyData .rLoadUAgain .rSuffix _ false rfl d13 rfl
    have he : put d13 (mr 1) (store d13 (wr .suf)++store d13 (mr 1))=d14 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d13,d14,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d13,d14,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d15 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => encodeInt (coefficient e u)++out
        | .suf => u
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | _ => []
      mult:=fun i => match i.val with
        | 2 => mulWord (e.b.bits) (u)
        | _ => [] }
  have h15 : Run (cfg .rSuffix d14) (cfg .rClearU d15) (16*((e.b.bits).length+(u).length+1)^2+3) := by
    have step := mulData .rSuffix .rClearU rfl d14 rfl rfl rfl
    have he : multiplied d14=d15 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d14,d15,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d14,d15,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d16 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => encodeInt (coefficient e u)++out
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | _ => []
      mult:=fun i => match i.val with
        | 2 => mulWord (e.b.bits) (u)
        | _ => [] }
  have h16 : Run (cfg .rClearU d15) (cfg .rKeepU d16) ((u).length+2) := by
    have step := clearData .rClearU .rKeepU _ rfl d15 rfl
    have he : put d15 (wr .suf) []=d16 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d15,d16,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d15,d16,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d17 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => encodeInt (coefficient e u)++out
        | .suf => mulWord (e.b.bits) (u)
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | _ => []
      mult:=fun i => match i.val with
        | 2 => mulWord (e.b.bits) (u)
        | _ => [] }
  have h17 : Run (cfg .rKeepU d16) (cfg .rClearProduct d17) (2*(mulWord (e.b.bits) (u)).length+3) := by
    have step := copyData .rKeepU .rClearProduct _ false rfl d16 rfl
    have he : put d16 (wr .suf) (store d16 (mr 2)++store d16 (wr .suf))=d17 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d16,d17,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d16,d17,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d18 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => encodeInt (coefficient e u)++out
        | .suf => mulWord (e.b.bits) (u)
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | .a => e.a.natAbs.bits
        | _ => []
      mult:=fun i => match i.val with

        | _ => [] }
  have h18 : Run (cfg .rClearProduct d17) (cfg .rClearA d18) ((mulWord (e.b.bits) (u)).length+2) := by
    have step := clearData .rClearProduct .rClearA _ rfl d17 rfl
    have he : put d17 (mr 2) []=d18 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d17,d18,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d17,d18,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d19 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => encodeInt (coefficient e u)++out
        | .suf => mulWord (e.b.bits) (u)
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | .b => e.b.bits
        | _ => []
      mult:=fun i => match i.val with

        | _ => [] }
  have h19 : Run (cfg .rClearA d18) (cfg .rClearB d19) ((e.a.natAbs.bits).length+2) := by
    have step := clearData .rClearA .rClearB _ rfl d18 rfl
    have he : put d18 (wr .a) []=d19 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d18,d19,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d18,d19,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d20 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => encodeInt (coefficient e u)++out
        | .suf => mulWord (e.b.bits) (u)
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | .pre => e.pre
        | _ => []
      mult:=fun i => match i.val with

        | _ => [] }
  have h20 : Run (cfg .rClearB d19) (cfg .rClearP d20) ((e.b.bits).length+2) := by
    have step := clearData .rClearB .rClearP _ rfl d19 rfl
    have he : put d19 (wr .b) []=d20 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d19,d20,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d19,d20,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  let d21 : Data :=
    { saved:=saved
      work:=fun r => match r with
        | .budget => budget
        | .fees => encodeInt (coefficient e u)++out
        | .suf => mulWord (e.b.bits) (u)
        | .prefixRev => es.flatMap (fun x => word x.pre)
        | .denRev => es.flatMap (fun x => word x.b.bits)
        | .numRev => es.flatMap (fun x => word x.a.natAbs.bits)
        | .signRev => es.map (fun x => decide (x.a<0))
        | _ => []
      mult:=fun i => match i.val with

        | _ => [] }
  have h21 : Run (cfg .rClearP d20) (cfg .rTest d21) ((e.pre).length+2) := by
    have step := clearData .rClearP .rTest _ rfl d20 rfl
    have he : put d20 (wr .pre) []=d21 := by
      apply data_ext
      · rfl
      · funext r; cases r <;> simp [d20,d21,backwardState,store,put,multiplied,coefficient,TreeBudgetSignedWordTM2.signed_mul]
      · funext i; fin_cases i <;> simp [d20,d21,backwardState,store,put,multiplied]
    simp only [Bool.false_eq_true,ite_false] at step
    rw [he] at step
    exact step
  have ht : (store d0 (wr .prefixRev)).isEmpty=false := by
    change (word e.pre++es.flatMap (fun x => word x.pre)).isEmpty=false
    cases e.pre <;> rfl
  have test := testData .rTest .cleanup .rP (wr .prefixRev) rfl d0
  simp only [ht,Bool.false_eq_true,ite_false] at test
  have run := seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (test) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21
  have he : d21=backwardState saved budget es (mulWord e.b.bits u)
      (encodeInt (coefficient e u)++out) := by
    apply data_ext
    · rfl
    · funext r; cases r <;> rfl
    · rfl
  rw [he] at run
  apply weaken run
  have hm1 := mulWord_length e.pre u
  have hm2 := mulWord_length e.a.natAbs.bits (mulWord e.pre u)
  have hm3 := mulWord_length e.b.bits u
  have hp1 := Nat.pow_le_pow_left (show e.pre.length+u.length+1 ≤ B+1 by omega) 2
  have hp2 := Nat.pow_le_pow_left (show e.a.natAbs.bits.length+(mulWord e.pre u).length+1 ≤ B+1 by omega) 2
  have hp3 := Nat.pow_le_pow_left (show e.b.bits.length+u.length+1 ≤ B+1 by omega) 2
  nlinarith

def backward_loop (saved : A4PairedParser.K → Bits) (budget : Bits)
    (hist : List Item) (u out : Bits) (B : ℕ)
    (hu : u.length ≤ B) (hb : Fits hist u.length B) :
    Run (cfg .rTest (backwardState saved budget hist u out))
      (TreeBudgetRegisterTM2.stopped (store (backwardState saved budget [] []
        ((backward hist u).2.flatMap encodeInt++out))))
      (1024*hist.length*(B+1)^2+B+4) := by
  induction hist generalizing u out with
  | nil =>
    let d := backwardState saved budget [] u out
    have a := testData .rTest .cleanup .rP (wr .prefixRev) rfl d
    have b := clearData .cleanup .done _ rfl d rfl
    have he : put d (wr .suf) []=backwardState saved budget [] [] out := by
      apply data_ext
      · rfl
      · funext r; cases r <;> rfl
      · rfl
    rw [he] at b
    have c := haltData (backwardState saved budget [] [] out)
    have run := seq (seq a b) c
    change Run (cfg .rTest d) _ (1+(u.length+2)+1) at run
    simpa [backward] using weaken run (show 1+(u.length+2)+1 ≤ 1024*0*(B+1)^2+B+4 by omega)
  | cons e es ih =>
    have hm := mulWord_length e.b.bits u
    have a := backward_round saved budget e es u out B hb.1
    have b := ih (mulWord e.b.bits u) (encodeInt (coefficient e u)++out)
      (by have := hb.1; omega) (fits_mono es _ _ B (by omega) hb.2)
    have run := seq a b
    simpa [backward,List.flatMap_append,List.append_assoc,Nat.add_mul,Nat.mul_add,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run

end UAVProof.A4FeeScaling
