import LeanCompletion.UAV.TreeBudgetFeeScalingForward
import LeanCompletion.UAV.TreeBudgetFeeScalingBudget
import LeanCompletion.UAV.TreeBudgetFeeScalingBackward
import LeanCompletion.UAV.TreeBudgetFeeScalingBounds

namespace UAVProof.A4FeeScaling
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
set_option synthInstance.maxSize 4096
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def Fields (s : A4PairedParser.K → Bits) (es : List Row) (aT : ℤ) (bT : ℕ) : Prop :=
  s (A4PairedParser.ik (.inr (.result .nums)))=(es.map Prod.fst).flatMap encodeInt ∧
  s (A4PairedParser.ik (.inr (.result .dens)))=(es.map Prod.snd).flatMap encodeNat ∧
  s (A4PairedParser.ik (.inr (.result .bnum)))=encodeInt aT ∧
  s (A4PairedParser.ik (.inr (.result .bden)))=encodeNat bT

def prepare_run (saved : A4PairedParser.K → Bits) (es : List Row) (aT : ℤ) (bT L : ℕ)
    (hf : Fields saved es aT bT)
    (hn : ((es.map Prod.fst).flatMap encodeInt).length ≤ L)
    (hd : ((es.map Prod.snd).flatMap encodeNat).length ≤ L)
    (hbn : (encodeInt aT).length ≤ L) (hbd : (encodeNat bT).length ≤ L) :
    Run (cfg .copyNums {saved:=saved})
      (cfg .fTest (forwardState saved (encodeInt aT) (encodeNat bT) es [true] []))
      (8*L+13) := by
  let d0 := (⟨saved,fun _ => [],fun _ => []⟩ : Data)
  let d1 := put d0 (wr .nums) (store d0 (inputField .nums)++store d0 (wr .nums))
  have h1 : Run (cfg .copyNums d0) (cfg .copyDens d1) (2*(store d0 (inputField .nums)).length+3) :=
    copyData .copyNums .copyDens _ false rfl d0 rfl
  let d2 := put d1 (wr .dens) (store d1 (inputField .dens)++store d1 (wr .dens))
  have h2 : Run (cfg .copyDens d1) (cfg .copyBNum d2) (2*(store d1 (inputField .dens)).length+3) :=
    copyData .copyDens .copyBNum _ false rfl d1 rfl
  let d3 := put d2 (wr .bnum) (store d2 (inputField .bnum)++store d2 (wr .bnum))
  have h3 : Run (cfg .copyBNum d2) (cfg .copyBDen d3) (2*(store d2 (inputField .bnum)).length+3) :=
    copyData .copyBNum .copyBDen _ false rfl d2 rfl
  let d4 := put d3 (wr .bden) (store d3 (inputField .bden)++store d3 (wr .bden))
  have h4 : Run (cfg .copyBDen d3) (cfg .seed d4) (2*(store d3 (inputField .bden)).length+3) :=
    copyData .copyBDen .seed _ false rfl d3 rfl
  have h5 := pushData .seed .fTest (wr .pre) true rfl d4
  have he : put d4 (wr .pre) (true::store d4 (wr .pre))=
      forwardState saved (encodeInt aT) (encodeNat bT) es [true] [] := by
    apply data_ext
    · rfl
    · funext r; cases r <;> simp [d0,d1,d2,d3,d4,store,put,Function.update_apply,forwardState,inputField,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2]
    · rfl
  rw [he] at h5
  have run := seq (seq (seq (seq h1 h2) h3) h4) h5
  apply weaken run
  simp [d0,d1,d2,d3,d4,store,put,Function.update_apply,inputField,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2]
  simp only [List.length_flatMap,List.map_map] at hn hd
  omega

def coreBound (L : ℕ) := 8192*(L+2)^3

def outputData (saved : A4PairedParser.K → Bits) (es : List Row) (aT : ℤ) (bT : ℕ) :=
  backwardState saved (encodeInt (aT*(denProd es:ℤ))) [] []
    ((formula 1 bT es).flatMap encodeInt)

/-- Every loaded, copied, normalized and returned stack is included in the bound. -/
def core_run (saved : A4PairedParser.K → Bits) (es : List Row) (aT : ℤ) (bT L : ℕ)
    (hf : Fields saved es aT bT) (hn : es.length ≤ L)
    (hm : mass es+aT.natAbs.bits.length+bT.bits.length ≤ L)
    (hnums : ((es.map Prod.fst).flatMap encodeInt).length ≤ L)
    (hdens : ((es.map Prod.snd).flatMap encodeNat).length ≤ L)
    (hbn : (encodeInt aT).length ≤ L) (hbd : (encodeNat bT).length ≤ L) :
    Run (cfg .copyNums {saved:=saved})
      (TreeBudgetRegisterTM2.stopped (store (outputData saved es aT bT))) (coreBound L) := by
  have prep := prepare_run saved es aT bT L hf hnums hdens hbn hbd
  have fw := forward_loop saved (encodeInt aT) (encodeNat bT) es [true] [] (L+1) (by simpa using (show 1+mass es ≤ L+1 by omega))
  simp only [List.append_nil] at fw
  have hp := prefixEnd_length [true] es
  have hd := denWidth_le_mass es
  simp only [List.length_cons,List.length_nil] at hp
  have br := budget_run saved aT bT (prefixEnd [true] es) (history [true] es) (L+1) (by omega)
  have bw := backward_loop saved (encodeInt (aT*(value (prefixEnd [true] es):ℤ)))
    (history [true] es) bT.bits [] (L+1) (by omega)
    (history_fits [true] es bT.bits.length (L+1) (by simp only [List.length_cons,List.length_nil]; omega))
  have run := seq (seq (seq prep fw) br) bw
  have hs : (backward (history [true] es) bT.bits).2=formula 1 bT es := by
    simpa [value] using (backward_history [true] bT.bits es).2
  have hv : value (prefixEnd [true] es)=denProd es := by simp [prefixEnd_value,value]
  simp only [hs,List.append_nil,hv] at run
  apply weaken run
  simp only [history_length]
  have hh := Nat.mul_le_mul_right ((L+1+1)^2) hn
  unfold coreBound
  nlinarith only [hh]

end UAVProof.A4FeeScaling
