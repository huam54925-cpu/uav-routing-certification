import LeanCompletion.UAV.TreeBudgetRowCheckFinish
import LeanCompletion.UAV.TreeBudgetRowCheckModel

namespace UAVProof.A4RowCheck
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2CallOn Turing StateTransition
open TreeBudgetSemanticRegisterTM2 A4RowCheckModel
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def body (vs : List Node) (f : Node → ℕ) : Bits := (vs.map f).flatMap encodeNat
def loopState (base : K → Bits) (vs : List Node) (q : WordState) : K → Bits :=
  ready base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
    (body vs Node.plus) (body vs Node.minus) q.1 q.2.1 q.2.2
def fieldState (base : K → Bits) (vs : List Node) (v : Node) (q : WordState) : K → Bits :=
  state base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
    (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
      q.1 q.2.1 q.2.2

def vertex_run (base : K → Bits) (rows Ap An : List ℕ) (root : ℕ)
    (hr : base (reg 5)=root.bits) (hrow : base (reg 2)=rows.flatMap encodeNat)
    (hap : base (reg 3)=Ap.flatMap encodeNat) (han : base (reg 4)=An.flatMap encodeNat)
    (v : Node) (vs : List Node) (q : WordState)
    (hp : v.parent<rows.length) (hpA : v.parent<Ap.length) (hpN : v.parent<An.length) :
    Execution (cfg .loop (loopState base (v::vs) q))
      (if nodePass rows root v then cfg .loop (loopState base vs (nodeStep Ap An root v q))
        else ⟨none,(none,false),retained base⟩) := by
  have read := read_fields base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
    (body vs Node.plus) (body vs Node.minus) q.1 q.2.1 q.2.2 v.parent v.cap v.coord v.plus v.minus
  have readProp := read.property
  change Run instructions (cfg .loop (loopState base (v::vs) q)) (cfg .capU (fieldState base vs v q)) read.val at readProp
  have cap := cap_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
    (body vs Node.plus) (body vs Node.minus) v.parent.bits v.plus.bits v.minus.bits q.1 q.2.1 q.2.2 v.cap v.coord
  have capProp := cap.property
  change Run instructions (cfg .capU (fieldState base vs v q))
    (cfg (if v.coord≤v.cap then .selfPosU else bad) (fieldState base vs v q)) cap.val at capProp
  by_cases hcap : v.coord≤v.cap
  · simp only [if_pos hcap] at capProp
    let qself : WordState :=
      (TreeBudgetWeightedTM2.weighted v.coord.bits v.plus.bits q.1,
       TreeBudgetWeightedTM2.weighted v.coord.bits v.minus.bits q.2.1,q.2.2)
    have self := self_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
      (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits q.1 q.2.1 q.2.2
    have selfProp := self.property
    change Run instructions (cfg .selfPosU (fieldState base vs v q)) (cfg .parentLeft (fieldState base vs v qself)) self.val at selfProp
    have choice := parent_choice base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
      (body vs Node.plus) (body vs Node.minus) v.cap.bits v.coord.bits v.plus.bits v.minus.bits qself.1 qself.2.1 qself.2.2
      v.parent root hr
    have choiceProp := choice.property
    change Run instructions (cfg .parentLeft (fieldState base vs v qself))
      (cfg (if v.parent=root then .rootAddU else .parentNonzero) (fieldState base vs v qself)) choice.val at choiceProp
    have pre := seq instructions (seq instructions (seq instructions readProp capProp) selfProp) choiceProp
    by_cases hroot : v.parent=root
    · simp only [if_pos hroot] at pre
      have mass := root_mass_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
        (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
        qself.1 qself.2.1 qself.2.2
      have clean := round_clear_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
        (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
        qself.1 qself.2.1 (TreeBudgetWeightedTM2.weighted v.coord.bits [true] qself.2.2)
      have run := seq instructions (seq instructions pre mass.property) clean.property
      exact ⟨_, by simpa [nodePass,nodeStep,hcap,hroot,loopState,fieldState,qself] using run⟩
    · simp only [if_neg hroot] at pre
      have parent := parent_test_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
        (body vs Node.plus) (body vs Node.minus) v.cap.bits v.plus.bits v.minus.bits
        qself.1 qself.2.1 qself.2.2 rows v.parent v.coord hp hrow
      have parentProp := parent.property
      change Run instructions (cfg .parentNonzero (fieldState base vs v qself))
        (cfg (if v.coord=0 then .roundClear 0 else if rows[v.parent]=0 then bad else .parentPosLookup)
          (fieldState base vs v qself)) parent.val at parentProp
      have pre2 := seq instructions pre parentProp
      by_cases hzero : v.coord=0
      · simp only [if_pos hzero] at pre2
        have clean := round_clear_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
          (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
          qself.1 qself.2.1 qself.2.2
        have run := seq instructions pre2 clean.property
        exact ⟨_, by simpa [nodePass,nodeStep,hcap,hroot,hzero,loopState,fieldState,qself] using run⟩
      · simp only [if_neg hzero] at pre2
        by_cases hparent : rows[v.parent]=0
        · simp only [if_pos hparent] at pre2
          have clean := cleanup_state_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
            (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
            qself.1 qself.2.1 qself.2.2 false
          have run := seq instructions pre2 clean.property
          have hpos : 0<v.coord := by omega
          exact ⟨_, by simpa [nodePass,hcap,hroot,hpos,List.getElem?_eq_getElem hp,hparent,bad,fieldState] using run⟩
        · simp only [if_neg hparent] at pre2
          have fees := parent_fees_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
            (body vs Node.plus) (body vs Node.minus) v.cap.bits v.coord.bits v.plus.bits v.minus.bits
            qself.1 qself.2.1 qself.2.2 Ap An v.parent hpA hpN hap han
          have clean := round_clear_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
            (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
            (TreeBudgetWeightedTM2.weighted v.coord.bits Ap[v.parent].bits qself.1)
            (TreeBudgetWeightedTM2.weighted v.coord.bits An[v.parent].bits qself.2.1) qself.2.2
          have run := seq instructions (seq instructions pre2 fees.property) clean.property
          have hpos : 0<rows[v.parent] := by omega
          exact ⟨_, by simpa [nodePass,nodeStep,hcap,hroot,hzero,List.getElem?_eq_getElem hp,
            List.getElem?_eq_getElem hpA,List.getElem?_eq_getElem hpN,hpos,loopState,fieldState,qself] using run⟩
  · simp only [if_neg hcap] at capProp
    have clean := cleanup_state_run base (body vs Node.parent) (body vs Node.cap) (body vs Node.coord)
      (body vs Node.plus) (body vs Node.minus) v.parent.bits v.cap.bits v.coord.bits v.plus.bits v.minus.bits
      q.1 q.2.1 q.2.2 false
    have run := seq instructions (seq instructions readProp capProp) clean.property
    exact ⟨_, by simpa [nodePass,hcap,bad,fieldState] using run⟩

def loop_run (base : K → Bits) (rows Ap An : List ℕ) (root : ℕ)
    (hr : base (reg 5)=root.bits) (hrow : base (reg 2)=rows.flatMap encodeNat)
    (hap : base (reg 3)=Ap.flatMap encodeNat) (han : base (reg 4)=An.flatMap encodeNat)
    (vs : List Node) (q : WordState)
    (hp : ∀ v∈vs, v.parent<rows.length ∧ v.parent<Ap.length ∧ v.parent<An.length) :
    Execution (cfg .loop (loopState base vs q))
      ⟨none,(none,loopResult rows Ap An root vs q),retained base⟩ := by
  induction vs generalizing q with
  | nil => exact final_run base q.1 q.2.1 q.2.2
  | cons v vs ih =>
    have hv := hp v (by simp)
    have one := vertex_run base rows Ap An root hr hrow hap han v vs q hv.1 hv.2.1 hv.2.2
    have tail := ih (nodeStep Ap An root v q) (by intro u hu; exact hp u (by simp [hu]))
    exact if h : nodePass rows root v = true then
      ⟨_, by
        have oneProp := one.property
        simp only [h,ite_true] at oneProp
        simpa [loopResult,h] using seq instructions oneProp tail.property⟩
    else
      ⟨one.val, by
        have hf : nodePass rows root v=false := Bool.eq_false_iff.mpr h
        simpa [loopResult,hf] using one.property⟩

end UAVProof.A4RowCheck
