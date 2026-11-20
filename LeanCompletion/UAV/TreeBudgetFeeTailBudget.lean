import LeanCompletion.UAV.TreeBudgetFeeTailGroups

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
set_option synthInstance.maxSize 2048
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def scalarField (g : Bool) : FeeField := if g then .bden else .bnum
def scalarEntry (g : Bool) : L := if g then .marker .bden false else .sign .bnum
def scalarEnd (g : Bool) (base : K → Bits) (s : Bits) : Cfg :=
  if g then wordEnd .bden base false s [] else signedEnd .bnum base s []
def fieldStore (base : K → Bits) (f : FeeField) (s w : Bits) : K → Bits :=
  Function.update (Function.update base src s) (.inr (.result f)) w

theorem scalar_start (base : K → Bits) (l : L) (hr : base (.inr .rev)=[]) :
    streamCfg l base (base src) [] (none,true)=plainCfg l base := by
  simp only [streamCfg,plainCfg]
  congr 1
  funext k
  by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
    simp_all [streamStore,Function.update_apply,src]

theorem scalar_flush_input (base : K → Bits) (f : FeeField) (w t : Bits)
    (hf : base (.inr (.result f))=[]) :
    flushCfg f (Function.update base src t) (.flush f) w.reverse [] (some false,true)=
      streamCfg (.flush f) base t (w.reverse++[]) (some false,true) := by
  simp only [flushCfg,TreeBudgetFrameRoutineTM2.cfg,streamCfg]
  congr 1
  funext k
  by_cases hs : k=src <;> by_cases hr : k=Sum.inr Aux.rev <;>
    by_cases ho : k=Sum.inr (Aux.result f) <;> by_cases ht : k=Sum.inr Aux.tmp <;>
    simp_all [tapes,flushPorts,streamStore,Function.update_apply,src]

theorem scalar_flush_output (base : K → Bits) (f : FeeField) (w t : Bits)
    (hr : base (.inr .rev)=[]) :
    flushCfg f (Function.update base src t) (nextGroup f) [] w (none,true)=
      plainCfg (nextGroup f) (fieldStore base f t w) := by
  simp only [flushCfg,TreeBudgetFrameRoutineTM2.cfg,plainCfg]
  congr 1
  funext k
  by_cases hs : k=src <;> by_cases ha : k=Sum.inr Aux.rev <;>
    by_cases ho : k=Sum.inr (Aux.result f) <;> by_cases ht : k=Sum.inr Aux.tmp <;>
    simp_all [tapes,flushPorts,fieldStore,Function.update_apply,src]

theorem scalar_checked_run (base : K → Bits) (g : Bool) (S : ℕ)
    (hr : base (.inr .rev)=[]) (hf : base (.inr (.result (scalarField g)))=[])
    (bs : (base src).length ≤ S) :
    ∃ out, Nonempty (Run (plainCfg (scalarEntry g) base) out (4*(S+1))) ∧
      (match groupRead g (base src) with
      | none => out.l=some .bad
      | some (w,t) => out=plainCfg (nextGroup (scalarField g)) (fieldStore base (scalarField g) t w)) ∧
      (∀ k, k≠src → k≠.inr .rev → k≠.inr (.result (scalarField g)) → out.stk k=base k) := by
  have run : Run (plainCfg (scalarEntry g) base) (scalarEnd g base (base src)) ((base src).length+2) := by
    cases g
    · simpa only [scalarEntry,Bool.false_eq_true,ite_false,scalarEnd,scalar_start base _ hr] using
        signed_run .bnum base (base src) [] (none,true)
    · simpa only [scalarEntry,ite_true,scalarEnd,scalar_start base _ hr] using
        weaken (word_run .bden base false (base src) [] (none,true)) (by omega : (base src).length+1 ≤ (base src).length+2)
  have contract : match groupRead g (base src) with
      | none => (scalarEnd g base (base src)).l=some .bad
      | some (w,t) => scalarEnd g base (base src)=
          streamCfg (.flush (scalarField g)) base t (w.reverse++[]) (some false,true) := by
    cases g
    · exact signedEnd_read .bnum base (base src) []
    · exact wordEnd_read .bden base (base src) [] false
  have kept : ∀ k, k≠src → k≠.inr .rev → (scalarEnd g base (base src)).stk k=base k := by
    intro k hs ha
    cases g
    · exact signedEnd_kept .bnum base (base src) [] k hs ha
    · exact wordEnd_kept .bden base (base src) [] false k hs ha
  cases hp : groupRead g (base src) with
  | none =>
    exact ⟨_,⟨weaken run (by omega)⟩,by simpa only [hp] using contract,
      fun k hs ha _ => kept k hs ha⟩
  | some pair =>
    obtain ⟨w,t⟩ := pair
    simp only [hp] at contract
    rw [contract] at run
    have fl := flush_run (scalarField g) (Function.update base src t) w.reverse [] (some false,true)
    simp only [List.reverse_reverse,List.append_nil] at fl
    rw [scalar_flush_input base (scalarField g) w t hf,
      scalar_flush_output base (scalarField g) w t hr] at fl
    have consumed := group_consumed g (base src) w t hp
    have bw : w.length ≤ S := by rw [consumed,List.length_append] at bs; omega
    refine ⟨_,⟨weaken (seq run fl) ?_⟩,by simp [hp],?_⟩
    · simp only [List.length_reverse]; omega
    · intro k hs ha hf
      simp [plainCfg,fieldStore,hs,hf]

def halted (base : K → Bits) (ok : Bool) : Cfg := ⟨none,(none,ok),base⟩

def bad_run (c : Cfg) (h : c.l=some .bad) : Run c (halted c.stk false) 1 := by
  apply once
  cases c
  simp_all [halted,machine,FinTM2.step,TM2.step,program,TM2.stepAux]
  rfl

def eof_run (base : K → Bits) : Run (plainCfg .eof base) (halted base (base src).isEmpty) 1 := by
  apply once
  cases hs : base src <;> simp [plainCfg,halted,machine,FinTM2.step,TM2.step,program,TM2.stepAux,hs] <;> rfl

def budgetParse (s : Bits) : Option (Bits × Bits) := do
  let (b,t) ← readSigned s
  let (q,u) ← readWord false t
  if u=[] then some (b,q) else none

def budgetStore (base : K → Bits) (b q : Bits) : K → Bits :=
  fieldStore (fieldStore base .bnum [] b) .bden [] q

def budgetKept (base : K → Bits) (out : Cfg) : Prop := ∀ k,
  k≠src → k≠.inr .rev → k≠.inr (.result .bnum) → k≠.inr (.result .bden) → out.stk k=base k

theorem budget_run (base : K → Bits) (S : ℕ)
    (hr : base (.inr .rev)=[]) (hb : base (.inr (.result .bnum))=[])
    (hq : base (.inr (.result .bden))=[]) (bs : (base src).length ≤ S) :
    ∃ out, Nonempty (Run (plainCfg (.sign .bnum) base) out (16*(S+1))) ∧
      out.l=none ∧ out.var.2=(budgetParse (base src)).isSome ∧ budgetKept base out ∧
      (∀ b q, budgetParse (base src)=some (b,q) → out=halted (budgetStore base b q) true) := by
  obtain ⟨a,⟨ha⟩,ca,ka⟩ := scalar_checked_run base false S hr hb bs
  change Run (plainCfg (.sign .bnum) base) a (4*(S+1)) at ha
  change (match readSigned (base src) with
    | none => a.l=some .bad
    | some (w,t) => a=plainCfg (.marker .bden false) (fieldStore base .bnum t w)) at ca
  cases hp : readSigned (base src) with
  | none =>
    simp only [hp] at ca
    refine ⟨_,⟨weaken (seq ha (bad_run a ca)) (by omega)⟩,rfl,?_,?_,?_⟩
    · simp [halted,budgetParse,hp]
    · intro k hs hv hb hq; exact ka k hs hv hb
    · intro b q h; simp [budgetParse,hp] at h
  | some pair =>
    obtain ⟨b,t⟩ := pair
    simp only [hp] at ca
    subst a
    let mid := fieldStore base .bnum t b
    have mr : mid (.inr .rev)=[] := by simp [mid,fieldStore,hr,src]
    have mq : mid (.inr (.result .bden))=[] := by simp [mid,fieldStore,hq,src]
    have mt : mid src=t := by simp [mid,fieldStore,src]
    have small : t.length ≤ S := by
      have hc := readSigned_consumed (base src) b t hp
      rw [hc,List.length_append] at bs; omega
    obtain ⟨a,⟨ha₂⟩,ca₂,ka₂⟩ := scalar_checked_run mid true S mr mq (by simpa [mt] using small)
    change Run (plainCfg (.marker .bden false) mid) a (4*(S+1)) at ha₂
    change (match readWord false (mid src) with
      | none => a.l=some .bad
      | some (w,u) => a=plainCfg .eof (fieldStore mid .bden u w)) at ca₂
    rw [mt] at ca₂
    have pre := seq ha ha₂
    cases hq₁ : readWord false t with
    | none =>
      simp only [hq₁] at ca₂
      refine ⟨_,⟨weaken (seq pre (bad_run a ca₂)) (by omega)⟩,rfl,?_,?_,?_⟩
      · simp [halted,budgetParse,hp,hq₁]
      · intro k hs hv hb hq
        change a.stk k=base k
        rw [ka₂ k hs hv hq]
        simp [mid,fieldStore,hs,hb]
      · intro bb qq h; simp [budgetParse,hp,hq₁] at h
    | some pair =>
      obtain ⟨q,u⟩ := pair
      simp only [hq₁] at ca₂
      subst a
      have run := seq pre (eof_run (fieldStore mid .bden u q))
      have hu : fieldStore mid .bden u q src=u := by simp [fieldStore,src]
      refine ⟨_,⟨weaken run (by omega)⟩,rfl,?_,?_,?_⟩
      · simp only [halted,hu,budgetParse,bind,hp,hq₁,Option.bind_some]
        cases u <;> simp
      · intro k hs hv hb hq
        simp [halted,fieldStore,mid,hs,hb,hq]
      · intro bb qq h
        simp only [budgetParse,bind,hp,hq₁,Option.bind_some] at h
        split_ifs at h with he
        cases he
        cases h
        congr 1
        funext k
        by_cases hs : k=src <;> by_cases hb : k=Sum.inr (Aux.result FeeField.bnum) <;>
          by_cases hq : k=Sum.inr (Aux.result FeeField.bden) <;>
          simp_all [budgetStore,fieldStore,mid,Function.update_apply,src]

end UAVProof.A4FeeTailMachine
