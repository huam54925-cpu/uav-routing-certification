import LeanCompletion.UAV.TreeBudgetFeeTailSetup
import LeanCompletion.UAV.TreeBudgetFeeTailLoops
import LeanCompletion.UAV.TreeBudgetFeeTailFlush

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
set_option synthInstance.maxSize 2048
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def groupParse (g : Bool) (n : ℕ) (s : Bits) : Option (Bits × Bits) := do
  let t ← stripHeader (encodeNat n) s
  let (ws,u) ← parseMany (groupRead g) n t
  pure (ws.flatten,u)

def groupStore (base : K → Bits) (g : Bool) (s w : Bits) : K → Bits :=
  Function.update (Function.update base src s) (.inr (.result (groupField g))) w

def groupClean (base : K → Bits) (g : Bool) : Prop :=
  base (.inr .tmp)=[] ∧ base (.inr .expected)=[] ∧ base (.inr .ticks)=[] ∧
  base (.inr .rev)=[] ∧ base (.inr (.result (groupField g)))=[]

def plainCfg (l : L) (base : K → Bits) : Cfg := ⟨some l,(none,true),base⟩

def groupKept (g : Bool) (base : K → Bits) (out : Cfg) : Prop := ∀ k,
  k≠src → k≠.inr .tmp → k≠.inr .expected → k≠.inr .ticks →
  k≠.inr .rev → k≠.inr (.result (groupField g)) → out.stk k=base k

theorem group_store_kept (base : K → Bits) (g : Bool) (s w : Bits) (l : L) :
    groupKept g base (plainCfg l (groupStore base g s w)) := by
  intro k hs ht he hk hr hf
  simp [plainCfg,groupStore,hs,hf]

theorem dimension_input (base : K → Bits) (g : Bool) (n : ℕ)
    (hd : base dimension=n.bits) (hc : groupClean base g) :
    TreeBudgetStackRoutine.conf dimPorts base (.dimension g .reverse) n.bits [] []=
      plainCfg (.dimension g .reverse) base := by
  simp only [TreeBudgetStackRoutine.conf,plainCfg]
  congr 1
  funext k
  by_cases h₁ : k=dimension <;> by_cases h₂ : k=Sum.inr Aux.tmp <;>
    by_cases h₃ : k=Sum.inr Aux.expected <;>
    simp_all [tapes,dimPorts,groupClean]

theorem dimension_output (base : K → Bits) (g : Bool) (n : ℕ)
    (hd : base dimension=n.bits) (hc : groupClean base g) :
    TreeBudgetStackRoutine.conf dimPorts base (.header g) n.bits [] (encodeNat n)=
      headerCfg base (.header g) (base src) (encodeNat n) := by
  simp only [TreeBudgetStackRoutine.conf,headerCfg]
  congr 1
  funext k
  by_cases h₁ : k=dimension <;> by_cases h₂ : k=Sum.inr Aux.tmp <;>
    by_cases h₃ : k=Sum.inr Aux.expected <;> by_cases h₄ : k=src <;>
    simp_all [tapes,dimPorts,headerPorts,groupClean,src,dimension]

theorem count_input (base : K → Bits) (g : Bool) (ps : List ℕ) (t : Bits)
    (hp : base parents=ps.flatMap encodeNat) (hc : groupClean base g) :
    TreeBudgetStackRoutine.conf countPorts (Function.update base src t) (.count g .count)
      (ps.flatMap encodeNat) [] [] = headerCfg base (.count g .count) t [] := by
  simp only [TreeBudgetStackRoutine.conf,headerCfg]
  congr 1
  funext k
  by_cases h₁ : k=parents <;> by_cases h₂ : k=Sum.inr Aux.tmp <;>
    by_cases h₃ : k=Sum.inr Aux.expected <;> by_cases h₄ : k=src <;>
    by_cases h₅ : k=Sum.inr Aux.ticks <;>
    simp_all [tapes,countPorts,headerPorts,Function.update_apply,groupClean,parents,src]

theorem count_output (base : K → Bits) (g : Bool) (ps : List ℕ) (t : Bits)
    (hp : base parents=ps.flatMap encodeNat) (hc : groupClean base g) :
    TreeBudgetStackRoutine.conf countPorts (Function.update base src t) (.more g)
      (ps.flatMap encodeNat) [] (List.replicate ps.length true)=loopCfg g base ps.length t [] (none,true) := by
  simp only [TreeBudgetStackRoutine.conf,loopCfg,streamCfg]
  congr 1
  funext k
  by_cases h₁ : k=parents <;> by_cases h₂ : k=Sum.inr Aux.tmp <;>
    by_cases h₃ : k=Sum.inr Aux.ticks <;> by_cases h₄ : k=src <;>
    by_cases h₅ : k=Sum.inr Aux.rev <;>
    simp_all [tapes,countPorts,streamStore,tickBase,Function.update_apply,groupClean,parents,src]

theorem flush_input (base : K → Bits) (g : Bool) (w t : Bits) (hc : groupClean base g) :
    flushCfg (groupField g) (Function.update base src t) (.flush (groupField g)) w.reverse [] (none,true)=
      streamCfg (.flush (groupField g)) (tickBase base 0) t (w.reverse++[]) (none,true) := by
  simp only [flushCfg,TreeBudgetFrameRoutineTM2.cfg,streamCfg]
  congr 1
  funext k
  by_cases h₁ : k=src <;> by_cases h₂ : k=Sum.inr Aux.tmp <;>
    by_cases h₃ : k=Sum.inr Aux.ticks <;> by_cases h₄ : k=Sum.inr Aux.rev <;>
    by_cases h₅ : k=Sum.inr (Aux.result (groupField g)) <;>
    simp_all [tapes,flushPorts,streamStore,tickBase,Function.update_apply,groupClean,src]

theorem flush_output_layout (base : K → Bits) (g : Bool) (w t : Bits) (hc : groupClean base g) :
    flushCfg (groupField g) (Function.update base src t) (nextGroup (groupField g)) [] w (none,true)=
      plainCfg (nextGroup (groupField g)) (groupStore base g t w) := by
  simp only [flushCfg,TreeBudgetFrameRoutineTM2.cfg,plainCfg]
  congr 1
  funext k
  by_cases h₁ : k=src <;> by_cases h₂ : k=Sum.inr Aux.tmp <;>
    by_cases h₃ : k=Sum.inr Aux.rev <;> by_cases h₄ : k=Sum.inr (Aux.result (groupField g)) <;>
    simp_all [tapes,flushPorts,groupStore,Function.update_apply,groupClean,src]

theorem group_checked_run (base : K → Bits) (g : Bool) (n : ℕ) (ps : List ℕ) (S : ℕ)
    (hd : base dimension=n.bits) (hp : base parents=ps.flatMap encodeNat) (hn : ps.length=n)
    (hc : groupClean base g) (bP : (ps.flatMap encodeNat).length≤S) (bD : n.bits.length≤S)
    (bn : n≤S) (bt : (base src).length≤S) :
    ∃ out, Nonempty (Run (plainCfg (.dimension g .reverse) base) out (64*(S+1)^2)) ∧
      (match groupParse g n (base src) with
      | none => out.l=some .bad
      | some (w,t) => out=plainCfg (nextGroup (groupField g)) (groupStore base g t w)) ∧
      groupKept g base out := by
  have dim := dimension_run base g n
  erw [dimension_input base g n hd hc,dimension_output base g n hd hc] at dim
  have head := header_run base g (encodeNat n) (base src) (none,true)
  have pre := seq dim head
  cases hh : stripHeader (encodeNat n) (base src) with
  | none =>
    refine ⟨_,⟨weaken pre ?_⟩,?_,?_⟩
    · simp only [encodeNat_length,← Nat.size_eq_bits_len]; nlinarith
    · simpa [groupParse,hh] using (header_failure base g _ _ hh).1
    · intro k hs ht he hk hr hf; exact header_preserved base g _ _ k hs he
  | some t =>
    rw [header_success base g _ _ _ hh] at pre
    have small : t.length≤S := by
      have eq := (stripHeader_iff _ _ _).mp hh
      rw [eq,List.length_append] at bt; omega
    have cnt := parent_count_run (Function.update base src t) g ps
    erw [count_input base g ps t hp hc,count_output base g ps t hp hc,hn] at cnt
    have loop := loop_run g base n t [] (none,true)
    have steps := seq (seq pre cnt) loop
    have contract := loop_read g base n t []
    cases hm : parseMany (groupRead g) n t with
    | none =>
      simp only [hm] at contract
      refine ⟨_,⟨weaken steps ?_⟩,?_,?_⟩
      · simp only [encodeNat_length,← Nat.size_eq_bits_len]; nlinarith
      · simpa [groupParse,hh,hm] using contract
      · intro k hs ht he hk hr hf; exact loop_kept g base n t [] k hs hr hk
    | some pair =>
      obtain ⟨ws,u⟩ := pair
      simp only [hm] at contract
      rw [contract] at steps
      have fl := flush_run (groupField g) (Function.update base src u) ws.flatten.reverse [] (none,true)
      simp only [List.reverse_reverse,List.append_nil] at fl
      erw [flush_input base g ws.flatten u hc,flush_output_layout base g ws.flatten u hc] at fl
      have consumed := groupMany_consumed g n t ws u hm
      have bw : ws.flatten.length≤S := by rw [consumed,List.length_append] at small; omega
      refine ⟨_,⟨weaken (seq steps fl) ?_⟩,?_,group_store_kept base g u ws.flatten _⟩
      · simp only [encodeNat_length,← Nat.size_eq_bits_len,List.length_reverse]; nlinarith
      · simp [groupParse,hh,hm]

end UAVProof.A4FeeTailMachine
