import LeanCompletion.UAV.TreeBudgetFeeTailSemantics

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
set_option synthInstance.maxSize 2048
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def feeStore (base : K → Bits) (w : FeeWords) : K → Bits :=
  budgetStore (groupStore (groupStore base false [] w.nums) true [] w.dens)
    w.budgetNum w.budgetDen

def feeKept (base : K → Bits) (out : Cfg) : Prop := ∀ k,
  k≠TreeBudgetRootFlowTM2.suffix → out.stk (.inl k)=base (.inl k)

theorem groupParse_consumed (g : Bool) (n : ℕ) (s w t : Bits)
    (h : groupParse g n s=some (w,t)) :
    s=encodeNat n++w++t := by
  simp only [groupParse,bind,Option.bind_eq_some_iff] at h
  obtain ⟨u,hu,⟨⟨ws,v⟩,hw,he⟩⟩ := h
  cases he
  rw [(stripHeader_iff _ _ _).mp hu,groupMany_consumed g n u ws v hw]
  simp [List.append_assoc]

theorem groupKept_prefix (g : Bool) (base : K → Bits) (out : Cfg)
    (h : groupKept g base out) : feeKept base out := by
  intro k hk
  exact h (.inl k) (by simpa [src] using hk) (by simp) (by simp) (by simp) (by simp) (by simp)

theorem budgetKept_prefix (base : K → Bits) (out : Cfg)
    (h : budgetKept base out) : feeKept base out := by
  intro k hk
  exact h (.inl k) (by simpa [src] using hk) (by simp) (by simp) (by simp)

theorem groupStore_prefix (base : K → Bits) (g : Bool) (s w : Bits)
    (k : TreeBudgetRootFlowTM2.K) (hk : k≠TreeBudgetRootFlowTM2.suffix) :
    groupStore base g s w (.inl k)=base (.inl k) := by
  simp [groupStore,src,hk]

/-- The two list loops and the two budget fields terminate on every suffix.
The bound counts all copies, headers, markers, field reads, reversals and EOF. -/
theorem fee_words_run (base : K → Bits) (n : ℕ) (ps : List ℕ) (S : ℕ)
    (hd : base dimension=n.bits) (hp : base parents=ps.flatMap encodeNat) (hn : ps.length=n)
    (hc : ∀ a, base (.inr a)=[]) (bP : (ps.flatMap encodeNat).length ≤ S)
    (bD : n.bits.length ≤ S) (bn : n ≤ S) (bt : (base src).length ≤ S) :
    ∃ out, Nonempty (Run (plainCfg (.dimension false .reverse) base) out (256*(S+1)^2)) ∧
      out.l=none ∧ out.var.2=(readFeeWords n (base src)).isSome ∧ feeKept base out ∧
      (∀ w, readFeeWords n (base src)=some w → out=halted (feeStore base w) true) := by
  have clean : groupClean base false := ⟨hc _,hc _,hc _,hc _,hc _⟩
  obtain ⟨a,⟨ha⟩,ca,ka⟩ := group_checked_run base false n ps S hd hp hn clean bP bD bn bt
  cases h₁ : groupParse false n (base src) with
  | none =>
    simp only [h₁] at ca
    refine ⟨_,⟨weaken (seq ha (bad_run a ca)) ?_⟩,rfl,?_,?_,?_⟩
    · nlinarith [Nat.zero_le S]
    · simp [halted,readFeeWords,h₁]
    · exact groupKept_prefix false base a ka
    · intro w hw; simp [readFeeWords,h₁] at hw
  | some pair =>
    obtain ⟨aa,t⟩ := pair
    simp only [h₁] at ca
    subst a
    let mid := groupStore base false t aa
    have md : mid dimension=n.bits := by simpa [mid,groupStore,dimension,src,groupField] using hd
    have mp : mid parents=ps.flatMap encodeNat := by simpa [mid,groupStore,parents,src,groupField] using hp
    have mc : groupClean mid true := by
      simp [mid,groupClean,groupStore,groupField,src,hc]
    have mt : mid src=t := by simp [mid,groupStore,src]
    have small : t.length ≤ S := by
      have eq := groupParse_consumed false n (base src) aa t h₁
      rw [eq,List.length_append,List.length_append] at bt
      omega
    obtain ⟨a,⟨ha₂⟩,ca₂,ka₂⟩ := group_checked_run mid true n ps S md mp hn mc bP bD bn (by simpa [mt] using small)
    change Run (plainCfg (.dimension true .reverse) mid) a (64*(S+1)^2) at ha₂
    have pre := seq ha ha₂
    rw [mt] at ca₂
    cases h₂ : groupParse true n t with
    | none =>
      simp only [h₂] at ca₂
      refine ⟨_,⟨weaken (seq pre (bad_run a ca₂)) ?_⟩,rfl,?_,?_,?_⟩
      · nlinarith [Nat.zero_le S]
      · simp [halted,readFeeWords,h₁,h₂]
      · intro k hk
        change a.stk (.inl k)=base (.inl k)
        rw [groupKept_prefix true mid a ka₂ k hk]
        exact groupStore_prefix base false t aa k hk
      · intro w hw; simp [readFeeWords,h₁,h₂] at hw
    | some pair =>
      obtain ⟨dd,u⟩ := pair
      simp only [h₂] at ca₂
      subst a
      let last := groupStore mid true u dd
      have lr : last (.inr .rev)=[] := by simp [last,mid,groupStore,groupField,src,hc]
      have lb : last (.inr (.result .bnum))=[] := by simp [last,mid,groupStore,groupField,src,hc]
      have lq : last (.inr (.result .bden))=[] := by simp [last,mid,groupStore,groupField,src,hc]
      have lu : last src=u := by simp [last,groupStore,src]
      have smaller : u.length ≤ S := by
        have eq := groupParse_consumed true n t dd u h₂
        rw [eq,List.length_append,List.length_append] at small
        omega
      obtain ⟨out,⟨ho⟩,hl,hv,hk,hw⟩ := budget_run last S lr lb lq (by simpa [lu] using smaller)
      have run := seq pre ho
      refine ⟨out,⟨weaken run ?_⟩,hl,?_,?_,?_⟩
      · nlinarith [Nat.zero_le S]
      · cases hb : budgetParse u <;> simpa [readFeeWords,h₁,h₂,lu,hb] using hv
      · intro k hk'
        rw [budgetKept_prefix last out hk k hk']
        change groupStore mid true u dd (.inl k)=base (.inl k)
        rw [groupStore_prefix mid true u dd k hk']
        exact groupStore_prefix base false t aa k hk'
      · intro w he
        simp only [readFeeWords,bind,pure,h₁,h₂,Option.bind_some] at he
        cases hb : budgetParse u with
        | none => simp [hb] at he
        | some pair =>
          obtain ⟨b,q⟩ := pair
          simp only [hb,Option.bind_some,Option.some.injEq] at he
          cases he
          rw [hw b q (by simpa [lu] using hb)]
          congr 1
          funext k
          by_cases hs : k=src <;> by_cases ha : k=Sum.inr (Aux.result FeeField.nums) <;>
            by_cases hd' : k=Sum.inr (Aux.result FeeField.dens) <;>
            by_cases hb' : k=Sum.inr (Aux.result FeeField.bnum) <;>
            by_cases hq' : k=Sum.inr (Aux.result FeeField.bden) <;>
            simp_all [feeStore,budgetStore,fieldStore,groupStore,groupField,last,mid,Function.update_apply,src]

/-- Total concrete fee-tail execution, with the parser's exact acceptance bit,
all four output bodies in their original order, and the prefix/context retained. -/
theorem fee_tail_run (base : K → Bits) (n : ℕ) (ps : List ℕ) (S : ℕ)
    (hd : base dimension=n.bits) (hp : base parents=ps.flatMap encodeNat) (hn : ps.length=n)
    (hc : ∀ a, base (.inr a)=[]) (bP : (ps.flatMap encodeNat).length ≤ S)
    (bD : n.bits.length ≤ S) (bn : n ≤ S) (bt : (base src).length ≤ S) :
    ∃ out, Nonempty (Run (plainCfg (.dimension false .reverse) base) out (256*(S+1)^2)) ∧
      out.l=none ∧ out.var.2=(A4FeeTailSpec.read n (base src)).isSome ∧ feeKept base out ∧
      (∀ f, A4FeeTailSpec.read n (base src)=some f → out=halted (feeStore base (wireWords f)) true) := by
  obtain ⟨out,hr,hl,hv,hk,hw⟩ := fee_words_run base n ps S hd hp hn hc bP bD bn bt
  refine ⟨out,hr,hl,?_,hk,?_⟩
  · simpa [readFeeWords_eq] using hv
  · intro f hf
    exact hw (wireWords f) (by simp [readFeeWords_eq,hf])

end UAVProof.A4FeeTailMachine
