import LeanCompletion.UAV.TreeBudgetFeeTailTM2

namespace UAVProof.A4FeeTailMachine
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition
set_option synthInstance.maxSize 2048
set_option maxRecDepth 20000

def headerPorts : Ports K := ⟨src,.inr .expected,.inr .tmp,by decide,by decide,by decide⟩
def headerCfg (base : K → Bits) (l : L) (s e : Bits) (v : State := (none,true)) : Cfg :=
  ⟨some l,v,tapes headerPorts base s e (base (.inr .tmp))⟩

@[simp] theorem header_src (base : K → Bits) (s e z : Bits) :
    tapes headerPorts base s e z src=s := tapes_src headerPorts base s e z
@[simp] theorem header_expected (base : K → Bits) (s e z : Bits) :
    tapes headerPorts base s e z (.inr .expected)=e := tapes_scratch headerPorts base s e z
@[simp] theorem header_update_src (base : K → Bits) (s e z t : Bits) :
    Function.update (tapes headerPorts base s e z) src t=tapes headerPorts base t e z :=
  update_src headerPorts base s t e z
@[simp] theorem header_update_expected (base : K → Bits) (s e z t : Bits) :
    Function.update (tapes headerPorts base s e z) (.inr .expected) t=tapes headerPorts base s t z :=
  update_scratch headerPorts base s e t z

def stripHeader : Bits → Bits → Option Bits
  | [],s => some s
  | _::_,[] => none
  | a::e,b::s => if a=b then stripHeader e s else none

theorem stripHeader_iff (e s t : Bits) : stripHeader e s=some t ↔ s=e++t := by
  induction e generalizing s with
  | nil => simp [stripHeader]
  | cons a e ih =>
    cases s with
    | nil => simp [stripHeader]
    | cons b s => by_cases h : a=b <;> simp [stripHeader,h,ih,eq_comm]

def headerEnd (base : K → Bits) (g : Bool) : Bits → Bits → Cfg
  | [],s => headerCfg base (.count g .count) s []
  | _::e,[] => headerCfg base .bad [] e (none,false)
  | a::e,b::s => if a=b then headerEnd base g e s else headerCfg base .bad s e (none,false)

def header_run (base : K → Bits) (g : Bool) (e s : Bits) (v : State) :
    EvalsToInTime machine.step (headerCfg base (.header g) s e v)
      (some (headerEnd base g e s)) (e.length+1) := by
  induction e generalizing s v with
  | nil =>
    apply once
    simp [machine,FinTM2.step,TM2.step,headerCfg,headerEnd,program,TM2.stepAux,go]
    congr 2
    funext k
    by_cases h₁ : k=src <;> by_cases h₂ : k=Sum.inr Aux.expected <;>
      simp_all [tapes,headerPorts,Function.update_apply]
  | cons a e ih =>
    cases s with
    | nil =>
      apply weaken (once (b:=headerEnd base g (a::e) []) ?_) (by simp)
      simp [machine,FinTM2.step,TM2.step,headerCfg,headerEnd,program,TM2.stepAux,go]
      funext k
      by_cases h₁ : k=src <;> by_cases h₂ : k=Sum.inr Aux.expected <;>
        simp_all [tapes,headerPorts,Function.update_apply]
    | cons b s =>
      by_cases h : a=b
      · subst b
        have step : machine.step (headerCfg base (.header g) (a::s) (a::e) v)=
            some (headerCfg base (.header g) s e) := by
          simp [machine,FinTM2.step,TM2.step,headerCfg,program,TM2.stepAux,go]
          congr 2
          funext k
          by_cases h₁ : k=src <;> by_cases h₂ : k=Sum.inr Aux.expected <;>
            simp_all [tapes,headerPorts,Function.update_apply]
        simpa [headerEnd] using prepend step (ih s (none,true))
      · apply weaken (once (b:=headerEnd base g (a::e) (b::s)) ?_) (by simp)
        have he : (a==b)=false := by cases a <;> cases b <;> simp_all
        simp [machine,FinTM2.step,TM2.step,headerCfg,headerEnd,program,TM2.stepAux,go,h,he]
        funext k
        by_cases h₁ : k=src <;> by_cases h₂ : k=Sum.inr Aux.expected <;>
          simp_all [tapes,headerPorts,Function.update_apply]

theorem header_success (base : K → Bits) (g : Bool) (e s t : Bits) (h : stripHeader e s=some t) :
    headerEnd base g e s=headerCfg base (.count g .count) t [] := by
  rw [(stripHeader_iff _ _ _).mp h]
  clear h
  induction e with
  | nil => rfl
  | cons a e ih => simpa [headerEnd] using ih

theorem header_failure (base : K → Bits) (g : Bool) (e s : Bits) (h : stripHeader e s=none) :
    (headerEnd base g e s).l=some .bad ∧ (headerEnd base g e s).var=(none,false) := by
  induction e generalizing s with
  | nil => simp [stripHeader] at h
  | cons a e ih =>
    cases s with
    | nil => exact ⟨rfl,rfl⟩
    | cons b s =>
      by_cases he : a=b
      · simp only [stripHeader,if_pos he] at h
        simpa only [headerEnd,if_pos he] using ih s h
      · simp [headerEnd,he,headerCfg]

theorem header_preserved (base : K → Bits) (g : Bool) (e s : Bits) (k : K)
    (hs : k≠src) (he : k≠.inr .expected) : (headerEnd base g e s).stk k=base k := by
  induction e generalizing s with
  | nil => simp [headerEnd,headerCfg,tapes,headerPorts,hs,he]; intro hk; subst k; rfl
  | cons a e ih =>
    cases s with
    | nil => simp [headerEnd,headerCfg,tapes,headerPorts,hs,he]; intro hk; subst k; rfl
    | cons b s =>
      by_cases h : a=b
      · simpa [headerEnd,h] using ih s
      · simp [headerEnd,h,headerCfg,tapes,headerPorts,hs,he]; intro hk; subst k; rfl

/-- Copy a canonical dimension into a framed expected header; source is restored. -/
def dimension_run (base : K → Bits) (g : Bool) (n : ℕ) :
    EvalsToInTime machine.step
      (TreeBudgetStackRoutine.conf dimPorts base (.dimension g .reverse) n.bits [] [])
      (some (TreeBudgetStackRoutine.conf dimPorts base (.header g) n.bits [] (encodeNat n)))
      (2*n.bits.length+2) := by
  simpa only [List.append_nil,encodeNat] using
    TreeBudgetStackRoutine.copy_run dimPorts base (L.dimension g) (.header g) true program (fun _ => rfl) n.bits []

/-- Derive one token per actual parent field and restore its entire body. -/
def parent_count_run (base : K → Bits) (g : Bool) (ps : List ℕ) :
    EvalsToInTime machine.step
      (TreeBudgetStackRoutine.conf countPorts base (.count g .count) (ps.flatMap encodeNat) [] [])
      (some (TreeBudgetStackRoutine.conf countPorts base (.more g)
        (ps.flatMap encodeNat) [] (List.replicate ps.length true)))
      (2*(ps.flatMap encodeNat).length+2) := by
  simpa only [List.append_nil] using
    TreeBudgetStackRoutine.count_run countPorts base (L.count g) (.more g) false program (fun _ => rfl) ps []

end UAVProof.A4FeeTailMachine
