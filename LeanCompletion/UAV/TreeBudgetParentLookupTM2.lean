import LeanCompletion.UAV.TreeBudgetIndexedZeroTM2
import LeanCompletion.UAV.TreeBudgetCanonicalDigits
import LeanCompletion.UAV.TreeBudgetParentArray

/-! Physical indexed lookup in the materialized parent table. Stack 0 starts
with an encoded index and the canonical table body. The index selects a prefix
length; its one-past-end case fails in the target parser. -/
namespace UAVProof.TreeBudgetParentLookupTM2
open TreeBudgetBinaryCodec TreeBudgetCanonicalDigits TreeBudgetFrameRoutineTM2
open TreeBudgetTM2Call Turing StateTransition
abbrev K := Fin 7 ⊕ Bool
abbrev L := Fin 18 ⊕ Fin 7
abbrev Cfg := Configuration K L
def ports : Ports K := ⟨.inl 0,.inr false,.inr true,by decide,by decide,by decide⟩
def labels : Phase → L
  | .marker => .inr 1 | .payload => .inr 2 | .reverse => .inr 3 | .clear => .inr 4

def program : L → Statement K L
  | .inl l => compile Sum.inl (.inr 0) (TreeBudgetListGuardTM2.program l)
  | .inr l => match l.val with
    | 0 => .branch Prod.snd (.load (fun _ => (none,true)) (.goto (fun _ => labels .marker))) .halt
    | 1 => code ports labels (.inr 5) (.inr 6) true .marker
    | 2 => code ports labels (.inr 5) (.inr 6) true .payload
    | 3 => code ports labels (.inr 5) (.inr 6) true .reverse
    | 4 => code ports labels (.inr 5) (.inr 6) true .clear
    | 5 => .halt
    | _ => .load (fun _ => (none,false)) .halt

def machine : FinTM2 where
  K := K
  k₀ := .inl 0
  k₁ := .inr true
  Γ _ := Bool
  Λ := L
  main := .inl 0
  σ := State
  initialState := (none,true)
  m := program

def liftCfg := embed (R := Bool) (Λ := Fin 18) (K := Fin 7) Sum.inl (Sum.inr (0 : Fin 7)) (fun _ => [])
def start (s ctx : Bits) : Cfg := liftCfg (TreeBudgetListGuardTM2.atLabel 0 s [] [] [] [] ctx)

theorem routine_eq (p : Phase) : program (labels p) = code ports labels (.inr 5) (.inr 6) true p := by
  cases p <;> rfl

def field (base : K → Bits) (r : Bits) : Cfg :=
  match parseNat r with
  | none => cfg ports base (.inr 6) none true (TreeBudgetNatListLoop.suffix r) [] []
  | some (v,t) => cfg ports base (.inr 5) none true t [] v.bits

def field_run (base : K → Bits) (r : Bits) : EvalsToInTime machine.step
    (cfg ports base (labels .marker) none true r [] []) (some (field base r)) (2*r.length+2) := by
  cases hw : parseWord r with
  | none =>
    have run := truncated_run ports base labels (.inr 5) (.inr 6) true program routine_eq r hw none true [] []
    simpa [field,parseNat_truncated r hw,TreeBudgetNatListLoop.suffix,hw,machine,FinTM2.step] using run
  | some pair =>
    obtain ⟨bs,t⟩ := pair
    obtain rfl := parseWord_consumed r bs t hw
    have run := framed_run ports base labels (.inr 5) (.inr 6) true program routine_eq bs t none true [] []
    have hb : 3*bs.length+2 ≤ 2*(word bs ++ t).length+2 := by simp [word_length]; omega
    cases hc : lastDigit bs true with
    | false => simpa [field,parseNat_framed,hc,TreeBudgetNatListLoop.suffix,parseWord_append,machine,FinTM2.step] using weaken run hb
    | true => simpa [field,parseNat_framed,hc,canonical_of_last bs hc,machine,FinTM2.step] using weaken run hb

def terminalField (base : K → Bits) (r : Bits) : Cfg :=
  {field base r with l := none, var := (none,(parseNat r).isSome)}

def finish (s ctx : Bits) : Cfg :=
  let c := TreeBudgetCountedNatsTM2.stopped s ctx
  if c.var.2 then terminalField (liftCfg c).stk (c.stk 0)
  else {liftCfg c with l := none}

theorem setup (c : TreeBudgetListGuardTM2.Cfg) (hl : c.l = none) (hf : c.var.2 = true) :
    machine.step (liftCfg c) = some (cfg ports (liftCfg c).stk (labels .marker) none true (c.stk 0) [] []) := by
  simp [machine,FinTM2.step,TM2.step,liftCfg,embed,hl,program,TM2.stepAux,hf,cfg]
  congr 1
  congr 1
  funext k
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr b => cases b <;> rfl

def lookup_run (s ctx : Bits) : EvalsToInTime machine.step (start s ctx) (some (finish s ctx))
    (24*(s.length+1)^2) := by
  let c := TreeBudgetCountedNatsTM2.stopped s ctx
  have run := call_run (R := Bool) Sum.inl (Sum.inr (0 : Fin 7)) (fun _ => [])
    TreeBudgetListGuardTM2.program program (fun _ => rfl) (TreeBudgetCountedNatsTM2.list_halts s ctx)
  have hl : c.l = none := by unfold c TreeBudgetCountedNatsTM2.stopped; dsimp only; split <;> rfl
  have layout := TreeBudgetIndexedZeroTM2.layout s ctx
  cases hp : parseNats s with
  | none =>
    simp only [hp] at layout
    have hflag : c.var.2 = false := layout
    have step : machine.step (liftCfg c) = some (finish s ctx) := by
      change _ = some (if c.var.2 then _ else _)
      simp [machine,FinTM2.step,TM2.step,liftCfg,embed,program,TM2.stepAux,hl,hflag]
      rfl
    have hpos : 0 < (s.length+1)^2 := Nat.pow_pos (by omega)
    exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _ run (once step)) (by omega)
  | some pair =>
    obtain ⟨xs,t⟩ := pair
    simp only [hp] at layout
    have hf : c.var.2 = true := layout.1
    have ht : c.stk 0 = t := layout.2.1
    let bk := (liftCfg c).stk
    have middle := field_run bk (c.stk 0)
    have last : machine.step (field bk (c.stk 0)) = some (finish s ctx) := by
      change _ = some (if c.var.2 then _ else _)
      rw [if_pos hf]
      change machine.step (field bk (c.stk 0)) = some (terminalField bk (c.stk 0))
      cases hn : parseNat (c.stk 0) with
      | none => simp only [terminalField,field,hn]; rfl
      | some p => obtain ⟨v,u⟩ := p; simp only [terminalField,field,hn]; rfl
    have seq := EvalsToInTime.trans machine.step _ _ _ _ _ run (once (setup c hl hf))
    have combined :=  EvalsToInTime.trans machine.step _ _ _ _ _ (EvalsToInTime.trans machine.step _ _ _ _ _ seq middle) (once last)
    have hs := congrArg List.length (parseList_canonical encodeNat parseNat parseNat_canonical s t xs hp)
    simp only [List.length_append] at hs
    apply weaken combined
    rw [ht]
    nlinarith

def read (c : Cfg) : Option (ℕ × Bits) :=
  if c.var.2 then some (value (c.stk (.inr true)), c.stk (.inl 0)) else none

theorem refines (s ctx : Bits) : read (finish s ctx) =
    (parseNats s).bind (fun p => parseNat p.2) ∧ (finish s ctx).stk (.inl 5) = ctx := by
  have hs := TreeBudgetIndexedZeroTM2.layout s ctx
  have hc := (TreeBudgetCountedNatsTM2.halted_refines s ctx).2
  cases hp : parseNats s with
  | none => simp [hp] at hs; simp [finish,hs,read,liftCfg,embed,banks,hc]
  | some pair =>
    obtain ⟨xs,t⟩ := pair
    simp only [hp] at hs
    cases hn : parseNat t with
    | none => simp [finish,hs,read,terminalField,field,hn,cfg,tapes,ports,liftCfg,embed,banks,hc]
    | some pair =>
      obtain ⟨a,u⟩ := pair
      simp [finish,hs,read,terminalField,field,hn,cfg,tapes,ports,liftCfg,embed,banks,hc]

theorem indexed_field (before after : List ℕ) (a : ℕ) (ctx : Bits) :
    read (finish (encodeNat before.length ++ (before ++ a :: after).flatMap encodeNat) ctx) =
      some (a, after.flatMap encodeNat) := by
  let t := encodeNat a ++ after.flatMap encodeNat
  have he : encodeNat before.length ++ (before ++ a :: after).flatMap encodeNat = encodeNats before ++ t := by
    simp [encodeList,t,List.append_assoc]
  rw [he,(refines ..).1,parseNats_append]
  exact parseNat_append a _

theorem init_eq (s : Bits) : initList machine s = start s [] := by
  simp only [initList,machine,start,liftCfg,embed,TreeBudgetListGuardTM2.atLabel]
  congr 1
  funext k
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr b => cases b <;> rfl

def lookup_from_init (s : Bits) : EvalsToInTime machine.step (initList machine s)
    (some (finish s [])) (24*(s.length+1)^2) := by rw [init_eq]; exact lookup_run s []

theorem terminal (s ctx : Bits) : machine.step (finish s ctx) = none := by
  unfold finish
  dsimp only
  split <;> rfl

end UAVProof.TreeBudgetParentLookupTM2
