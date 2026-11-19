import LeanCompletion.UAV.TreeBudgetCountedNatsHalt
import LeanCompletion.UAV.TreeBudgetTM2Call
import LeanCompletion.UAV.TreeBudgetBitPrimitives

/-! Test the root-coordinate-zero condition on a row of canonical fields.
The input is the encoded index followed by the row body. The list subroutine
consumes exactly the preceding coordinates. A single peek tests the target,
leaving the prefix and the current suffix available to the caller. -/
namespace UAVProof.TreeBudgetIndexedZeroTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call Turing StateTransition
open TreeBudgetCountedNatsTM2 (result stopped)
open TreeBudgetListGuardTM2 (outcome)
open TreeBudgetNatListLoop (loopEnd loop_contract)

/-- Physical list-return layout used by callers that branch on the flag. -/
theorem layout (s ctx : Bits) :
    match parseNats s with
    | none => (stopped s ctx).var.2 = false
    | some (ns,t) => (stopped s ctx).var.2 = true ∧ (stopped s ctx).stk 0 = t ∧
        (stopped s ctx).stk 2 = ns.flatMap encodeNat := by
  cases hp : parseNat s with
  | none =>
    have hh := (TreeBudgetListGuardTM2.header_invalid s ctx hp).1
    simp [stopped,result,outcome,parseNats,parseList,hp,hh,TreeBudgetListCleanup.done]
  | some pair =>
    obtain ⟨k,r⟩ := pair
    by_cases h : k ≤ r.length
    · have ht := loop_contract k r [] ctx
      cases hm : parseMany parseNat k r with
      | none =>
        simp only [hm] at ht
        simp [stopped,result,parseNats,parseList,hp,h,hm,ht.1,TreeBudgetListCleanup.done]
      | some pair =>
        obtain ⟨ns,t⟩ := pair
        simp only [hm] at ht
        simp [stopped,result,parseNats,parseList,hp,h,hm,ht,TreeBudgetNatListLoop.conf,cfg,
          tapes,TreeBudgetNatListLoop.ports]
    · have ht := TreeBudgetListGuardTM2.guard_contract r k.bits [] ctx
      simp [h] at ht
      simp [stopped,result,outcome,parseNats,parseList,hp,h,ht.1,TreeBudgetListCleanup.done]

abbrev K := Fin 7 ⊕ Unit
abbrev L := Fin 18 ⊕ Unit
abbrev Cfg := Configuration K L
def program : L → Statement K L
  | .inl l => compile Sum.inl (.inr ()) (TreeBudgetListGuardTM2.program l)
  | .inr _ => .peek (.inl 0) (fun v b => (none,v.2 && (b == some false))) .halt

def machine : FinTM2 where
  K := K
  k₀ := .inl 0
  k₁ := .inr ()
  Γ _ := Bool
  Λ := L
  main := .inl 0
  σ := State
  initialState := (none,true)
  m := program

def liftCfg := embed (R := Unit) (Λ := Fin 18) (K := Fin 7) Sum.inl (Sum.inr ()) (fun _ => [])
def start (s ctx : Bits) : Cfg := liftCfg (TreeBudgetListGuardTM2.atLabel 0 s [] [] [] [] ctx)

def finish (s ctx : Bits) : Cfg :=
  let c := stopped s ctx
  ⟨none, (none,c.var.2 && ((c.stk 0).head? == some false)), (liftCfg c).stk⟩

def check_run (s ctx : Bits) : EvalsToInTime machine.step (start s ctx) (some (finish s ctx))
    (20*(s.length+1)^2+1) := by
  have parsed :=  call_run (R := Unit) Sum.inl (Sum.inr ()) (fun _ => [])
    TreeBudgetListGuardTM2.program program (fun _ => rfl) (TreeBudgetCountedNatsTM2.list_halts s ctx)
  have hl : (stopped s ctx).l = none := by unfold stopped; dsimp only; split <;> rfl
  have step : machine.step (liftCfg (stopped s ctx)) = some (finish s ctx) := by
    simp [machine,FinTM2.step,TM2.step,liftCfg,embed,program,TM2.stepAux,hl,finish,banks]
  exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _ parsed (once step)) (by omega)

/-- A malformed prefix, an absent target, or a target starting with a payload
marker fails. The one-bit zero field is the only successful target prefix. -/
theorem refines (s ctx : Bits) :
    (finish s ctx).var.2 = (parseNats s).any (fun p => p.2.head? == some false) ∧
    (finish s ctx).stk (.inl 5) = ctx := by
  have hl := layout s ctx
  have hc := (TreeBudgetCountedNatsTM2.halted_refines s ctx).2
  cases hp : parseNats s with
  | none => simp [hp] at hl; simp [finish,liftCfg,embed,banks,hl,hc]
  | some p =>
    obtain ⟨ns,t⟩ := p
    simp [hp] at hl
    simp [finish,liftCfg,embed,banks,hl,hc]

theorem zero_marker (a : ℕ) (tail : Bits) :
    ((encodeNat a ++ tail).head? == some false) = (TreeBudgetBitPrimitives.zeroNatD a).value := by
  rw [TreeBudgetBitPrimitives.zeroNatD_value]
  cases hb : a.bits with
  | nil =>
    have h := value_bits a
    rw [hb] at h
    change 0 = a at h
    subst a; rfl
  | cons b bs =>
    have ha : a ≠ 0 := by intro h; subst a; simp at hb
    simp [encodeNat,word,hb,ha]

theorem row_coordinate (before after : List ℕ) (a : ℕ) (ctx : Bits) :
    let wire := encodeNat before.length ++ (before ++ a :: after).flatMap encodeNat
    (finish wire ctx).var.2 = (TreeBudgetBitPrimitives.zeroNatD a).value ∧
    (finish wire ctx).stk (.inl 0) = encodeNat a ++ after.flatMap encodeNat ∧
    (finish wire ctx).stk (.inl 2) = before.flatMap encodeNat := by
  let r := encodeNat a ++ after.flatMap encodeNat
  have hp := parseNats_append before r
  have he : encodeNat before.length ++ (before ++ a :: after).flatMap encodeNat =
      encodeNats before ++ r := by simp [encodeList,r,List.append_assoc]
  dsimp only
  rw [he]
  have hl := layout (encodeNats before ++ r) ctx
  simp [hp] at hl
  refine ⟨?_, hl.2.1, hl.2.2⟩
  change (_ && _) = _
  rw [hl.1,hl.2.1,Bool.true_and]
  exact zero_marker a _

theorem init_eq (s : Bits) : initList machine s = start s [] := by
  simp only [initList,machine,start,liftCfg,embed,TreeBudgetListGuardTM2.atLabel]
  congr 1
  funext k
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr u => cases u; rfl

def check_from_init (s : Bits) : EvalsToInTime machine.step (initList machine s)
    (some (finish s [])) (20*(s.length+1)^2+1) := by rw [init_eq]; exact check_run s []

end UAVProof.TreeBudgetIndexedZeroTM2
