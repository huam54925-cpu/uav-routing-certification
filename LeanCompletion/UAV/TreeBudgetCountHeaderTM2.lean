import LeanCompletion.UAV.TreeBudgetListGuardRuns

namespace UAVProof.TreeBudgetListGuardTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetCanonicalDigits Turing StateTransition

def base (ctx : Bits) : Fin 7 → Bits := fun k => if k = 5 then ctx else []

theorem frame_layout (ctx r t d : Bits) (l : Label) :
    cfg ports (base ctx) l none true r t d = atLabel l r d t [] [] ctx := by
  unfold cfg atLabel
  congr 1
  funext k; fin_cases k <;> rfl

def headerEnd (s ctx : Bits) : Cfg :=
  match parseWord s with
  | none => atLabel 10 [] [] [] [] [] ctx
  | some (bs,r) => if lastDigit bs true then atLabel 4 r bs [] [] [] ctx
    else atLabel 10 r [] [] [] [] ctx

def header_run (s ctx : Bits) : Run (atLabel 0 s [] [] [] [] ctx) (headerEnd s ctx)
    (2*s.length+2) := by
  cases hw : parseWord s with
  | none =>
    have run := truncated_run ports (base ctx) lab 4 10 true program code_eq s hw none true [] []
    simpa [Run, machine, FinTM2.step, lab, headerEnd, hw, frame_layout] using run
  | some pair =>
    obtain ⟨bs,r⟩ := pair
    have he := parseWord_consumed s bs r hw
    subst s
    have run := framed_run ports (base ctx) lab 4 10 true program code_eq bs r none true [] []
    have hb : 3*bs.length+2 ≤ 2*(word bs ++ r).length+2 := by simp [word_length]; omega
    cases hl : lastDigit bs true <;>
      simpa [Run, machine, FinTM2.step, lab, headerEnd, parseWord_append, hl, frame_layout]
        using weaken run hb

def outcome (s ctx : Bits) : Cfg :=
  match parseNat s with
  | none => headerEnd s ctx
  | some (k,r) => guardEnd r k.bits [] ctx

theorem header_valid (s ctx r : Bits) (k : ℕ) (h : parseNat s = some (k,r)) :
    headerEnd s ctx = atLabel 4 r k.bits [] [] [] ctx := by
  rw [parseNat_canonical s r k h]
  simp [headerEnd, encodeNat, parseWord_append, lastDigit_bits]

theorem header_invalid (s ctx : Bits) (h : parseNat s = none) :
    (headerEnd s ctx).l = some 10 ∧ (headerEnd s ctx).stk 5 = ctx := by
  cases hw : parseWord s with
  | none => simp [headerEnd, hw, atLabel, layout]
  | some pair =>
    obtain ⟨bs,r⟩ := pair
    rw [parseWord_consumed s bs r hw, parseNat_framed] at h
    cases hl : lastDigit bs true <;> simp_all [headerEnd, atLabel, layout]

def precheck_run (s ctx : Bits) : Run (atLabel 0 s [] [] [] [] ctx) (outcome s ctx)
    (8*(s.length+1)^2) := by
  have head := header_run s ctx
  cases hp : parseNat s with
  | none =>
    simp [outcome, hp]
    exact weaken head (by nlinarith)
  | some pair =>
    obtain ⟨k,r⟩ := pair
    rw [header_valid s ctx r k hp] at head
    have hl := congrArg List.length (parseNat_canonical s r k hp)
    simp only [List.length_append, encodeNat_length] at hl
    simp only [outcome, hp]
    apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ head (guard_run r k.bits [] ctx))
    simp only [Nat.size_eq_bits_len, List.length_nil]
    have hm := Nat.mul_le_mul (show r.length+1 ≤ s.length+1 by omega)
      (show 2*k.size+4 ≤ 2*s.length+4 by omega)
    nlinarith

def readBack (c : Cfg) : Option (ℕ × Bits) :=
  if c.l = some 9 then some ((c.stk 4).length, c.stk 0) else none

def reference (s : Bits) : Option (ℕ × Bits) := do
  let (k,r) ← parseNat s
  if k ≤ r.length then some (k,r) else none

theorem precheck_refines (s ctx : Bits) :
    readBack (outcome s ctx) = reference s ∧ (outcome s ctx).stk 5 = ctx := by
  cases hp : parseNat s with
  | none =>
    obtain ⟨hl,hc⟩ := header_invalid s ctx hp
    simp [outcome, reference, hp, readBack, hl, hc]
  | some pair =>
    obtain ⟨k,r⟩ := pair
    have hg := guard_contract r k.bits [] ctx
    by_cases h : k ≤ r.length
    · simp [h] at hg
      simp [outcome, reference, hp, h, hg, readBack, atLabel, layout, marks]
    · simp [h] at hg
      simp [outcome, reference, hp, h, readBack, hg]

theorem precheck_parseNatsD (s ctx : Bits) :
    (readBack (outcome s ctx)).bind (fun p => parseMany parseNat p.1 p.2) =
      (TreeBudgetCostedParsing.parseNatsD s).value := by
  rw [(precheck_refines s ctx).1]
  simp only [TreeBudgetCostedParsing.parseNatsD, TreeBudgetCostedParsing.parseListD_value,
    TreeBudgetCostedCodec.parseNatD_value]
  cases hp : parseNat s with
  | none => simp [reference, parseList, hp]
  | some pair =>
    obtain ⟨k,r⟩ := pair
    by_cases h : k ≤ r.length <;> simp [reference, parseList, hp, h]

theorem too_large (k : ℕ) (r ctx : Bits) (h : r.length < k) :
    (outcome (encodeNat k ++ r) ctx).l = some 10 := by
  have hg := guard_contract r k.bits [] ctx
  simp only [value_bits, if_neg (Nat.not_le_of_lt h)] at hg
  simpa only [outcome, parseNat_append] using hg.1

theorem huge_count (ctx : Bits) : readBack (outcome (encodeNat (2^80) ++ [true,false,true]) ctx) = none := by
  rw [(precheck_refines ..).1]
  simp [reference, parseNat_append]

theorem zero_count (r ctx : Bits) :
    outcome (encodeNat 0 ++ r) ctx = atLabel 9 r [] [] [] [] ctx := by
  simp [outcome, parseNat_append, guardEnd, predWord, marks]

theorem init_eq (s : Bits) : initList machine s = atLabel 0 s [] [] [] [] [] := by
  simp only [initList, machine, atLabel]
  congr 1
  funext k; fin_cases k <;> rfl

def precheck_from_init (s : Bits) : Run (initList machine s) (outcome s []) (8*(s.length+1)^2) := by
  rw [init_eq]
  exact precheck_run s []

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end UAVProof.TreeBudgetListGuardTM2
