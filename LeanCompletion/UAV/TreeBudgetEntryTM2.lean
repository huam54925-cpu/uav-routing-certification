import LeanCompletion.UAV.TreeBudgetCountedNatsHalt
import LeanCompletion.UAV.TreeBudgetTM2Call
import LeanCompletion.UAV.TreeBudgetSparseCostedParsing

namespace UAVProof.TreeBudgetEntryTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetCanonicalDigits Turing StateTransition
open TreeBudgetTM2Call (banks embed compile call_run)

abbrev K := (Fin 7) ⊕ Unit
abbrev L := (Fin 18) ⊕ (Fin 6)
abbrev Cfg := Configuration K L
abbrev Stmt := Statement K L

def ports : Ports K := ⟨.inl 0,.inl 1,.inr (),by decide,by decide,by decide⟩
def labels : Phase → L
  | .marker => .inr 0 | .payload => .inr 1 | .reverse => .inr 2 | .clear => .inr 3

def program : L → Stmt
  | .inl l => compile Sum.inl (.inr 5) (TreeBudgetListGuardTM2.program l)
  | .inr l => match l.val with
    | 0 => code ports labels (.inl 0) (.inr 4) true .marker
    | 1 => code ports labels (.inl 0) (.inr 4) true .payload
    | 2 => code ports labels (.inl 0) (.inr 4) true .reverse
    | 3 => code ports labels (.inl 0) (.inr 4) true .clear
    | 4 => .load (fun _ => (none,false)) .halt
    | _ => .halt

def machine : FinTM2 where
  K := K
  k₀ := .inl 0
  k₁ := .inl 2
  Γ _ := Bool
  Λ := L
  main := labels .marker
  σ := State
  initialState := (none,true)
  m := program

def base (ctx : Bits) : K → Bits := fun k => if k = .inl 5 then ctx else []
def start (s ctx : Bits) : Cfg := cfg ports (base ctx) (labels .marker) none true s [] []
def invalid (s ctx : Bits) : Cfg := cfg ports (base ctx) (.inr 4) none true
  (TreeBudgetNatListLoop.suffix s) [] []
def callee (n : ℕ) (c : TreeBudgetListGuardTM2.Cfg) : Cfg :=
  embed Sum.inl (.inr 5) (fun _ : Unit => n.bits) c

theorem routine_eq (p : Phase) : program (labels p) = code ports labels (.inl 0) (.inr 4) true p := by
  cases p <;> rfl

theorem transfer_eq (r ctx : Bits) (n : ℕ) : cfg ports (base ctx) (.inl 0) none true r [] n.bits =
    callee n (TreeBudgetListGuardTM2.atLabel 0 r [] [] [] [] ctx) := by
  unfold callee embed TreeBudgetListGuardTM2.atLabel cfg
  congr 1
  funext k; cases k with
  | inl i => fin_cases i <;> rfl
  | inr i => cases i; rfl

def first (s ctx : Bits) : Cfg := match parseNat s with
  | none => invalid s ctx
  | some (n,r) => callee n (TreeBudgetListGuardTM2.atLabel 0 r [] [] [] [] ctx)

def first_run (s ctx : Bits) : EvalsToInTime machine.step (start s ctx) (some (first s ctx))
    (2*s.length+2) := by
  cases hw : parseWord s with
  | none =>
    have run := truncated_run ports (base ctx) labels (.inl 0) (.inr 4) true program routine_eq s hw none true [] []
    simpa [machine, FinTM2.step, first, parseNat_truncated s hw, start, invalid, TreeBudgetNatListLoop.suffix, hw] using run
  | some pair =>
    obtain ⟨bs,r⟩ := pair
    have eq := parseWord_consumed s bs r hw
    subst s
    have run := framed_run ports (base ctx) labels (.inl 0) (.inr 4) true program routine_eq bs r none true [] []
    have hb : 3*bs.length+2 ≤ 2*(word bs ++ r).length+2 := by simp [word_length]; omega
    cases hc : lastDigit bs true with
    | false => simpa [start, machine, FinTM2.step, first, parseNat_framed, hc, invalid,
        TreeBudgetNatListLoop.suffix, parseWord_append] using weaken run hb
    | true =>
      have he := transfer_eq r ctx (value bs)
      rw [canonical_of_last bs hc] at he
      simpa [start, machine, FinTM2.step, first, parseNat_framed, hc, he] using weaken run hb

def stopped (s ctx : Bits) : Cfg :=
  match parseNat s with
  | none => {invalid s ctx with l := none, var := (none,false)}
  | some (n,r) => {callee n (TreeBudgetCountedNatsTM2.stopped r ctx) with l := none}

theorem callee_stops (r ctx : Bits) : (TreeBudgetCountedNatsTM2.stopped r ctx).l = none := by
  unfold TreeBudgetCountedNatsTM2.stopped
  dsimp only
  split <;> rfl

def entry_run (s ctx : Bits) : EvalsToInTime machine.step (start s ctx) (some (stopped s ctx))
    (24*(s.length+1)^2) := by
  have head := first_run s ctx
  cases hp : parseNat s with
  | none =>
    simp only [first, hp] at head
    have last : machine.step (invalid s ctx) = some (stopped s ctx) := by rw [stopped,hp]; rfl
    exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _ head (once last)) (by nlinarith)
  | some pair =>
    obtain ⟨n,r⟩ := pair
    simp only [first, hp] at head
    have row := call_run (R := Unit) Sum.inl (Sum.inr (5 : Fin 6)) (fun _ => n.bits)
      TreeBudgetListGuardTM2.program program (fun _ => rfl) (TreeBudgetCountedNatsTM2.list_halts r ctx)
    have last : machine.step (callee n (TreeBudgetCountedNatsTM2.stopped r ctx)) =
        some (stopped s ctx) := by
      rw [stopped,hp]
      simp [machine, FinTM2.step, TM2.step, callee, embed, callee_stops, program, TM2.stepAux]
    have run := EvalsToInTime.trans machine.step _ _ _ _ _
      (EvalsToInTime.trans machine.step _ _ _ _ _ head row) (once last)
    have hl := congrArg List.length (parseNat_canonical s r n hp)
    simp only [List.length_append] at hl
    have hb : (r.length+1)^2 ≤ (s.length+1)^2 := by gcongr; omega
    exact weaken run (by nlinarith)

def readEntry (c : Cfg) : Option (TreeBudgetSparseCodec.RawEntry × Bits) :=
  if c.var.2 then (TreeBudgetNatListLoop.fields (c.stk (.inl 2)).length (c.stk (.inl 2))).map
    (fun ns => ((value (c.stk (.inr ())), ns), c.stk (.inl 0)))
  else none

theorem refines (s ctx : Bits) : readEntry (stopped s ctx) = (TreeBudgetSparseCostedParsing.parseEntryD s).value ∧
    (stopped s ctx).stk (.inl 5) = ctx := by
  rw [TreeBudgetSparseCostedParsing.parseEntryD_value]
  cases hp : parseNat s with
  | none => simp [stopped, hp, readEntry, TreeBudgetSparseCodec.parseEntry, invalid, cfg, tapes, base, ports, TreeBudgetNatListLoop.suffix]
  | some pair =>
    obtain ⟨n,r⟩ := pair
    have hr := TreeBudgetCountedNatsTM2.halted_refines r ctx
    rw [TreeBudgetCostedParsing.parseNatsD_value] at hr
    obtain ⟨he,hctx⟩ := hr
    simp only [TreeBudgetCountedNatsTM2.readStopped] at he
    cases hf : (TreeBudgetCountedNatsTM2.stopped r ctx).var.2 <;>
      simp [readEntry, stopped, hp, callee, embed, banks, hf, TreeBudgetSparseCodec.parseEntry,
        ← he, hctx]
    cases TreeBudgetNatListLoop.fields ((TreeBudgetCountedNatsTM2.stopped r ctx).stk 2).length
      ((TreeBudgetCountedNatsTM2.stopped r ctx).stk 2) <;> rfl

theorem entry_suffix (e : TreeBudgetSparseCodec.RawEntry) (tail ctx : Bits) :
    readEntry (stopped (TreeBudgetSparseCodec.encodeEntry e ++ tail) ctx) = some (e,tail) := by
  rw [(refines _ ctx).1, TreeBudgetSparseCostedParsing.parseEntryD_value,
    TreeBudgetSparseCodec.parseEntry_append]

theorem init_eq (s : Bits) : initList machine s = start s [] := by
  simp only [initList, machine, start, cfg]
  congr 1
  funext k; cases k with
  | inl i => fin_cases i <;> rfl
  | inr i => cases i; rfl

def entry_from_init (s : Bits) : EvalsToInTime machine.step (initList machine s) (some (stopped s []))
    (24*(s.length+1)^2) := by rw [init_eq]; exact entry_run s []

theorem finite_alphabet (k : machine.K) : Finite (machine.Γ k) := by change Finite Bool; infer_instance

end UAVProof.TreeBudgetEntryTM2
