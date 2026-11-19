import LeanCompletion.UAV.TreeBudgetParentWalkRuns

namespace UAVProof.TreeBudgetParentWalkTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call Turing StateTransition

/-- One logical parent lookup on a possibly malformed internal query. -/
def parts (q : Bits) : Option (List ℕ × ℕ × Bits) := do
  let (xs,r) ← parseNats q
  let (a,t) ← parseNat r
  return (xs,a,t)

def bodyOf (q : Bits) := ((parseNat q).map Prod.snd).getD []
def nextQuery (xs : List ℕ) (a : ℕ) (t : Bits) :=
  encodeNat a ++ (xs.flatMap encodeNat ++ (encodeNat a ++ t))

theorem parts_canonical (q : Bits) (xs : List ℕ) (a : ℕ) (t : Bits)
    (h : parts q = some (xs,a,t)) : q = encodeNats xs ++ (encodeNat a ++ t) := by
  cases hp : parseNats q with
  | none => simp [parts,hp] at h
  | some p =>
    obtain ⟨ys,r⟩ := p
    cases hv : parseNat r with
    | none => simp [parts,hp,hv] at h
    | some p =>
      obtain ⟨b,u⟩ := p
      simp [parts,hp,hv] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      rw [parseList_canonical encodeNat parseNat parseNat_canonical q r ys hp,
        parseNat_canonical r u b hv]

theorem query_invariant (q : Bits) (xs : List ℕ) (a : ℕ) (t : Bits)
    (h : parts q = some (xs,a,t)) :
    bodyOf (nextQuery xs a t) = bodyOf q ∧ (nextQuery xs a t).length ≤ 2*(bodyOf q).length := by
  rw [parts_canonical q xs a t h]
  simp [bodyOf,nextQuery,encodeList,List.append_assoc,parseNat_append]
  omega

def rejected (q ticks ctx : Bits) : Cfg :=
  {callCfg ticks (TreeBudgetParentLookupTM2.finish q ctx) with l := none}

theorem flag_none (q ctx : Bits) (h : parts q = none) :
    (TreeBudgetParentLookupTM2.finish q ctx).var.2 = false := by
  have hs := TreeBudgetIndexedZeroTM2.layout q ctx
  cases hp : parseNats q with
  | none => simp only [hp] at hs; simp [TreeBudgetParentLookupTM2.finish,hs,
      TreeBudgetParentLookupTM2.liftCfg,embed]
  | some p =>
    obtain ⟨xs,r⟩ := p
    simp only [hp] at hs
    cases hv : parseNat r with
    | none => simp [TreeBudgetParentLookupTM2.finish,TreeBudgetParentLookupTM2.terminalField,hs,hv]
    | some p => obtain ⟨a,t⟩ := p; simp [parts,hp,hv] at h

def reject_run (q ticks ctx : Bits) (b : Bool) (h : parts q = none) :
    Run (cfg 7 q [] [] [] (b::ticks) ctx) (rejected q ticks ctx) (32*(q.length+1)^2) := by
  let c := TreeBudgetParentLookupTM2.finish q ctx
  have hc : c.l = none := by unfold c TreeBudgetParentLookupTM2.finish; dsimp only; split <;> rfl
  have hf : c.var.2 = false := flag_none q ctx h
  have ret : machine.step (callCfg ticks c) = some (rejected q ticks ctx) := by
    change _ = some {callCfg ticks c with l := none}
    simp [machine,FinTM2.step,TM2.step,TM2.stepAux,callCfg,embed,hc,hf,program]
  have parser := call_run (R := Unit) Sum.inl (.inr (0 : Fin 8)) (fun _ => ticks)
    TreeBudgetParentLookupTM2.program program (fun _ => rfl) (TreeBudgetParentLookupTM2.lookup_run q ctx)
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ (once (tick_step b q ticks ctx)) parser
  have hpos : 0 < (q.length+1)^2 := Nat.pow_pos (by omega)
  exact weaken (EvalsToInTime.trans machine.step _ _ _ _ _ seq (once ret)) (by omega)

def walkEnd : Bits → Bits → Bits → Cfg
  | [], q, ctx => done q ctx
  | _ :: left, q, ctx => match parts q with
    | none => rejected q left ctx
    | some (xs,a,t) => walkEnd left (nextQuery xs a t) ctx

def arbitrary_run (ticks q ctx : Bits) (N : ℕ) (hq : q.length ≤ N) (hb : 2*(bodyOf q).length ≤ N) :
    Run (cfg 7 q [] [] [] ticks ctx) (walkEnd ticks q ctx) (ticks.length*(32*(N+1)^2)+1) := by
  induction ticks generalizing q with
  | nil =>
    simp only [List.length_nil,Nat.zero_mul,Nat.zero_add,walkEnd]
    apply once
    exact stop_step _ _
  | cons b left ih =>
    have hs : (q.length+1)^2 ≤ (N+1)^2 := by gcongr
    cases hp : parts q with
    | none =>
      simp only [walkEnd,hp]
      apply weaken (reject_run q left ctx b hp)
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega
    | some p =>
      obtain ⟨xs,a,t⟩ := p
      have he := parts_canonical q xs a t hp
      have hinv := query_invariant q xs a t hp
      have head := one_hop xs a t left ctx b
      rw [← he] at head
      have tail := ih (nextQuery xs a t) (hinv.2.trans hb) (hinv.1.symm ▸ hb)
      simp only [walkEnd,hp]
      apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ head tail)
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega

theorem body_length (q : Bits) : (bodyOf q).length ≤ q.length := by
  cases hp : parseNat q with
  | none => simp [bodyOf,hp]
  | some p =>
    obtain ⟨i,r⟩ := p
    have h := congrArg List.length (parseNat_canonical q r i hp)
    simp only [List.length_append] at h
    simp [bodyOf,hp]; omega

def total_run (ticks q ctx : Bits) :
    Run (cfg 7 q [] [] [] ticks ctx) (walkEnd ticks q ctx) (ticks.length*(32*(2*q.length+1)^2)+1) :=
  arbitrary_run ticks q ctx (2*q.length) (by omega) (Nat.mul_le_mul_left 2 (body_length q))

def walkQuery : Bits → Bits → Option Bits
  | [], q => some q
  | _ :: left, q => (parts q).bind (fun (xs,a,t) => walkQuery left (nextQuery xs a t))

def read (c : Cfg) : Option Bits := if c.var.2 then some (c.stk src) else none

theorem arbitrary_refines (ticks q ctx : Bits) :
    read (walkEnd ticks q ctx) = walkQuery ticks q ∧
    (walkEnd ticks q ctx).stk (.inl (.inl 5)) = ctx := by
  induction ticks generalizing q with
  | nil => exact ⟨rfl,rfl⟩
  | cons b left ih =>
    cases hp : parts q with
    | none =>
      have hf := flag_none q ctx hp
      have hc := (TreeBudgetParentLookupTM2.refines q ctx).2
      simp [walkEnd,walkQuery,hp,rejected,callCfg,embed,banks,read,hf,hc]
    | some pair =>
      obtain ⟨xs,a,t⟩ := pair
      simpa [walkEnd,walkQuery,hp] using ih (nextQuery xs a t)

theorem terminal (ticks q ctx : Bits) : (walkEnd ticks q ctx).l = none := by
  induction ticks generalizing q with
  | nil => rfl
  | cons b ticks ih =>
    simp only [walkEnd]
    split
    · rfl
    · apply ih

end UAVProof.TreeBudgetParentWalkTM2
