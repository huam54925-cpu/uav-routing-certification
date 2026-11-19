import LeanCompletion.UAV.TreeBudgetParentWalkTM2

namespace UAVProof.TreeBudgetParentWalkTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 TreeBudgetTM2Call TreeBudgetParentArray Turing StateTransition

def callCfg (ticks : Bits) := embed (K := TreeBudgetParentLookupTM2.K) (Λ := TreeBudgetParentLookupTM2.L)
  Sum.inl (Sum.inr (0 : Fin 8)) (fun _ : Unit => ticks)

theorem list_output (xs : List ℕ) (t ctx : Bits) :
    TreeBudgetCountedNatsTM2.stopped (encodeNats xs ++ t) ctx =
      {TreeBudgetNatListLoop.conf 17 t (xs.flatMap encodeNat) [] [] ctx with l := none} := by
  have hm := parseMany_append encodeNat parseNat parseNat_append xs t
  have hg : xs.length ≤ (xs.flatMap encodeNat ++ t).length := by
    have h := length_le_flatMap encodeNat encodeNat_nonempty xs
    simp only [List.length_append]; omega
  have h := TreeBudgetNatListLoop.loop_contract xs.length (xs.flatMap encodeNat ++ t) [] ctx
  simp only [hm,List.reverse_nil,List.nil_append] at h
  simp only [TreeBudgetCountedNatsTM2.stopped,TreeBudgetCountedNatsTM2.result,encodeNats,encodeList,
    List.append_assoc,parseNat_append,if_pos hg,h]
  rfl

theorem lookup_return (xs : List ℕ) (a : ℕ) (t ticks ctx : Bits) :
    callCfg ticks (TreeBudgetParentLookupTM2.finish (encodeNats xs ++ (encodeNat a ++ t)) ctx) =
      cfg 0 t (xs.flatMap encodeNat) a.bits [] ticks ctx := by
  simp only [TreeBudgetParentLookupTM2.finish,list_output]
  change callCfg ticks (TreeBudgetParentLookupTM2.terminalField _ (encodeNat a ++ t)) = _
  simp only [TreeBudgetParentLookupTM2.terminalField,TreeBudgetParentLookupTM2.field,parseNat_append]
  unfold callCfg embed cfg
  congr 1
  funext k
  cases k with
  | inr u => cases u; rfl
  | inl k => cases k with
    | inr b => cases b <;> rfl
    | inl i => fin_cases i <;> rfl

theorem tick_step (b : Bool) (q ticks ctx : Bits) : machine.step (cfg 7 q [] [] [] (b::ticks) ctx) =
    some (callCfg ticks (TreeBudgetParentLookupTM2.start q ctx)) := by
  simp [machine,FinTM2.step,TM2.step,TM2.stepAux,cfg,program,scan,jump,store,callCfg,embed,
    TreeBudgetParentLookupTM2.start,TreeBudgetParentLookupTM2.liftCfg,TreeBudgetListGuardTM2.atLabel]
  all_goals congr 2
  all_goals funext k; cases k with
    | inr u => cases u; rfl
    | inl k => cases k with
      | inr b => cases b <;> rfl
      | inl i => fin_cases i <;> rfl

theorem dispatch_step (f d t ticks ctx : Bits) :
    machine.step (cfg 0 t f d [] ticks ctx) = some (cfg 1 t f d [] ticks ctx) := rfl

def one_hop (xs : List ℕ) (a : ℕ) (t ticks ctx : Bits) (b : Bool) :
    let q := encodeNats xs ++ (encodeNat a ++ t)
    Run (cfg 7 q [] [] [] (b::ticks) ctx)
      (cfg 7 (encodeNat a ++ (xs.flatMap encodeNat ++ (encodeNat a ++ t))) [] [] [] ticks ctx)
      (32*(q.length+1)^2) := by
  dsimp only
  let q := encodeNats xs ++ (encodeNat a ++ t)
  have first := once (tick_step b q ticks ctx)
  have parser := call_run (R := Unit) Sum.inl (.inr (0 : Fin 8)) (fun _ => ticks)
    TreeBudgetParentLookupTM2.program program (fun _ => rfl) (TreeBudgetParentLookupTM2.lookup_run q ctx)
  change Run (callCfg ticks (TreeBudgetParentLookupTM2.start q ctx))
    (callCfg ticks (TreeBudgetParentLookupTM2.finish q ctx)) _ at parser
  have hout := lookup_return xs a t ticks ctx
  rw [show callCfg ticks (TreeBudgetParentLookupTM2.finish q ctx) = _ from hout] at parser
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ first parser
  have seq := EvalsToInTime.trans machine.step _ _ _ _ _ seq (once (dispatch_step ..))
  have recon := requery (xs.flatMap encodeNat) a.bits t ticks ctx
  apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ seq recon)
  have hw : 4*a.bits.length + 2*(xs.flatMap encodeNat).length+8 ≤ 8*(q.length+1) := by
    simp only [q,encodeNats,encodeList,List.length_append,encodeNat_length,Nat.size_eq_bits_len]
    omega
  have hs : q.length+1 ≤ (q.length+1)^2 := Nat.le_self_pow (by decide) _
  change _ ≤ 32*(q.length+1)^2
  omega

def table {n : ℕ} (P : ParentArray n) := P.parents.toList.map Fin.val
def body {n : ℕ} (P : ParentArray n) := (table P).flatMap encodeNat
def query {n : ℕ} (P : ParentArray n) (v : Fin n) := encodeNat v.val ++ body P

theorem query_width {n : ℕ} (P : ParentArray n) (v : Fin n) :
    (query P v).length ≤ (body P).length + 2*n.size+1 := by
  have h := Nat.size_le_size v.isLt.le
  simp only [query,List.length_append,encodeNat_length]
  omega

def parent_hop {n : ℕ} (P : ParentArray n) (v : Fin n) (b : Bool) (ticks ctx : Bits) :
    Run (cfg 7 (query P v) [] [] [] (b::ticks) ctx)
      (cfg 7 (query P (parent P v)) [] [] [] ticks ctx) (32*((query P v).length+1)^2) := by
  let xs := table P
  have hi : v.val < xs.length := by simp [xs,table]
  have eqn : xs.take v.val ++ xs[v.val] :: xs.drop (v.val+1) = xs := by
    rw [List.getElem_cons_drop,List.take_append_drop]
  have hb : (xs.take v.val).flatMap encodeNat ++ (encodeNat xs[v.val] ++
      (xs.drop (v.val+1)).flatMap encodeNat) = body P := by
    simpa only [List.flatMap_append,List.flatMap_cons] using congrArg (List.flatMap encodeNat) eqn
  have hh := one_hop (xs.take v.val) xs[v.val] ((xs.drop (v.val+1)).flatMap encodeNat) ticks ctx b
  simp only [encodeNats,encodeList,List.append_assoc,List.length_take,Nat.min_eq_left hi.le,hb] at hh
  simpa [query,xs,table,parent] using hh

def done (q ctx : Bits) : Cfg := ⟨none,(none,true),store q [] [] [] [] ctx⟩

theorem stop_step (q ctx : Bits) : machine.step (cfg 7 q [] [] [] [] ctx) = some (done q ctx) := by
  simp [machine,FinTM2.step,TM2.step,TM2.stepAux,cfg,done,program,scan,store]
  all_goals congr 2
  all_goals funext k; cases k with
    | inr u => cases u; rfl
    | inl k => rfl

def walk_run {n : ℕ} (P : ParentArray n) (ticks ctx : Bits) (v : Fin n) :
    Run (cfg 7 (query P v) [] [] [] ticks ctx)
      (done (query P (follow P ticks.length v)) ctx)
      (ticks.length * (32*((body P).length+2*n.size+2)^2)+1) := by
  induction ticks generalizing v with
  | nil =>
    simp only [List.length_nil,Nat.zero_mul,Nat.zero_add,follow]
    apply once
    exact stop_step _ _
  | cons b ticks ih =>
    have first := parent_hop P v b ticks ctx
    have tail := ih (parent P v)
    apply weaken (EvalsToInTime.trans machine.step _ _ _ _ _ first tail)
    have h := query_width P v
    have hs : ((query P v).length+1)^2 ≤ ((body P).length+2*n.size+2)^2 := by gcongr
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem follow_refines {n : ℕ} (P : ParentArray n) (ticks ctx : Bits) (v : Fin n) :
    (done (query P (follow P ticks.length v)) ctx).stk src =
      query P (TreeBudgetCostedInput.followCost P ticks.length v).value := by simp [done,store]

end UAVProof.TreeBudgetParentWalkTM2
