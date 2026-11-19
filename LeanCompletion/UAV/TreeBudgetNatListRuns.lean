import LeanCompletion.UAV.TreeBudgetNatListLoop

namespace UAVProof.TreeBudgetNatListLoop
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition

def loopEnd : ℕ → Bits → Bits → Bits → Cfg
  | 0, r, acc, ctx => conf 17 r acc.reverse [] [] ctx
  | k+1, r, acc, ctx =>
    match parseNat r with
    | none => conf 10 (suffix r) [] (List.replicate k true) acc ctx
    | some (n,t) => loopEnd k t ((encodeNat n).reverse ++ acc) ctx

def loop_run {M : L → Stmt} (link : Linked M) (k : ℕ) (r acc ctx : Bits) (N : ℕ)
    (hN : r.length + acc.length ≤ N) :
    EvalsToInTime (TM2.step M) (conf 9 r [] (List.replicate k true) acc ctx)
      (some (loopEnd k r acc ctx)) ((k+1)*(4*N+8)) := by
  induction k generalizing r acc with
  | zero =>
    have run := prepend (tick_nil link r acc ctx) (finish_run link acc r [] ctx)
    apply weaken (by simpa [loopEnd] using run)
    simp; omega
  | succ k ih =>
    have head := prepend (tick_cons link r (List.replicate k true) acc ctx)
      (field_run link r (List.replicate k true) acc ctx)
    cases hp : parseNat r with
    | none =>
      apply weaken (by simpa [List.replicate_succ, fieldEnd, hp, loopEnd] using head)
      nlinarith
    | some pair =>
      obtain ⟨n,t⟩ := pair
      have he := parseNat_canonical r t n hp
      have hl := congrArg List.length he
      simp only [List.length_append] at hl
      have hb : t.length + ((encodeNat n).reverse ++ acc).length ≤ N := by
        simp only [List.length_append, List.length_reverse]; omega
      have tail := ih t ((encodeNat n).reverse ++ acc) hb
      have emit := emit_run link n.bits t (List.replicate k true) acc ctx
      simp only [fieldEnd, hp] at head
      have seq := EvalsToInTime.trans (TM2.step M) _ _ _ _ _ head emit
      have run := EvalsToInTime.trans (TM2.step M) _ _ _ _ _ seq tail
      apply weaken (by simpa only [loopEnd, hp, List.replicate_succ] using run)
      rw [encodeNat_length] at hl
      rw [Nat.size_eq_bits_len]
      nlinarith

/-- For success, the output stack is precisely the concatenation of canonical
element encodings, with the oldest stored prefix first. On rejection the
return label identifies failure and the context stack is preserved. -/
theorem loop_contract (k : ℕ) (r acc ctx : Bits) :
    match parseMany parseNat k r with
    | none => (loopEnd k r acc ctx).l = some 10 ∧ (loopEnd k r acc ctx).stk 5 = ctx
    | some (ns,t) => loopEnd k r acc ctx = conf 17 t (acc.reverse ++ ns.flatMap encodeNat) [] [] ctx := by
  induction k generalizing r acc with
  | zero => simp [loopEnd, parseMany]
  | succ k ih =>
    cases hp : parseNat r with
    | none => simp [parseMany, loopEnd, hp, conf, cfg, tapes, ports, base]
    | some pair =>
      obtain ⟨n,t⟩ := pair
      have ht := ih t ((encodeNat n).reverse ++ acc)
      cases hm : parseMany parseNat k t with
      | none => simpa [parseMany, hp, hm, loopEnd] using ht
      | some out =>
        obtain ⟨ns,rest⟩ := out
        simpa [parseMany, hp, hm, loopEnd, List.reverse_append, List.append_assoc] using ht

end UAVProof.TreeBudgetNatListLoop
