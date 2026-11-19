import LeanCompletion.UAV.TreeBudgetNatListLoop

namespace UAVProof.TreeBudgetNatListLoop
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing StateTransition

/-- Exact intermediate stacks even when the unexamined tail is malformed.
The remaining loop tokens count only the elements still to be attempted. -/
def prefix_run {M : L → Stmt} (link : Linked M) (ns : List ℕ) (left : ℕ)
    (t acc ctx : Bits) : EvalsToInTime (TM2.step M)
      (conf 9 (ns.flatMap encodeNat ++ t) [] (List.replicate (ns.length+left) true) acc ctx)
      (some (conf 9 t [] (List.replicate left true) ((ns.flatMap encodeNat).reverse ++ acc) ctx))
      (4*(ns.flatMap encodeNat).length + 4*ns.length) := by
  induction ns generalizing acc with
  | nil => simpa using EvalsToInTime.refl (TM2.step M) (conf 9 t [] (List.replicate left true) acc ctx)
  | cons n ns ih =>
    let r := ns.flatMap encodeNat ++ t
    let tok := List.replicate (ns.length+left) true
    have parse := framed_run ports (base tok acc ctx) labels 15 10 true M link.frame
      n.bits r none true [] []
    have field : EvalsToInTime (TM2.step M) (conf 11 (encodeNat n ++ r) [] tok acc ctx)
        (some (conf 15 r n.bits tok acc ctx)) (3*n.bits.length+2) := by
      simpa [conf, encodeNat, labels, TreeBudgetCanonicalDigits.lastDigit_bits] using parse
    have head := prepend (tick_cons link (encodeNat n ++ r) tok acc ctx) field
    have store := emit_run link n.bits r tok acc ctx
    have written := EvalsToInTime.trans (TM2.step M) _ _ _ _ _ head store
    have tail := ih ((encodeNat n).reverse ++ acc)
    have run := EvalsToInTime.trans (TM2.step M) _ _ _ _ _ written tail
    have hk : (n :: ns).length+left = (ns.length+left)+1 := by simp; omega
    apply weaken (by simpa only [hk, List.flatMap_cons, List.append_assoc, List.reverse_append,
      List.replicate_succ, r, tok, encodeNat] using run)
    simp only [List.flatMap_cons, List.length_append, List.length_cons, encodeNat_length, Nat.size_eq_bits_len]
    omega

theorem prefix_decomposition (j : ℕ) (r t : Bits) (ns : List ℕ)
    (h : parseMany parseNat j r = some (ns,t)) : r = ns.flatMap encodeNat ++ t :=
  parseMany_canonical _ _ (fun input rest x => parseNat_canonical input rest x) _ _ _ _ h

end UAVProof.TreeBudgetNatListLoop
