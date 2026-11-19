import LeanCompletion.UAV.TreeBudgetBinaryCodec

namespace UAVProof.TreeBudgetNatListLoop
open TreeBudgetBinaryCodec

/-- Decode a stack of delimited outputs until the stack is empty. -/
def fields : ℕ → Bits → Option (List ℕ)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel+1, b :: bs => do
    let (n,t) ← parseNat (b :: bs)
    let tail ← fields fuel t
    return n :: tail

theorem fields_encoded (ns : List ℕ) (fuel : ℕ) (hf : ns.length ≤ fuel) :
    fields fuel (ns.flatMap encodeNat) = some ns := by
  induction ns generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons n ns ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hn := encodeNat_nonempty n
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hf
      simp only [List.flatMap_cons]
      generalize hw : encodeNat n ++ ns.flatMap encodeNat = wire
      have hp : parseNat wire = some (n,ns.flatMap encodeNat) := hw ▸ parseNat_append n _
      cases wire with
      | nil =>
        have hl := congrArg List.length hw
        simp only [List.length_append, List.length_nil] at hl
        omega
      | cons b bs => simp [fields, hp, ih fuel hf]

theorem fields_readback (ns : List ℕ) :
    fields (ns.flatMap encodeNat).length (ns.flatMap encodeNat) = some ns :=
  fields_encoded ns _ (length_le_flatMap encodeNat encodeNat_nonempty ns)

end UAVProof.TreeBudgetNatListLoop
