import LeanCompletion.UAV.TreeBudgetEntryTM2
import LeanCompletion.UAV.TreeBudgetIndexedZeroTM2

/-! Full physical return layouts for repeated compressed-record calls. In
particular, successful calls leave every scratch stack empty. The caller can
move the count and row to its output before restarting at the exact suffix. -/

namespace UAVProof.TreeBudgetCountedNatsTM2
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 Turing

def returned (ns : List ℕ) (tail ctx : Bits) : TreeBudgetListGuardTM2.Cfg :=
  ⟨none, (none, true), TreeBudgetListCleanup.tapes tail [] (ns.flatMap encodeNat) [] [] [] ctx⟩

/-- A successful list parse determines all seven stacks, including scratch. -/
theorem stopped_success (s ctx : Bits) (ns : List ℕ) (tail : Bits)
    (hp : parseNats s = some (ns, tail)) : stopped s ctx = returned ns tail ctx := by
  rw [parseList_canonical encodeNat parseNat parseNat_canonical s tail ns hp]
  have hb : ns.length ≤ (ns.flatMap encodeNat ++ tail).length := by
    have h := length_le_flatMap encodeNat encodeNat_nonempty ns
    simp only [List.length_append]
    omega
  have hl := TreeBudgetNatListLoop.loop_contract ns.length (ns.flatMap encodeNat ++ tail) [] ctx
  rw [parseMany_append encodeNat parseNat parseNat_append] at hl
  simp only [List.reverse_nil, List.nil_append] at hl
  simp only [stopped, result, encodeList, List.append_assoc, parseNat_append,
    if_pos hb, hl]
  simp only [TreeBudgetNatListLoop.conf, cfg, returned, ↓reduceIte]
  congr 1
  funext k
  fin_cases k <;> rfl

end UAVProof.TreeBudgetCountedNatsTM2

namespace UAVProof.TreeBudgetEntryTM2
open TreeBudgetBinaryCodec TreeBudgetSparseCodec TreeBudgetFrameRoutineTM2
open Turing StateTransition

def returned (e : RawEntry) (tail ctx : Bits) : Cfg :=
  ⟨none, (none, true), TreeBudgetTM2Call.banks
    (TreeBudgetCountedNatsTM2.returned e.2 tail ctx).stk (fun _ : Unit => e.1.bits)⟩

/-- Full physical return layout, with no restriction on the next record. -/
theorem stopped_success (s ctx : Bits) (e : RawEntry) (tail : Bits)
    (hp : parseEntry s = some (e, tail)) : stopped s ctx = returned e tail ctx := by
  rw [parseEntry_canonical s tail e hp]
  rcases e with ⟨count, row⟩
  simp only [encodeEntry, List.append_assoc, stopped, parseNat_append]
  rw [TreeBudgetCountedNatsTM2.stopped_success (encodeNats row ++ tail) ctx row tail
    (parseNats_append row tail)]
  rfl

/-- The physical result flag reflects parsing failure as well as success. -/
theorem stopped_flag (s ctx : Bits) : (stopped s ctx).var.2 = (parseEntry s).isSome := by
  cases hp : parseNat s with
  | none => simp [stopped, hp, parseEntry, invalid, cfg]
  | some pair =>
    obtain ⟨count, rest⟩ := pair
    have hl := TreeBudgetIndexedZeroTM2.layout rest ctx
    cases hr : parseNats rest with
    | none =>
      simp only [hr] at hl
      simpa [stopped, hp, parseEntry, hr, callee, TreeBudgetTM2Call.embed] using hl
    | some pair =>
      obtain ⟨row, tail⟩ := pair
      simp only [hr] at hl
      simpa [stopped, hp, parseEntry, hr, callee, TreeBudgetTM2Call.embed] using hl.1

theorem returned_fields (e : RawEntry) (tail ctx : Bits) :
    (returned e tail ctx).stk (.inl 0) = tail ∧
    (returned e tail ctx).stk (.inl 2) = e.2.flatMap encodeNat ∧
    (returned e tail ctx).stk (.inr ()) = e.1.bits ∧
    (returned e tail ctx).stk (.inl 5) = ctx := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem returned_scratch (e : RawEntry) (tail ctx : Bits) (k : Fin 7)
    (h0 : k ≠ 0) (h2 : k ≠ 2) (h5 : k ≠ 5) :
    (returned e tail ctx).stk (.inl k) = [] := by
  fin_cases k <;> simp_all [returned, TreeBudgetCountedNatsTM2.returned,
    TreeBudgetTM2Call.banks, TreeBudgetListCleanup.tapes]

theorem stopped_halted (s ctx : Bits) : (stopped s ctx).l = none := by
  unfold stopped
  split <;> rfl

/-- The existing quadratic run now ends in an explicit reusable stack layout. -/
def entry_success_run (s ctx : Bits) (e : RawEntry) (tail : Bits)
    (hp : parseEntry s = some (e, tail)) :
    EvalsToInTime machine.step (start s ctx) (some (returned e tail ctx))
      (24 * (s.length + 1)^2) := by
  rw [← stopped_success s ctx e tail hp]
  exact entry_run s ctx

theorem entry_layout_polynomial (s ctx : Bits) :
    ∃ out, Nonempty (EvalsToInTime machine.step (start s ctx) (some out)
      (24 * (s.length + 1)^2)) ∧ out.l = none ∧
      out.var.2 = (parseEntry s).isSome ∧ out.stk (.inl 5) = ctx ∧
      (∀ e tail, parseEntry s = some (e, tail) → out = returned e tail ctx) := by
  exact ⟨stopped s ctx, ⟨entry_run s ctx⟩, stopped_halted s ctx, stopped_flag s ctx,
    (refines s ctx).2, stopped_success s ctx⟩

end UAVProof.TreeBudgetEntryTM2
