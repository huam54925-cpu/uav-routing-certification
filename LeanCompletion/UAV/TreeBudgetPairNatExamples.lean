import LeanCompletion.UAV.TreeBudgetPairNatTM2

/-! Kernel-evaluated regressions of the actual finite-control TM2 program,
including stack order, suffix preservation and rejection cleanup. -/
namespace UAVProof.TreeBudgetPairNatExamples
open TreeBudgetBinaryCodec TreeBudgetSparseNPBridge TreeBudgetPairNatTM2

def run : ℕ → machine.Cfg → machine.Cfg
  | 0, c => c
  | n + 1, c => match machine.step c with
    | none => c
    | some d => run n d

def observe (wire : Bits) : Bool × Bits × Bits × Bits × Bits :=
  let c : TreeBudgetFrameRoutineTM2.Configuration (Fin 4) (Fin 10) :=
    run (3 * wire.length + 5) (Turing.initList machine wire)
  (c.var.2, c.stk 0, c.stk 1, c.stk 2, c.stk 3)

theorem zero_empty_certificate : observe (pairWire (encodeNat 0, [])) =
    (true, [], [], [], []) := by decide +kernel

theorem preserves_digit_order : observe (pairWire (encodeNat 6, [])) =
    (true, [], [], [], [false, true, true]) := by decide +kernel

theorem preserves_both_suffixes :
    observe (pairWire (encodeNat 5 ++ [false, true], [true, false])) =
      (true, [true, false], [false, true], [], [true, false, true]) := by decide +kernel

theorem rejects_empty_outer : observe [] = (false, [], [], [], []) := by decide +kernel
theorem rejects_outer_missing_payload : observe [true] = (false, [], [], [], []) := by decide +kernel
theorem rejects_outer_missing_terminator : observe [true, false] =
    (false, [], [], [], []) := by decide +kernel

theorem rejects_empty_instance : observe (pairWire ([], [true])) =
    (false, [true], [], [], []) := by decide +kernel

theorem rejects_inner_missing_payload : observe (pairWire ([true], [true, false])) =
    (false, [true, false], [], [], []) := by decide +kernel

theorem rejects_inner_missing_terminator : observe (pairWire ([true, true], [false])) =
    (false, [false], [], [], []) := by decide +kernel

theorem rejects_noncanonical_zero : observe (pairWire (word [false] ++ [true], [false, true])) =
    (false, [false, true], [true], [], []) := by decide +kernel

theorem rejects_high_zero : observe (pairWire (word [true, false] ++ [false, true], [])) =
    (false, [], [false, true], [], []) := by decide +kernel

theorem accepts_internal_zeros : observe (pairWire (encodeNat 8 ++ [true], [])) =
    (true, [], [true], [], [false, false, false, true]) := by decide +kernel

end UAVProof.TreeBudgetPairNatExamples
