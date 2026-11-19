import LeanCompletion.UAV.TreeBudgetCountedNatsHalt

namespace UAVProof.TreeBudgetCountedNatsExamples
open TreeBudgetBinaryCodec TreeBudgetListGuardTM2 TreeBudgetCountedNatsTM2

def observe : ℕ → Cfg → Option (Option (List ℕ × Bits) × Bits)
  | 0, _ => none
  | n+1, c => if c.l = some 17 ∨ c.l = some 10 then some (readList c, c.stk 5)
    else (machine.step c).bind (observe n)

theorem empty_nonempty_suffix :
    observe 32 (atLabel 0 (encodeNats [] ++ [true,false]) [] [] [] [] [true]) =
      some (some ([], [true,false]), [true]) := by decide +kernel

theorem repeat_zero_order :
    observe 180 (atLabel 0 (encodeNats [2,0,2,1] ++ [false,true]) [] [] [] [] [true,false]) =
      some (some ([2,0,2,1],[false,true]),[true,false]) := by decide +kernel

theorem late_truncation :
    observe 64 (atLabel 0 (encodeNat 2 ++ encodeNat 0 ++ [true]) [] [] [] [] [false]) =
      some (none, [false]) := by decide +kernel

theorem bad_second_word :
    observe 64 (atLabel 0 (encodeNat 2 ++ encodeNat 1 ++ word [false]) [] [] [] [] [true]) =
      some (none, [true]) := by decide +kernel

def finalState : ℕ → Cfg → Option (Option (List ℕ × Bits) × ℕ × Bits)
  | 0, _ => none
  | n+1, c => match machine.step c with
    | some d => finalState n d
    | none => some (readStopped c, TreeBudgetListCleanup.workCells c, c.stk 5)

theorem released_partial_row :
    finalState 80 (atLabel 0 (encodeNat 3 ++ encodeNat 2 ++ [true]) [] [] [] [] [true]) =
      some (none,0,[true]) := by decide +kernel

theorem released_oversized_header :
    finalState 80 (atLabel 0 (encodeNat 8 ++ [true,false]) [] [] [] [] [true]) =
      some (none,0,[true]) := by decide +kernel

end UAVProof.TreeBudgetCountedNatsExamples
