import LeanCompletion.UAV.TreeBudgetRowCheckTM2
import LeanCompletion.UAV.TreeBudgetSignedTableRuns

namespace UAVProof.A4RowCheckExamples
open TreeBudgetBinaryCodec TreeBudgetFrameRoutineTM2 A4RowCheck Turing

def run : ℕ → Configuration K (TreeBudgetSemanticRegisterTM2.Label PC) → Option (Configuration K (TreeBudgetSemanticRegisterTM2.Label PC))
  | 0,_ => none
  | fuel+1,c => match machine.step c with
    | none => some c
    | some d => run fuel d

def input (P H p : List ℕ) (A : List ℤ) (T : ℤ) (root : ℕ) :=
  start (P.flatMap encodeNat) (H.flatMap encodeNat) (p.flatMap encodeNat)
    (TreeBudgetSignedTableTM2.positive A) (TreeBudgetSignedTableTM2.negative A)
    root.bits T.toNat.bits (-T).toNat.bits [true,false,true] [false,true,false]
def output (b : Bool) (P H p : List ℕ) (A : List ℤ) (T : ℤ) (root : ℕ) :=
  stopped b (P.flatMap encodeNat) (H.flatMap encodeNat) (p.flatMap encodeNat)
    (TreeBudgetSignedTableTM2.positive A) (TreeBudgetSignedTableTM2.negative A)
    root.bits T.toNat.bits (-T).toNat.bits [true,false,true] [false,true,false]
def snap (c : Configuration K (TreeBudgetSemanticRegisterTM2.Label PC)) :=
  (c.l.isNone, c.var,
    List.ofFn (fun i : Fin 35 => c.stk (reg i)),
    List.ofFn (fun i : Fin 7 => c.stk (.inl (.inl i))),
    c.stk (.inl (.inr false)), c.stk (.inl (.inr true)))
def exactResult (b : Bool) (P H p : List ℕ) (A : List ℤ) (T : ℤ) (root : ℕ) :=
  (run 5000 (input P H p A T root)).map snap = some (snap (output b P H p A T root))

set_option maxRecDepth 200000
set_option maxHeartbeats 128000000

theorem negative_later_term_recovers :
    exactResult true [0,0,1] [0,1,1] [0,1,1] [0,5,-12] (-2) 0 := by rfl
theorem forward_parent_index :
    exactResult true [0,2,0] [0,1,1] [0,1,1] [0,0,0] 0 0 := by rfl
theorem missing_forward_parent :
    exactResult false [0,2,0] [0,1,1] [0,1,0] [0,0,0] 0 0 := by rfl
theorem nonzero_root_rejects :
    exactResult false [0,0] [1,1] [1,1] [0,0] 0 0 := by rfl
theorem capacity_rejects :
    exactResult false [0,0] [0,1] [0,2] [0,0] 0 0 := by rfl
theorem two_root_departures_reject :
    exactResult false [0,0,0] [0,1,1] [0,1,1] [0,0,0] 0 0 := by rfl
theorem negative_budget_exact :
    exactResult true [0,0] [0,1] [0,1] [0,-5] (-5) 0 := by rfl
theorem budget_excess_rejects :
    exactResult false [0,0] [0,1] [0,1] [0,5] 4 0 := by rfl
theorem zero_row_still_rejects :
    exactResult false [0] [0] [0] [0] 0 0 := by rfl
theorem nonzero_root_index :
    exactResult true [1,1,0] [1,123,1] [1,0,1] [0,0,0] 0 1 := by rfl

theorem signed_split_keeps_zero_and_order :
    TreeBudgetSignedTableTM2.positive [-5,0,7]=[0,0,7].flatMap encodeNat ∧
    TreeBudgetSignedTableTM2.negative [-5,0,7]=[5,0,0].flatMap encodeNat := ⟨rfl,rfl⟩

end UAVProof.A4RowCheckExamples
