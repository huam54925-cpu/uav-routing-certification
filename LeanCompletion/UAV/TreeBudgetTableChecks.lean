import LeanCompletion.UAV.TreeBudgetParentLookupTM2
import LeanCompletion.UAV.TreeBudgetCostedInput

namespace UAVProof.TreeBudgetTableChecks
open TreeBudgetBinaryCodec TreeBudgetParentArray

/-- Indexed fetch on the table body produced by the counted list parser. -/
theorem get_coordinate (xs : List ℕ) (i : ℕ) (hi : i < xs.length) (ctx : Bits) :
    TreeBudgetParentLookupTM2.read (TreeBudgetParentLookupTM2.finish
      (encodeNat i ++ xs.flatMap encodeNat) ctx) = some (xs[i], (xs.drop (i+1)).flatMap encodeNat) := by
  have h := TreeBudgetParentLookupTM2.indexed_field (xs.take i) (xs.drop (i+1)) xs[i] ctx
  simpa only [List.length_take,Nat.min_eq_left hi.le,List.getElem_cons_drop,List.take_append_drop] using h

/-- This is the index operation used by each step of the parent chase. -/
theorem parent_at {n : ℕ} (P : ParentArray n) (v : Fin n) (ctx : Bits) :
    let table := P.parents.toList.map Fin.val
    TreeBudgetParentLookupTM2.read (TreeBudgetParentLookupTM2.finish
      (encodeNat v.val ++ table.flatMap encodeNat) ctx) =
      some ((parent P v).val, (table.drop (v.val+1)).flatMap encodeNat) := by
  dsimp only
  have hi : v.val < (P.parents.toList.map Fin.val).length := by simp
  simpa [parent] using get_coordinate _ v.val hi ctx

theorem follow_one {n : ℕ} (P : ParentArray n) (v : Fin n) (ctx : Bits) :
    let table := P.parents.toList.map Fin.val
    (TreeBudgetParentLookupTM2.read (TreeBudgetParentLookupTM2.finish
      (encodeNat v.val ++ table.flatMap encodeNat) ctx)).map Prod.fst =
      some (TreeBudgetCostedInput.followCost P 1 v).value.val := by
  simp only [parent_at,Option.map_some,TreeBudgetCostedInput.followCost_value,follow]

/-- The root-coordinate test in rowCheck applies even to a zero-multiplicity entry. -/
theorem row_root_zero {n : ℕ} (P : ParentArray n) (p : Vector ℕ n) (ctx : Bits) :
    (TreeBudgetIndexedZeroTM2.finish (encodeNat P.root.val ++ p.toList.flatMap encodeNat) ctx).var.2 =
      (TreeBudgetBitPrimitives.zeroNatD p[P.root]).value := by
  have hi : P.root.val < p.toList.length := by simp
  have h := (TreeBudgetIndexedZeroTM2.row_coordinate (p.toList.take P.root.val)
    (p.toList.drop (P.root.val+1)) p.toList[P.root.val] ctx).1
  rw [List.getElem_cons_drop, List.take_append_drop, List.length_take, Nat.min_eq_left hi.le] at h
  exact h

theorem row_reject_of_root {n : ℕ} (P : ParentArray n) (H p : Vector ℕ n) (A : Vector ℤ n)
    (budget : ℤ) (ctx : Bits) (h : (TreeBudgetIndexedZeroTM2.finish
      (encodeNat P.root.val ++ p.toList.flatMap encodeNat) ctx).var.2 = false) :
    (TreeBudgetCostedCandidates.rowCheck P H A budget p).value = false := by
  rw [row_root_zero] at h
  simp only [TreeBudgetCostedCandidates.rowCheck,h,Bool.false_and]

def observe : ℕ → TreeBudgetParentLookupTM2.Cfg → Option (Option (ℕ × Bits) × Bits)
  | 0, _ => none
  | n+1, c => match TreeBudgetParentLookupTM2.machine.step c with
    | some d => observe n d
    | none => some (TreeBudgetParentLookupTM2.read c,c.stk (.inl 5))

theorem interior_zero :
    observe 130 (TreeBudgetParentLookupTM2.start
      (encodeNat 1 ++ [2,0,1].flatMap encodeNat) [false,true]) = some (some (0,encodeNat 1),[false,true]) := by rfl

theorem past_end :
    observe 100 (TreeBudgetParentLookupTM2.start (encodeNat 1 ++ encodeNat 3) [true]) =
      some (none,[true]) := by rfl

theorem malformed_target :
    observe 100 (TreeBudgetParentLookupTM2.start (encodeNat 1 ++ encodeNat 2 ++ [true,false,false]) []) =
      some (none,[]) := by rfl

theorem truncated_target :
    observe 100 (TreeBudgetParentLookupTM2.start (encodeNat 1 ++ encodeNat 0 ++ [true]) [false]) =
      some (none,[false]) := by rfl

end UAVProof.TreeBudgetTableChecks
