import LeanCompletion.UAV.TreeBudgetRowCheckSpec

namespace UAVProof.A4RowCheckModel
open TreeBudgetBinaryCodec TreeBudgetWeightedTM2

structure Node where
  parent : ℕ
  cap : ℕ
  coord : ℕ
  plus : ℕ
  minus : ℕ
  deriving DecidableEq

abbrev WordState := Bits × Bits × Bits

def nodePass (rows : List ℕ) (root : ℕ) (v : Node) : Bool :=
  decide (v.coord≤v.cap) &&
    decide (v.parent≠root ∧ 0<v.coord → 0<(rows[v.parent]?.getD 0))

def nodeStep (Ap An : List ℕ) (root : ℕ) (v : Node) (q : WordState) : WordState :=
  let pos := weighted v.coord.bits v.plus.bits q.1
  let neg := weighted v.coord.bits v.minus.bits q.2.1
  if v.parent=root then (pos,neg,weighted v.coord.bits [true] q.2.2)
  else if v.coord=0 then (pos,neg,q.2.2)
  else (weighted v.coord.bits (Ap[v.parent]?.getD 0).bits pos,
    weighted v.coord.bits (An[v.parent]?.getD 0).bits neg,q.2.2)

def loopResult (rows Ap An : List ℕ) (root : ℕ) : List Node → WordState → Bool
  | [],q => decide (value q.2.2=1 ∧ value q.1≤value q.2.1)
  | v::vs,q => nodePass rows root v && loopResult rows Ap An root vs (nodeStep Ap An root v q)

def nodes {n : ℕ} (P : TreeBudgetParentArray.ParentArray n) (H Ap An p : Vector ℕ n) : List Node :=
  List.ofFn fun v : Fin n => ⟨(P.parents[v]).val,H[v],p[v],Ap[v],An[v]⟩

def rowResult {n : ℕ} (P : TreeBudgetParentArray.ParentArray n) (H Ap An p : Vector ℕ n)
    (budget : ℤ) : Bool :=
  decide (p[P.root]=0) && loopResult p.toList Ap.toList An.toList P.root.val
    (nodes P H Ap An p) ((-budget).toNat.bits,budget.toNat.bits,[])

end UAVProof.A4RowCheckModel
