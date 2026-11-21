import LeanCompletion.UAV.TreeBudgetRowCheckModel

namespace UAVProof.A4RowCheckModel
open TreeBudgetBinaryCodec TreeBudgetWeightedTM2 TreeBudgetParentArray TreeBudgetCostedCandidates
open A4RowCheckSpec
set_option maxHeartbeats 4000000

def stateBalance (q : WordState) : ℤ := (value q.1:ℤ)-(value q.2.1:ℤ)
def nodeMass (root : ℕ) (v : Node) : ℕ := if v.parent=root then v.coord else 0
def nodeCost (Ap An : List ℕ) (root : ℕ) (v : Node) : ℤ :=
  (v.coord:ℤ)*((v.plus:ℤ)-(v.minus:ℤ)+
    if v.parent=root then 0 else ((Ap[v.parent]?.getD 0:ℕ):ℤ)-((An[v.parent]?.getD 0:ℕ):ℤ))
def massSum (root : ℕ) (vs : List Node) : ℕ := (vs.map (nodeMass root)).sum
def costSum (Ap An : List ℕ) (root : ℕ) (vs : List Node) : ℤ :=
  (vs.map (nodeCost Ap An root)).sum

theorem nodeStep_balance (Ap An : List ℕ) (root : ℕ) (v : Node) (q : WordState) :
    stateBalance (nodeStep Ap An root v q)=stateBalance q+nodeCost Ap An root v := by
  by_cases hp : v.parent=root
  · simp [nodeStep,hp,stateBalance,nodeCost,weighted_value]
    ring
  · by_cases hz : v.coord=0
    · simp [nodeStep,hp,hz,stateBalance,nodeCost,weighted_value]
    · simp [nodeStep,hp,hz,stateBalance,nodeCost,weighted_value]
      ring

theorem nodeStep_mass (Ap An : List ℕ) (root : ℕ) (v : Node) (q : WordState) :
    value (nodeStep Ap An root v q).2.2=value q.2.2+nodeMass root v := by
  by_cases hp : v.parent=root
  · simp [nodeStep,hp,nodeMass,weighted_value,value]
  · by_cases hz : v.coord=0 <;> simp [nodeStep,hp,hz,nodeMass]

theorem loopResult_value (rows Ap An : List ℕ) (root : ℕ) (vs : List Node) (q : WordState) :
    loopResult rows Ap An root vs q=
      (vs.all (nodePass rows root) && decide (value q.2.2+massSum root vs=1) &&
        decide (stateBalance q+costSum Ap An root vs≤0)) := by
  induction vs generalizing q with
  | nil =>
    simp only [loopResult,List.all_nil,massSum,costSum,List.map_nil,List.sum_nil,
      Nat.add_zero,Int.add_zero,Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    unfold stateBalance
    omega
  | cons v vs ih =>
    rw [loopResult,ih,nodeStep_mass,nodeStep_balance]
    simp [massSum,costSum,Bool.and_assoc,Nat.add_assoc,Int.add_assoc]
    rfl

theorem toList_lookup {n : ℕ} (xs : Vector ℕ n) (v : Fin n) :
    xs.toList[v.val]?.getD 0=xs[v] := by
  simp [List.getElem?_eq_getElem,v.isLt]

def ofVertex {n : ℕ} (P : ParentArray n) (H Ap An p : Vector ℕ n) (v : Fin n) : Node :=
  ⟨(P.parents[v]).val,H[v],p[v],Ap[v],An[v]⟩

theorem vertex_pass {n : ℕ} (P : ParentArray n) (H Ap An p : Vector ℕ n) (v : Fin n) :
    nodePass p.toList P.root.val (ofVertex P H Ap An p v)=nodeAll P H p v := by
  simp only [nodePass,ofVertex,nodeAll,toList_lookup]
  congr 1
  apply Bool.decide_congr
  have he : (P.parents[v]).val=P.root.val ↔ P.parents[v]=P.root := Fin.val_inj
  tauto

theorem nodes_pass {n : ℕ} (P : ParentArray n) (H Ap An p : Vector ℕ n) :
    (nodes P H Ap An p).all (nodePass p.toList P.root.val)=
      (List.ofFn fun v : Fin n => nodeAll P H p v).all id := by
  have he : (nodes P H Ap An p).map (nodePass p.toList P.root.val)=
      List.ofFn (fun v : Fin n => nodeAll P H p v) := by
    simp only [nodes,List.map_ofFn,Function.comp_def]
    congr 1
    funext v
    exact vertex_pass P H Ap An p v
  rw [← he,List.all_map]
  rfl

theorem nodes_mass {n : ℕ} (P : ParentArray n) (H Ap An p : Vector ℕ n) :
    massSum P.root.val (nodes P H Ap An p)=rootSumAll P p := by
  simp [massSum,nodeMass,nodes,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    rootSumAll,Fin.val_inj]

theorem vertex_cost {n : ℕ} (P : ParentArray n) (H Ap An p : Vector ℕ n) (v : Fin n) :
    nodeCost Ap.toList An.toList P.root.val (ofVertex P H Ap An p v)=
      natTermSum (tableVertexTerms P Ap An p v) := by
  simp only [nodeCost,ofVertex,toList_lookup,Fin.val_inj,tableVertexTerms,natTermSum,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,natTermValue]
  split_ifs <;> ring

theorem nodes_cost {n : ℕ} (P : ParentArray n) (H Ap An : Vector ℕ n) (A : Vector ℤ n)
    (p : Vector ℕ n) (ha : ∀ v : Fin n, (Ap[v]:ℤ)-(An[v]:ℤ)=A[v]) (hr : p[P.root]=0) :
    costSum Ap.toList An.toList P.root.val (nodes P H Ap An p)=(rowCost P A p).value := by
  rw [← tableTerms_sum P Ap An A p ha hr]
  simp only [costSum,nodes,tableTerms,natTermSum_flatMap,List.map_ofFn,Function.comp_def]
  congr 2
  funext v
  exact vertex_cost P H Ap An p v

theorem rowResult_eq_rowCheck {n : ℕ} (P : ParentArray n) (H Ap An : Vector ℕ n)
    (A : Vector ℤ n) (p : Vector ℕ n) (budget : ℤ)
    (ha : ∀ v : Fin n, (Ap[v]:ℤ)-(An[v]:ℤ)=A[v]) :
    rowResult P H Ap An p budget=(rowCheck P H A budget p).value := by
  by_cases hr : p[P.root]=0
  · have hi : stateBalance ((-budget).toNat.bits,budget.toNat.bits,[])=-budget :=
      initial_balance budget
    have hbudget : -budget+(rowCost P A p).value≤0 ↔ (rowCost P A p).value≤budget := by omega
    simp [rowResult,loopResult_value,nodes_pass,nodes_mass,nodes_cost P H Ap An A p ha hr,
      hi,hbudget,rootSumAll_eq P p hr,nodeAll_eq P H p hr,rowCheck,hr,
      List.map_ofFn,Function.comp_def,Bool.and_assoc,value]
  · have hn : p[(P.root : ℕ)]≠0 := hr
    simp [rowResult,rowCheck,hn]

end UAVProof.A4RowCheckModel
