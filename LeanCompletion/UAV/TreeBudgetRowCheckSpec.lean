import LeanCompletion.UAV.TreeBudgetWeightedWidth
import LeanCompletion.UAV.TreeBudgetCostedCandidates
import LeanCompletion.UAV.TreeBudgetSignedWordTM2
import LeanCompletion.UAV.TreeBudgetSparseVerifier

/-! Signed row costs are accumulated in two natural words. The budget is
compared only after the complete row; multiplicity is not a row-cost factor. -/
namespace UAVProof.A4RowCheckSpec
open TreeBudgetBinaryCodec TreeBudgetWeightedTM2 TreeBudgetParentArray
open TreeBudgetCostedCandidates TreeBudgetVectorChecker
open TreeBudgetBitPrimitives
set_option maxHeartbeats 4000000

abbrev Term := ℕ × ℤ
def termValue (e : Term) : ℤ := (e.1:ℤ)*e.2
def termSum (es : List Term) : ℤ := (es.map termValue).sum

def wordStep (e : Term) (pos neg : Bits) : Bits × Bits :=
  if e.2<0 then (pos,weighted e.1.bits e.2.natAbs.bits neg)
  else (weighted e.1.bits e.2.natAbs.bits pos,neg)

def wordFold : List Term → Bits → Bits → Bits × Bits
  | [],pos,neg => (pos,neg)
  | e::es,pos,neg =>
      let next := wordStep e pos neg
      wordFold es next.1 next.2

def balance (s : Bits × Bits) : ℤ := (value s.1:ℤ)-(value s.2:ℤ)

theorem wordStep_balance (e : Term) (pos neg : Bits) :
    balance (wordStep e pos neg)=balance (pos,neg)+termValue e := by
  obtain ⟨c,a⟩ := e
  cases a with
  | ofNat a =>
    have hn : ¬ (a:ℤ)<0 := by omega
    simp [wordStep,balance,weighted_value,termValue,hn]
    ring
  | negSucc a =>
    simp [wordStep,balance,weighted_value,termValue]
    rw [Int.negSucc_eq]
    ring

theorem wordFold_balance (es : List Term) (pos neg : Bits) :
    balance (wordFold es pos neg)=balance (pos,neg)+termSum es := by
  induction es generalizing pos neg with
  | nil => simp [wordFold,termSum]
  | cons e es ih =>
    simp only [wordFold]
    rw [ih,wordStep_balance]
    simp only [termSum,List.map_cons,List.sum_cons]
    ring

theorem wordFold_append (xs ys : List Term) (pos neg : Bits) :
    wordFold (xs++ys) pos neg=
      wordFold ys (wordFold xs pos neg).1 (wordFold xs pos neg).2 := by
  induction xs generalizing pos neg <;> simp_all [wordFold]

def initial (budget : ℤ) : Bits × Bits := ((-budget).toNat.bits,budget.toNat.bits)

theorem initial_balance (budget : ℤ) : balance (initial budget) = -budget := by
  cases budget <;> simp [initial,balance]

theorem wordFold_budget (es : List Term) (budget : ℤ) :
    value (wordFold es (initial budget).1 (initial budget).2).1 ≤
      value (wordFold es (initial budget).1 (initial budget).2).2 ↔ termSum es ≤ budget := by
  have h := wordFold_balance es (initial budget).1 (initial budget).2
  rw [show ((initial budget).1,(initial budget).2)=initial budget from Prod.eta _,
    initial_balance] at h
  unfold balance at h
  omega

def vertexTerms {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (p : Vector ℕ n) (v : Fin n) : List Term :=
  if v=P.root then [] else
    [(p[v],A[v]),(p[v],if P.parents[v]=P.root then 0 else A[P.parents[v]])]

def rowTerms {n : ℕ} (P : ParentArray n) (A : Vector ℤ n) (p : Vector ℕ n) : List Term :=
  (List.ofFn fun v : Fin n => v).flatMap (vertexTerms P A p)

theorem termSum_flatMap {α : Type} (xs : List α) (f : α → List Term) :
    termSum (xs.flatMap f)=(xs.map fun x => termSum (f x)).sum := by
  induction xs <;> simp_all [termSum,List.map_append,List.sum_append]

theorem vertexTerms_sum {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (p : Vector ℕ n) (v : Fin n) :
    termSum (vertexTerms P A p v)=(costTerm P A p v).value := by
  by_cases h : v=P.root
  · simp [vertexTerms,h,termSum]
  · simp only [vertexTerms,if_neg h,termSum,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,termValue,costTerm_value,if_neg h]
    split_ifs <;> ring

theorem rowTerms_sum {n : ℕ} (P : ParentArray n) (A : Vector ℤ n) (p : Vector ℕ n) :
    termSum (rowTerms P A p)=(rowCost P A p).value := by
  simp [rowTerms,termSum_flatMap,vertexTerms_sum,rowCost,List.map_ofFn,Function.comp_def]

/-- This final comparison is equivalent even when earlier prefixes exceed
the budget, or when the budget and some vertex fees are negative. -/
theorem row_budget_iff {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (budget : ℤ) (p : Vector ℕ n) :
    value (wordFold (rowTerms P A p) (initial budget).1 (initial budget).2).1 ≤
      value (wordFold (rowTerms P A p) (initial budget).1 (initial budget).2).2 ↔
      (rowCost P A p).value ≤ budget := by
  rw [wordFold_budget,rowTerms_sum]

def structural {n : ℕ} (P : ParentArray n) (H p : Vector ℕ n) : Bool :=
  decide (p[P.root]=0) &&
  ((List.ofFn fun v : Fin n => (nodeCheck P H p v).value).all id) &&
  decide ((rootCountCost P p).value=1)

def accepted {n : ℕ} (P : ParentArray n) (H : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) (p : Vector ℕ n) : Bool :=
  structural P H p &&
    decide (value (wordFold (rowTerms P A p) (initial budget).1 (initial budget).2).1 ≤
      value (wordFold (rowTerms P A p) (initial budget).1 (initial budget).2).2)

theorem accepted_eq_rowCheck {n : ℕ} (P : ParentArray n) (H : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) (p : Vector ℕ n) :
    accepted P H A budget p=(rowCheck P H A budget p).value := by
  simp [accepted,structural,rowCheck,row_budget_iff,List.map_ofFn,Function.comp_def]

/-- Root mass is linear in compressed record multiplicities. No distinctness
or positivity of multiplicities is assumed. -/
theorem root_mass_exchange {n k : ℕ} (P : ParentArray n)
    (c : Fin k → ℕ) (p : Fin k → Vector ℕ n) :
    (∑ i, c i*(rootCountCost P (p i)).value)=
      ∑ v : Fin n, if v≠P.root ∧ P.parents[v]=P.root then
        ∑ i, c i*(p i)[v] else 0 := by
  simp only [rootCountCost,collect_value,List.map_ofFn,sumNatCost_value,Function.comp_def,
    rootTerm_value,List.sum_ofFn]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : v≠P.root ∧ P.parents[v]=P.root <;> simp [h]

theorem total_count_of_columns {n k : ℕ} (P : ParentArray n) (H : Vector ℕ n)
    (m : ℕ) (c : Fin k → ℕ) (p : Fin k → Vector ℕ n)
    (hm : (rootCountCost P H).value=m)
    (hr : ∀ i, (rootCountCost P (p i)).value=1)
    (hc : ∀ v, v≠P.root → (∑ i, c i*(p i)[v])=H[v]) :
    (∑ i, c i)=m := by
  have h := root_mass_exchange P c p
  simp only [hr,Nat.mul_one] at h
  rw [← hm,h]
  simp only [rootCountCost,collect_value,List.map_ofFn,sumNatCost_value,Function.comp_def,
    rootTerm_value,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v≠P.root ∧ P.parents[v]=P.root
  · simp only [if_pos hv]
    exact hc v hv.1
  · simp only [if_neg hv]


/-- The implementation can scan every coordinate after the root-zero test:
no separate vertex-index counter is needed. -/
def nodeAll {n : ℕ} (P : ParentArray n) (H p : Vector ℕ n) (v : Fin n) : Bool :=
  decide (p[v]≤H[v]) &&
    decide (0<p[v] → P.parents[v]≠P.root → 0<p[P.parents[v]])

def rootSumAll {n : ℕ} (P : ParentArray n) (p : Vector ℕ n) : ℕ :=
  ∑ v : Fin n, if P.parents[v]=P.root then p[v] else 0

def allVertexTerms {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (p : Vector ℕ n) (v : Fin n) : List Term :=
  [(p[v],A[v]),(p[v],if P.parents[v]=P.root then 0 else A[P.parents[v]])]

def allTerms {n : ℕ} (P : ParentArray n) (A : Vector ℤ n) (p : Vector ℕ n) : List Term :=
  (List.ofFn fun v : Fin n => v).flatMap (allVertexTerms P A p)

theorem nodeAll_eq {n : ℕ} (P : ParentArray n) (H p : Vector ℕ n)
    (hr : p[P.root]=0) (v : Fin n) :
    nodeAll P H p v=(nodeCheck P H p v).value := by
  by_cases hv : v=P.root
  · subst v; simp [nodeAll,hr]
  · simp [nodeAll,nodeCheck_value,hv]

theorem rootSumAll_eq {n : ℕ} (P : ParentArray n) (p : Vector ℕ n)
    (hr : p[P.root]=0) : rootSumAll P p=(rootCountCost P p).value := by
  simp only [rootSumAll,rootCountCost,collect_value,List.map_ofFn,sumNatCost_value,
    Function.comp_def,rootTerm_value,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v=P.root
  · subst v; simp [hr]
  · simp [hv]

theorem allVertexTerms_sum {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (p : Vector ℕ n) (hr : p[P.root]=0) (v : Fin n) :
    termSum (allVertexTerms P A p v)=(costTerm P A p v).value := by
  by_cases hv : v=P.root
  · subst v; simp [allVertexTerms,termSum,termValue,hr]
  · simp only [allVertexTerms,termSum,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,termValue,costTerm_value,if_neg hv]
    split_ifs <;> ring

theorem allTerms_sum {n : ℕ} (P : ParentArray n) (A : Vector ℤ n)
    (p : Vector ℕ n) (hr : p[P.root]=0) :
    termSum (allTerms P A p)=(rowCost P A p).value := by
  simp [allTerms,termSum_flatMap,allVertexTerms_sum P A p hr,rowCost,List.map_ofFn,Function.comp_def]

def allAccepted {n : ℕ} (P : ParentArray n) (H : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) (p : Vector ℕ n) : Bool :=
  decide (p[P.root]=0) &&
    ((List.ofFn fun v : Fin n => nodeAll P H p v).all id) &&
    decide (rootSumAll P p=1) &&
    decide (value (wordFold (allTerms P A p) (initial budget).1 (initial budget).2).1 ≤
      value (wordFold (allTerms P A p) (initial budget).1 (initial budget).2).2)

theorem allAccepted_eq_rowCheck {n : ℕ} (P : ParentArray n) (H : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) (p : Vector ℕ n) :
    allAccepted P H A budget p=(rowCheck P H A budget p).value := by
  by_cases hr : p[P.root]=0
  · simp [allAccepted,wordFold_budget,allTerms_sum P A p hr,nodeAll_eq P H p hr,
      rootSumAll_eq P p hr,rowCheck,hr,List.map_ofFn,Function.comp_def]
  · have hn : p[(P.root : ℕ)]≠0 := hr
    simp [allAccepted,rowCheck,hn]


/-- Two natural coefficient tables allow every update to use the same
unsigned multiply-add routine, including a zero coefficient. -/
abbrev NatTerm := ℕ × ℕ × ℕ

def natTermValue (e : NatTerm) : ℤ := (e.1:ℤ)*((e.2.1:ℤ)-(e.2.2:ℤ))
def natTermSum (es : List NatTerm) : ℤ := (es.map natTermValue).sum

def natStep (e : NatTerm) (pos neg : Bits) : Bits × Bits :=
  (weighted e.1.bits e.2.1.bits pos,weighted e.1.bits e.2.2.bits neg)

def natFold : List NatTerm → Bits → Bits → Bits × Bits
  | [],pos,neg => (pos,neg)
  | e::es,pos,neg =>
      let next := natStep e pos neg
      natFold es next.1 next.2

theorem natStep_balance (e : NatTerm) (pos neg : Bits) :
    balance (natStep e pos neg)=balance (pos,neg)+natTermValue e := by
  simp [natStep,balance,weighted_value,natTermValue]
  ring

theorem natFold_balance (es : List NatTerm) (pos neg : Bits) :
    balance (natFold es pos neg)=balance (pos,neg)+natTermSum es := by
  induction es generalizing pos neg with
  | nil => simp [natFold,natTermSum]
  | cons e es ih =>
    simp only [natFold]
    rw [ih,natStep_balance]
    simp only [natTermSum,List.map_cons,List.sum_cons]
    ring

theorem natFold_append (xs ys : List NatTerm) (pos neg : Bits) :
    natFold (xs++ys) pos neg=
      natFold ys (natFold xs pos neg).1 (natFold xs pos neg).2 := by
  induction xs generalizing pos neg <;> simp_all [natFold]

theorem natFold_budget (es : List NatTerm) (budget : ℤ) :
    value (natFold es (initial budget).1 (initial budget).2).1 ≤
      value (natFold es (initial budget).1 (initial budget).2).2 ↔
      natTermSum es ≤ budget := by
  have h := natFold_balance es (initial budget).1 (initial budget).2
  rw [show ((initial budget).1,(initial budget).2)=initial budget from Prod.eta _,
    initial_balance] at h
  unfold balance at h
  omega

def tableVertexTerms {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n)
    (v : Fin n) : List NatTerm :=
  [(p[v],Ap[v],An[v]),(p[v],if P.parents[v]=P.root then 0 else Ap[P.parents[v]],
    if P.parents[v]=P.root then 0 else An[P.parents[v]])]

def tableTerms {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n) : List NatTerm :=
  (List.ofFn fun v : Fin n => v).flatMap (tableVertexTerms P Ap An p)

theorem natTermSum_flatMap {α : Type} (xs : List α) (f : α → List NatTerm) :
    natTermSum (xs.flatMap f)=(xs.map fun x => natTermSum (f x)).sum := by
  induction xs <;> simp_all [natTermSum,List.map_append,List.sum_append]

theorem tableVertexTerms_sum {n : ℕ} (P : ParentArray n) (Ap An : Vector ℕ n)
    (A : Vector ℤ n) (p : Vector ℕ n)
    (ha : ∀ v : Fin n, (Ap[v]:ℤ)-(An[v]:ℤ)=A[v]) (v : Fin n) :
    natTermSum (tableVertexTerms P Ap An p v)=termSum (allVertexTerms P A p v) := by
  simp only [tableVertexTerms,allVertexTerms,natTermSum,termSum,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,natTermValue,termValue]
  split_ifs <;> simp only [Int.natCast_zero,sub_zero,mul_zero,add_zero,ha]

theorem tableTerms_sum {n : ℕ} (P : ParentArray n) (Ap An : Vector ℕ n)
    (A : Vector ℤ n) (p : Vector ℕ n)
    (ha : ∀ v : Fin n, (Ap[v]:ℤ)-(An[v]:ℤ)=A[v]) (hr : p[P.root]=0) :
    natTermSum (tableTerms P Ap An p)=(rowCost P A p).value := by
  rw [← allTerms_sum P A p hr]
  simp only [tableTerms,allTerms,natTermSum_flatMap,termSum_flatMap,
    tableVertexTerms_sum P Ap An A p ha]

def tableAccepted {n : ℕ} (P : ParentArray n) (H Ap An : Vector ℕ n)
    (budget : ℤ) (p : Vector ℕ n) : Bool :=
  decide (p[P.root]=0) &&
    ((List.ofFn fun v : Fin n => nodeAll P H p v).all id) &&
    decide (rootSumAll P p=1) &&
    decide (value (natFold (tableTerms P Ap An p) (initial budget).1 (initial budget).2).1 ≤
      value (natFold (tableTerms P Ap An p) (initial budget).1 (initial budget).2).2)

theorem tableAccepted_eq_rowCheck {n : ℕ} (P : ParentArray n) (H Ap An : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) (p : Vector ℕ n)
    (ha : ∀ v : Fin n, (Ap[v]:ℤ)-(An[v]:ℤ)=A[v]) :
    tableAccepted P H Ap An budget p=(rowCheck P H A budget p).value := by
  by_cases hr : p[P.root]=0
  · simp [tableAccepted,natFold_budget,tableTerms_sum P Ap An A p ha hr,
      nodeAll_eq P H p hr,rootSumAll_eq P p hr,rowCheck,hr,List.map_ofFn,Function.comp_def]
  · have hn : p[(P.root : ℕ)]≠0 := hr
    simp [tableAccepted,rowCheck,hn]

/-- The three machine phases retain the public checker's order and check
every record even when its multiplicity is zero. -/
def tableCheck (I : TreeBudgetSparseVerifier.Instance)
    (C : TreeBudgetCertificate.Certificate (Fin I.data.n))
    (Ap An : Vector ℕ I.data.n) : Bool :=
  (List.finRange C.size).all (fun i =>
    tableAccepted I.data.parents I.data.H Ap An
      (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator)
      (Vector.ofFn (C.row i))) &&
  decide ((List.ofFn C.count).sum=I.routes) &&
  (List.finRange I.data.n).all (fun v => decide (v≠I.data.parents.root →
    (List.ofFn (fun i => C.count i*C.row i v)).sum=I.data.H[v]))

theorem tableCheck_eq (I : TreeBudgetSparseVerifier.Instance)
    (C : TreeBudgetCertificate.Certificate (Fin I.data.n))
    (Ap An : Vector ℕ I.data.n)
    (ha : ∀ v : Fin I.data.n, (Ap[v]:ℤ)-(An[v]:ℤ)=
      (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator)[v]) :
    tableCheck I C Ap An=TreeBudgetSparseVerifier.check I C := by
  simp only [tableCheck,TreeBudgetSparseVerifier.check,tableAccepted_eq_rowCheck _ _ _ _ _ _ _ ha]

/-- Physical row control omits the parent calls when their contribution is
zero, while always performing both calls for the vertex's own coefficient. -/
def machineVertexTerms {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n)
    (v : Fin n) : List NatTerm :=
  [(p[v],Ap[v],An[v])] ++
    if P.parents[v]≠P.root ∧ 0<p[v] then
      [(p[v],Ap[P.parents[v]],An[P.parents[v]])] else []

def machineTerms {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n) : List NatTerm :=
  (List.ofFn fun v : Fin n => v).flatMap (machineVertexTerms P Ap An p)

theorem machineVertexTerms_sum {n : ℕ} (P : ParentArray n) (Ap An p : Vector ℕ n)
    (v : Fin n) : natTermSum (machineVertexTerms P Ap An p v)=
      natTermSum (tableVertexTerms P Ap An p v) := by
  by_cases hp : P.parents[v]=P.root
  · simp only [machineVertexTerms,tableVertexTerms,hp,ne_eq,not_true_eq_false,
      false_and,if_false,if_true,List.append_nil,natTermSum,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,natTermValue,Int.natCast_zero,sub_zero,mul_zero,add_zero]
  · by_cases hz : p[v]=0
    · simp only [machineVertexTerms,tableVertexTerms,hz,lt_self_iff_false,and_false,
        if_false,List.append_nil,natTermSum,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,natTermValue,Int.natCast_zero,zero_mul,add_zero]
    · have hpos : 0<p[v] := Nat.pos_of_ne_zero hz
      simp only [machineVertexTerms,tableVertexTerms,hp,if_false,ne_eq,not_false_eq_true,
        hpos,and_self,if_true,List.cons_append,List.nil_append]

theorem machineTerms_sum {n : ℕ} (P : ParentArray n) (Ap An : Vector ℕ n)
    (A : Vector ℤ n) (p : Vector ℕ n)
    (ha : ∀ v : Fin n, (Ap[v]:ℤ)-(An[v]:ℤ)=A[v]) (hr : p[P.root]=0) :
    natTermSum (machineTerms P Ap An p)=(rowCost P A p).value := by
  rw [← tableTerms_sum P Ap An A p ha hr]
  simp only [machineTerms,tableTerms,natTermSum_flatMap,machineVertexTerms_sum]

def machineAccepted {n : ℕ} (P : ParentArray n) (H Ap An : Vector ℕ n)
    (budget : ℤ) (p : Vector ℕ n) : Bool :=
  decide (p[P.root]=0) &&
    ((List.ofFn fun v : Fin n => nodeAll P H p v).all id) &&
    decide (rootSumAll P p=1) &&
    decide (value (natFold (machineTerms P Ap An p) (initial budget).1 (initial budget).2).1 ≤
      value (natFold (machineTerms P Ap An p) (initial budget).1 (initial budget).2).2)

theorem machineAccepted_eq_rowCheck {n : ℕ} (P : ParentArray n) (H Ap An : Vector ℕ n)
    (A : Vector ℤ n) (budget : ℤ) (p : Vector ℕ n)
    (ha : ∀ v : Fin n, (Ap[v]:ℤ)-(An[v]:ℤ)=A[v]) :
    machineAccepted P H Ap An budget p=(rowCheck P H A budget p).value := by
  by_cases hr : p[P.root]=0
  · simp [machineAccepted,natFold_budget,machineTerms_sum P Ap An A p ha hr,
      nodeAll_eq P H p hr,rootSumAll_eq P p hr,rowCheck,hr,List.map_ofFn,Function.comp_def]
  · have hn : p[(P.root : ℕ)]≠0 := hr
    simp [machineAccepted,rowCheck,hn]

end UAVProof.A4RowCheckSpec
