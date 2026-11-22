import LeanCompletion.UAV.TreeBudgetRowCheckSpec

namespace UAVProof.A4RowsCheckSpec
open TreeBudgetSparseCodec TreeBudgetSparseVerifier TreeBudgetCertificate
open TreeBudgetCostedCandidates TreeBudgetVectorChecker

def rawRow (n : ℕ) (e : RawEntry) : Vector ℕ n :=
  Vector.ofFn fun v : Fin n => e.2[v.val]?.getD 0

theorem rawRow_ofFn {n : ℕ} (c : ℕ) (p : Fin n → ℕ) :
    rawRow n (c,List.ofFn p)=Vector.ofFn p := by
  ext v hv
  simp [rawRow,List.getElem?_eq_getElem,hv]

theorem countSum_toRaw {n : ℕ} (C : Certificate (Fin n)) :
    ((toRaw C).map Prod.fst).sum=(List.ofFn C.count).sum := by
  simp [toRaw,List.map_ofFn,Function.comp_def]

theorem rows_toRaw {n : ℕ} (C : Certificate (Fin n)) (f : Vector ℕ n → Bool) :
    (toRaw C).all (fun e => f (rawRow n e))=
      (List.finRange C.size).all (fun i => f (Vector.ofFn (C.row i))) := by
  simp only [toRaw,List.ofFn_eq_map,List.all_map,Function.comp_def]
  congr 1
  funext i
  rw [← List.ofFn_eq_map]
  rw [rawRow_ofFn]

def rowPredicate (I : Instance) (e : RawEntry) : Bool :=
  (rowCheck I.data.parents I.data.H
    (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator)
    (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator)
    (rawRow I.data.n e)).value

theorem rows_counts_public (I : Instance) (C : Certificate (Fin I.data.n)) :
    ((toRaw C).all (rowPredicate I) &&
      decide (((toRaw C).map Prod.fst).sum=I.routes))=
    ((List.finRange C.size).all (fun i =>
      (rowCheck I.data.parents I.data.H
        (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator)
        (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator)
        (Vector.ofFn (C.row i))).value) && decide ((List.ofFn C.count).sum=I.routes)) := by
  change ((toRaw C).all (fun e => (rowCheck I.data.parents I.data.H
    (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator)
    (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator)
    (rawRow I.data.n e)).value) && decide (((toRaw C).map Prod.fst).sum=I.routes)) = _
  rw [rows_toRaw C (fun p => (rowCheck I.data.parents I.data.H
    (scaleFees I.data.numerators I.data.denominators I.data.budgetDenominator)
    (scaleBudget I.data.denominators I.data.budgetNumerator I.data.budgetDenominator) p).value),
    countSum_toRaw]

end UAVProof.A4RowsCheckSpec
