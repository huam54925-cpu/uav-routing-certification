import LeanCompletion.UAV.TreeBudgetVerifierTotal

namespace UAVProof.A4Verifier
open TreeBudgetBinaryCodec TreeBudgetSparseVerifier TreeBudgetSparseNPBridge
open Turing
set_option synthInstance.maxSize 32768
set_option maxRecDepth 50000

noncomputable def inputPolynomial : Polynomial ℕ :=
  let X := (Polynomial.X : Polynomial ℕ)
  let B := Polynomial.C 4*(X+1)^2
  Polynomial.C 131072*(X+2)^4 +
    (Polynomial.C 5*(Polynomial.C 2*B)+Polynomial.C 13*(Polynomial.C 3*B+3)+19) +
    (X+1)*(Polynomial.C 8192*(B+X+1)^3+Polynomial.C 72*(X+1)^2) +
    Polynomial.C 16384*(Polynomial.C 2*X+1)^4+2

theorem inputPolynomial_eval (N : ℕ) : inputPolynomial.eval N=limit N := by
  simp [inputPolynomial,limit,A4FeeScaling.Entry.totalBound,prepBound,recordsBound,
    A4RowsCheck.rowTimeBound,columnsBound,fieldBound]

/-- A4: finite alphabet and exact standard Boolean output for every raw pair. -/
noncomputable def verifier : StandardVerifier verify :=
  TreeBudgetStandardOutputTM2.standardVerifier (K := K) (Λ := L)
    (Finset.univ : Finset K).toList
    (fun k => Finset.mem_toList.mpr (Finset.mem_univ k))
    machine.k₀ machine.main program verify inputPolynomial
    (by intro x y; rw [inputPolynomial_eval]; exact executes x y)

theorem tree_budget_inNP : InNP language :=
  language_inNP_of_standard_verifier verifier

end UAVProof.A4Verifier
