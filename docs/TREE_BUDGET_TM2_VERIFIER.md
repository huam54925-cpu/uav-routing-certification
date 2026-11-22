# A4: standard TM2 verifier for sparse tree-budget certificates

For every instance string `x` and certificate string `y`, the verifier starts at
`pairWire (x, y)` and halts in the standard configuration with the singleton
output `[verify x y]`. All other stacks are empty and the finite control state
has been reset. The theorem includes malformed instances and certificates,
failed row and total checks, and failed weighted column checks.

| Stage | Lean entry |
| --- | --- |
| A3 public verifier and certificate semantics | [TreeBudgetSparseVerifier](../LeanCompletion/UAV/TreeBudgetSparseVerifier.lean) |
| One row, with exact return layout and a uniform transition bound | [`row_run_in_time`](../LeanCompletion/UAV/TreeBudgetRowCheckTime.lean) |
| All compressed records and total multiplicity | [`records_from_start_unconditional`](../LeanCompletion/UAV/TreeBudgetRowsCheckTotal.lean) |
| All nonroot weighted columns | [`check_run`](../LeanCompletion/UAV/TreeBudgetColumnCheckTotal.lean) |
| Refinement for every raw pair | [`executes`](../LeanCompletion/UAV/TreeBudgetVerifierTotal.lean) |
| Standard verifier and language theorem | [`verifier`, `tree_budget_inNP`](../LeanCompletion/UAV/TreeBudgetVerifierNP.lean) |

Each row is checked even if its multiplicity is zero. The row budget is
compared after summing the signed terms. The all-record loop sums
multiplicities in binary, and column checks multiply each stored count by the
corresponding row coordinate without expanding the records.

The polynomial in `TreeBudgetVerifierNP.inputPolynomial` adds the actual
parsed-and-scaled entrance, preparation, row/count and column bounds. Its
degree is seven. The standard output wrapper adds a linear expression in the
input length and this transition bound to pay for the final cleanup.

Reproduce the proof with `lake build LeanCompletion.UAV.TreeBudgetVerifierNP`.
The [actual machine regressions](../LeanCompletion/UAV/TreeBudgetVerifierExamples.lean)
have a separate target `LeanCompletion.UAV.TreeBudgetVerifierExamples`.
