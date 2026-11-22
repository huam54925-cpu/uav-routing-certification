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

## Package A acceptance

The semantic checks landed in `e19e78d`. The standard verifier and the NP
theorem landed in `e76a304`, the proof revision used for the November 22, 2026
acceptance. The toolchain is Lean `4.30.0-rc2` with mathlib pinned to
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

| Local check | Recorded result |
| --- | --- |
| `lake build LeanCompletion.UAV.TreeBudgetVerifierNP` | Exit 0. Lake reported 8,528 jobs, including cached jobs. |
| `lake build LeanCompletion.UAV.TreeBudgetVerifierExamples` | Exit 0. The target contains six actual machine regressions. The successful run reported 8,485 jobs, including cached jobs. |
| `python tools/check_sparse_patterns.py` | Exit 0. 3,220 instances, 44,020 rows, 2,739 midpoint pairs, 1,633 feasible instances and one multiplicity exchange. The distinct-minimizers example also passed. |
| `lake env lean verification/AuditTreeBudgetVerifier.lean` | Six core declarations audited, including `tree_budget_inNP`. The only dependencies reported were `propext`, `Classical.choice`, and `Quot.sound`. |

The audit covers the transitive axiom dependencies of the six printed
declarations. These are targeted local checks using the pinned workspace.
This record does not include a full repository cold build or remote CI.

| #24 validation item | Evidence |
| --- | --- |
| Small trees and caps against the old mode predicate | [Independent enumeration](../tools/check_sparse_patterns.py) |
| Root coordinate, child count above parent count, zero parent capacity with positive descendants, signed fees or budget, and route-count mismatch | [Row machine examples](../LeanCompletion/UAV/TreeBudgetRowCheckExamples.lean), [mode and midpoint examples](../LeanCompletion/UAV/TreeBudgetSparseExamples.lean), and [wire examples](../LeanCompletion/UAV/TreeBudgetSparseWireExamples.lean) |
| Same-parity midpoints and multiplicity exchange | `signed_midpoint_valid` and `signed_midpoint_compression_accept` in the mode examples, and the exchange check in the enumeration script |
| Large counts in compressed form | `binary_large_count_accept` in the wire examples uses a count of `2^80`. The [record loop](../LeanCompletion/UAV/TreeBudgetRowsCheckTotal.lean) and [column loop](../LeanCompletion/UAV/TreeBudgetColumnCheckTotal.lean) operate on compressed records. |
| Targeted builds and axiom audit | Commands and recorded outcomes above. [Audit source](../verification/AuditTreeBudgetVerifier.lean) |

A0–A4 establish the short witness and the standard verifier for the general
binary language. They give the NP membership direction. Any strong
NP-completeness claim also needs the reduction into this same language.
