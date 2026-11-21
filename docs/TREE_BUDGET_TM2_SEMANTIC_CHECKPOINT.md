# TM2 semantic verifier checkpoint

This checkpoint follows the fee-scaling entry at `a9f346f`. Its 30 new Lean modules were compiled with the pinned toolchain in the existing Lake workspace.

- `A4NaturalLookup.lookup_run` proves exact canonical lookup, preserves the original table and index, and charges copying, lookup, and cleanup.
- `TreeBudgetSignedTableTM2.split_run` produces the two natural fee tables and restores the signed source. The single-row finite program uses numeric comparison and tests the signed budget at the end.
- The record traversal, column traversal, and combined verifier programs are present. The proved inner column loop processes compressed multiplicities directly. Seven kernel-checked column regressions exercise the actual machine.
- The output wrapper clears the caller stacks, resets the finite state, and writes a single Boolean. It can construct a standard verifier once given a polynomial execution theorem for the semantic pipeline.

The remaining A4 work includes the full single-row execution and transition bound, the complete record and column execution theorems, and refinement of the combined machine to the public verifier. Issue #24 tracks this work. The historical proof target remains a separate build.

The source files can be checked with `lake build` followed by the desired module target, for example `lake build LeanCompletion.UAV.TreeBudgetColumnCheckExamples`. This checkpoint records targeted compilation in the current workspace.
