# Shared addressed search: packages A–C

This extension uses the existing pinned Lean environment and preserves the old
search/store modules. It introduces a separate shared-answer store and an
addressed executor for the search phase. The complete input/output and resource proofs are described in
[TREE_BUDGET_STORED_EXECUTION_STATUS.md](TREE_BUDGET_STORED_EXECUTION_STATUS.md).

## A: shared answers

`LeanCompletion/UAV/TreeBudgetSharedAnswerStore.lean` defines:

| Object | Slots |
| --- | --- |
| Empty row chain | `[bit false]` |
| Nonempty row chain | `[bit true, ref row, ref tail]` |
| Failed answer | `[bit false]` |
| Successful answer | `[bit true, ref rows]` |

`RowsRep` and `SharedAnswerRep` persist under `Extends`.
`prependRows_correct`, `prependRows_shares`, and `prependRows_size` prove that
prepending borrows both existing objects and adds exactly three slots. Including
the success wrapper adds exactly five slots (`prepend_success_size`), independent
of tail length. `failure_ne_success` also covers the successful empty matrix.
`nodeD_value` connects actual addressed writes to append-only allocation; its
fixed-width interface retains an explicit local capacity contract.

## B: charged ordered caches

`LeanCompletion/UAV/TreeBudgetChargedCache.lean` uses `readCellD`, `readWordD`,
`allocateSlotsD`, digit arithmetic, and the costed codecs. Address widths are
measured by `widthNat`; the measured address selects the actual slot. `load`,
`lengthRead`, `blobRead`, `keyRead`, and `headRead` have value/correctness proofs.

The executable lookup and filter take heap addresses, not decoded cache lists.
`lookupD_correct` preserves first-match lookup and the exact comparison count.
The outer option denotes a storage error, the next option a miss versus a hit;
the hit is an answer reference, including a reference to a failed answer.

`filterD_correct` proves stable removal of **all** matching keys, well-formedness,
heap extension, and exact heap growth of four slots per retained entry. It reuses
the existing empty-cache node and the retained key/answer payloads. The insertion
theorem adds one four-slot head and preserves the exact scan count. These
theorems allow arbitrary represented ordered caches, including duplicate and
conflicting keys. They assume neither reachability nor key uniqueness.

`Costed.allocations` includes auxiliary workspace as well as heap writes. It is
not equated with the heap-size difference. The filter/insert size equalities
refer to the actual heaps; they do not reuse the old abstract factor-eight bound.

## C: stored search

`LeanCompletion/UAV/TreeBudgetStoredSearch.lean` defines `memoD` and `scanD`.
Persistent vectors and keys are blobs; candidates and answers use shared row
chains. Scan continuations occupy five heap slots and memo continuations three.
The executor reloads the continuation after a child returns. A failed child feeds
its updated cache to the remaining candidates; a successful child prepends a
shared row and stops scanning. Depth tests and decrements call binary primitives.

The central contract is `memoD_correct`: from represented candidates, a residual
vector, an arbitrary ordered cache and a valid parent reference, the evaluator
returns without a storage error and simultaneously preserves:

- the answer of `memoStatV`;
- the full ordered cache of `memoStatV`;
- all six event counters;
- `WellFormed` and `Extends`.

`memoD_refines_cost` connects this result and the counters to `memoCost` for any
existing backend satisfying its value contracts. It does **not** identify their
work/allocation fields. `memoD_preserves` additionally retains the represented
caller frames, original candidates and original residual vector. Frame
constructors and frame persistence have separate proofs.

## Model and remaining work

Heap cells are the existing typed append-only random-access reference model.
Variable-sized parsing, encoding and arithmetic buffers use the existing
`Costed` auxiliary-workspace semantics; filtering explicitly charges its
continuation workspace. Traversal fuel uses a charged binary control cursor; initialization, zero tests
and decrements are included in the actual costs. Six event
counts are observations, not runtime output fields. This is not a theorem about
compiled Lean runtime or a sequential-tape machine.

D now connects the actual input bits, preprocessing, candidate construction and
charged final output to this executor. E analyzes the new executor's own
allocations, address widths and total work. See the [A–E record](TREE_BUDGET_STORED_EXECUTION_STATUS.md)
for the exported theorems and their cost-model scope. The A–C refinement alone
does not transfer a runtime bound from the old abstract search.

## Verification

`TreeBudgetStoredSearchExamples.lean` contains executable comparisons against
`memoStatV`, checking the answer, full ordered cache and all counters. Cases
include duplicate conflicting keys, cached failure, cached successful empty
answers, failed-child cache propagation, early success, rejected guards, stable
replacement, and addresses crossing 8, 16 and 32.

`verification/AuditTreeBudgetStoredExecution.lean` provides `#print axioms` inputs for the main
contracts. Raw compilation/audit output belongs only in
`verification/runs/shared-search-abc/`.

Run from the repository root with the existing dependencies available:

```powershell
lake build LeanCompletion.UAV.TreeBudgetStoredSearchExamples
lake env lean verification/AuditTreeBudgetStoredExecution.lean
```

This work uses the existing dependency/build caches; it is not a clean-clone
replay. No historical PASS result is being relabeled as a current check.

A–C initial local check on 2026-11-08 (before the D/E follow-up) completed using
Lean 4.30.0-rc2 and the repository's Lake options. All 11 executable regressions
passed. The 26 audited contracts depend only on subsets of `propext`,
`Classical.choice` and `Quot.sound`; none reports `sorryAx` or an additional
axiom. Lake still emits style/flexible-tactic and `#guard` linter warnings; this
is a successful compilation and proof audit, not a warning-free lint result.
