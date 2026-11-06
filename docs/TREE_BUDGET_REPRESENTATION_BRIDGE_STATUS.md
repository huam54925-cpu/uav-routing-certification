# Issue #21: first representation-bridge package

Date: 2026-11-06 (Asia/Tokyo). This package completes the bounded route/row interface task and its information-loss examples. The wider Issue #21 remains open. Plans and mathematical derivations are provided as English LaTeX source; this page records implementation and verification evidence.

## Delivered interfaces

[TreeBudgetRepresentationBridge.lean](../LeanCompletion/UAV/TreeBudgetRepresentationBridge.lean) contains 15 new theorems in `UAVProof.TreeBudgetRepresentationBridge`:

| Interface | Declarations |
| --- | --- |
| Normalized projection | `projectRow_root`, `edgeFlow_normalize`, `projectRow_of_flow`, `projectRow_flow`, `projectRow_sound` |
| Existential reconstruction and signed budget preservation | `exists_route_project_normalize`, `exists_route_project`, `rowValid_exists_route` |
| Signed tree-side existence and forward next conversion | `exact_iff_checked_certificate`, `exact_implies_next`, `matrix_implies_next`, `checked_certificate_implies_next` |
| Shared-domain next equivalences | `next_iff_exact`, `next_iff_matrix`, `next_iff_checked_certificate` |

The normalized projection is `normalize R (routeRow R r)`. Reconstruction preserves exact flow, visit counts, and every signed additive service function. The root-zero version recovers the original row; the unrestricted-root version recovers its normalization. These are existential contracts, not executable route reconstruction algorithms.

Only the reverse next interface assumes nonnegative service fees and a strictly positive budget. It derives absence of self-loops from the tree and the fleet equality from `HasDegrees`. No positive-fleet hypothesis is introduced. Existing matrix and pattern-certificate equivalences are reused rather than counted as newly proved foundations.

## Regression scope

[TreeBudgetRepresentationBridgeExamples.lean](../LeanCompletion/UAV/TreeBudgetRepresentationBridgeExamples.lean) contains 12 new theorem declarations. The pre-existing `TreeBudgetRepresentationExamples.lean` is unchanged.

- Two distinct, tree-supported routes have the same normalized row, visit counts, and cost for every signed service function.
- Two explicit two-route families have identical exact flow, visit demands, and total cost, but individual costs `(3,3)` and `(4,2)` at budget `3`.
- `aggregate_does_not_determine_witness_budget` restricts its quantifier to exact decompositions of that same fixed input. `good_instance_feasible` separately proves the input is feasible.
- Boundary theorems cover a nonzero ignored root coordinate, signed fees with budget `-3`, and an empty route family at arbitrary signed fees and budget. They do not introduce an empty individual `LegalRoute`.

## Actual local verification

Executed from the existing development project with the pinned Lean toolchain and dependencies:

```powershell
lake build LeanCompletion.UAV.TreeBudgetRepresentationBridge
lake build LeanCompletion.UAV.TreeBudgetRepresentationBridgeExamples
```

Both final commands exited 0. The main module was actually compiled in `core-build-2.log` (`8344 jobs`); the final example source was actually compiled in `examples-build-final2.log` (`8355 jobs`). Existing dependencies and the already-built main module were reused as applicable. This was not a fresh-environment or standalone publication-package rebuild.

All **27 new theorem declarations** have individually checked `#print axioms` output. Dependencies are subsets of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs in either final successful log. Neither new source contains `sorry`, `admit`, an added `axiom`, `unsafe`, or `native_decide`. Concrete finite checks use `decide +kernel`; the remaining claims use ordinary proofs and existing theorems.

The main module retains non-fatal unused-section-variable/unused-`Fintype` linter warnings on four small projection lemmas. The new examples module has no warnings; warnings replayed from older dependencies retain their existing status. Failed development builds, including the intermediate attempt to restrict the aggregate theorem's domain, are excluded from PASS. The final statement explicitly parenthesizes the budget equivalence after its exact-flow and visit-count premises.

Raw logs, hashes, and scratch output remain in ignored `verification/runs/issue21-bridge-20261106/`. SHA-256 comparison confirmed that all **112 pre-existing UAV Lean files** and the five protected root-import, toolchain, Lake configuration, dependency-lock, and verification-input files were unchanged.

## English mathematical sources

- [Representation contract](TREE_BUDGET_REPRESENTATION_CONTRACT.tex): revised from the user-supplied English manuscript, with a direction-specific assumption table and the actual first-package declaration map.
- [Allocation boundaries](TREE_BUDGET_ALLOCATION_BOUNDARIES.tex): paper proofs of the strict-hub/three-partition semantic correspondence for #23 and the fixed-exterior subtree gluing separation for #19.

At the initial package validation, both standalone sources used `article` and were intended for Overleaf with pdfLaTeX or XeLaTeX. Mathematical statements and source references were independently reviewed; environment/brace matching, labels, internal references, English text, and source paths were checked statically. No LaTeX compiler was run and no PDF was generated or visually verified as part of that validation. The subsequent review below is a separate event.

The #23 and #19 results remain paper proofs. They are not new Lean results, a formal complexity reduction, a strong NP-hardness classification, or a new internal-subtree algorithm. Full certificate round trips, executable reconstruction, and relaxation of the reverse next sign assumptions are outside this completed first package.

## Publication comparison

The publication worktree starts from `1bc992475a9bd515d77245e2bc0471e5ecab2fd5` on the existing `research/structural-service-cuts-20261023` branch of `huam54925-cpu/uav-routing-certification`. The six-file change contains the two new Lean modules, the revised English representation note, the new allocation note, this record, and README navigation. Raw output and build products are excluded.

The two Lean files and two LaTeX files match the reviewed development files byte for byte. Their Lean import closure contains 43 `LeanCompletion` modules including the two additions. All proof code matches the publication environment: 39 existing modules agree after line-ending/trailing-whitespace normalization, while `CopyProfileRealizability` and `FixedFlowObstruction` differ only in explicitly reviewed historical-status doc comments. The target toolchain, nine pinned dependencies, and Lean options agree with the validation environment. The target retains its direct Mathlib configuration; unused additional development dependencies are not copied.

Publication reuses the successful local checks recorded above. It does not add a fresh build, remote CI result, or LaTeX compilation. Frozen modules, dependency pins, earlier proof sources, and historical validation records are preserved; no issue is closed by this package.

## Subsequent PDF review and follow-up scope — 2026-11-06

After implementation commit [e576911](https://github.com/huam54925-cpu/uav-routing-certification/commit/e5769113868b75a38016a30c2f6a8a016a14060e), the user supplied a nine-page representation-contract PDF and a six-page allocation-boundaries PDF. Their page renders were inspected separately from the recorded Lean validation. The representation PDF clipped the signed equivalence chain in Proposition 3.2 on page 4; the current LaTeX source breaks that display across lines. The two sources now distinguish the original publication's lack of LaTeX compilation from this later PDF review. New bridge/example links are pinned to the implementation commit.

This documentation update does not change Lean files, rerun builds or axiom audits, compile LaTeX, or regenerate either supplied PDF. The corrected representation source has not yet been rendered; the supplied PDFs remain snapshots preceding this documentation revision.

The first #21 bridge package and the first #22 candidate-list package are complete within their stated scopes; both wider issues remain open. The next bounded proof task is #23's semantic correspondence: unit columns determine an assignment, total cost saturates every row budget, and each saturated group has three items, followed by composition with the existing hub-packing theorem. Polynomial encoding and complexity classifications remain later tasks. For #19, continue the paper specification with one matched boundary excursion per route before considering a general internal-subtree DP. No new Lean work for #23 or #19 is included here.
