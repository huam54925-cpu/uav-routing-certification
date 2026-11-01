# Finite tree-budget patterns, certificates, and complete reference search

This extension builds on the tree-budget matrix interfaces recorded at local
publication commit `e04db4c37376e65d252553e241f23f2d1b74453b`. It adds new modules
without changing those interfaces, root imports, frozen targets, the toolchain,
or dependency pins. The model charges service on every non-depot visit; it does
not include travel costs, time windows, or time-dependent weights.

## Finite pattern theorem

`TreeBudgetPatterns` normalizes each row's root coordinate to zero. Its
`BoundedRow R h` type is the dependent finite product

```text
(v : V) -> Fin (bound R h v + 1)
bound R h root = 0
bound R h v = h v                 when v != root
```

`Pattern R h s T` restricts this finite type to rows with root degree one,
ancestor-closed positive support, and cost at most T. `card_pattern_le` bounds
the number of patterns by the product of the coordinate ranges. This does not
require positive costs: zero and signed rational costs are supported.

`matrix_iff_pattern_rows` identifies feasible matrices with finite families of
patterns. `matrix_iff_pattern_counts` proves

```text
m = rootCount R h ->
  (MatrixFeasible R h m s T <-> PatternCountsFeasible R h s T)
```

The count predicate requires, at each non-root vertex v,
`sum_p z(p) * p(v) = h(v)`. `pattern_count_total` derives
`sum_p z(p) = rootCount R h`, and `pattern_count_le` bounds each count by this
total. Thus both the row space and the relevant count space are finite.

This theorem uses only root-degree compatibility for a supplied natural h.
Full integer `FlowCompatible` is needed when connecting h to prescribed
demands. Root normalization preserves cost, root degree, and ancestor closure.
Ancestor closure imposes positivity, not child multiplicity <= parent
multiplicity.

## Executable certificate verification

`TreeBudgetCertificate.Certificate V` contains a finite number of entries, a
natural row for each entry, and a natural multiplicity for each entry.
`checkCertificate` checks:

1. Every stored row is root-normalized, bounded by h, and structurally and
   financially valid as one route.
2. The sum of multiplicities equals m.
3. Weighted column sums equal h at every non-root vertex.

Repeated entries and zero multiplicities are allowed. Every stored row must
still be valid, including a row whose multiplicity is zero. Distinct rows are
not a required certificate invariant. The verifier sums multiplicities directly
and does not expand them into copies. `matrix_iff_exists_certificate` proves
that some accepted certificate exists exactly when the matrix is feasible.
`pattern_counts_iff_certificate` connects the count theorem to this interface.
Rejection of one supplied certificate does not prove global infeasibility.

## Complete reference search

`TreeBudgetFiniteSearch` works on vertices `Fin n`. `boundedVectors` recursively
enumerates all functions with the specified coordinate bounds; its membership
theorem proves both directions. `candidates` filters them by the executable
single-row predicate. `families` enumerates all ordered m-tuples of candidates,
and `searchRows` finds the first tuple with the exact non-root column sums.

`search` returns `Option Certificate`. `search_sound` proves that every returned
certificate passes the independent verifier. `search_correct` proves that a
certificate is returned exactly when the matrix is feasible, and
`search_none_iff` proves the meaning of exhaustive failure.

This implementation is a deliberately simple enumeration baseline. It is not
the proposed remaining-demand recursion, a memoized dynamic program, or an
efficient tree algorithm. If there are P valid patterns, it constructs up to
P^m ordered families, in addition to enumerating the bounded row space. Lists
are materialized; time and memory costs can therefore be very large. The
reference search emits m entries with multiplicity one, without automatically
merging duplicate rows. The certificate format independently supports compressed
counts, as exercised by the regression tests.

## From demands to actual route existence

`TreeBudgetChecker.requirementExec` computes the integer leaf recursion using
the supplied parent and rank functions and a computable children enumeration.
`requirementExec_eq` proves equality with the original abstract recursion.
`compatible` checks nonnegativity at non-root vertices and the integer root
degree equation before search is invoked. Negative requirements are not silently
accepted through natural-number truncation.

The public entry points are `solve`, which returns a certificate, and
`checkTreeBudget`, which returns its success flag. The main theorem is

```text
checkTreeBudget R d m s T = true <-> BudgetRoutes R d m s T
```

`solve_sound` also supplies flow compatibility and verifier acceptance;
`solve_none_iff` identifies exhaustive failure with nonexistence of legal
budgeted routes. These statements impose no sign condition on service fees or
the budget. In particular, an empty fleet with zero non-root demand is feasible
even for a negative budget. The depot's own demand and service fee are ignored.

The executable input is an explicitly supplied rooted tree on `Fin n`, with
computable data fields. A tree created by the older noncomputable
`RootedTree.ofIsTree` adapter is still valid mathematical input, but that adapter
is not made executable by this extension. The search returns edge-count
patterns, not ordered vertex-by-vertex routes. Existence of actual legal routes
is obtained through the previously proved matrix theorem; an executable route
sequence generator remains separate work.

## Regression and reproduction scope

`TreeBudgetCheckerExamples` includes a depot, a hub, and three satellites. It
checks rejection of two capacity-10 routes for three weight-6 visits and
acceptance of three routes. Hub demand is respectively 5 and 6; increasing the
fleet while holding hub demand at 5 is explicitly rejected.

Other kernel-checked regressions cover empty negative-budget fleets, positive
flow with no depot connection, negative integer requirements, missing ancestors,
signed-cost cancellation, exact budget equality, zero fees, compressed
multiplicities, wrong counts, wrong columns, and a nonzero certificate root
coordinate. Route existence and nonexistence are also derived from the public
checker theorem. `#eval` examples display execution and a returned certificate;
the regression proofs use `decide +kernel`, not `native_decide`.

From the project root, the targeted reproduction command is:

```powershell
lake build LeanCompletion.UAV.TreeBudgetCheckerExamples
```

On 2026-11-01 this command completed successfully with exit code 0 (8342 Lake
jobs). All five new modules were built, while existing dependencies and prior
regression modules reused local caches. All 16 named new regression theorems
compiled. The 29 axiom reports from the five new modules contain only `propext`,
`Classical.choice`, and `Quot.sound`; the successful final log contains no
`sorryAx`. The executable examples returned false for two routes, true for three
routes, and a three-row certificate allocating one satellite visit per row.
Non-fatal linter warnings remain, including an unnecessary decidable-equality
hypothesis on the generic counting lemma and pre-existing dependency warnings.

The six earlier tree-budget source modules were checked byte-for-byte against
the baseline publication worktree and remain unchanged. This validation used
the pinned Lean 4.30.0-rc2 toolchain in the original development project; it is
not a clean rebuild or a rebuild of the separate publication worktree. Earlier
failed development runs are not PASS evidence. These checks preceded
publication; publishing the batch does not constitute another verification run.

Raw development and verification output stays under the ignored
`verification/runs/tree-budget-patterns-20261101/` directory. Local cached builds
must not be described as independent clean rebuilds or publication-package
verification.

## Next stages

The reference semantics now provide a target for proving equivalence of a
remaining-demand search, witness compression, or memoization. Root-subtree
factorization is also a separate useful next theorem: each pattern has exactly
one positive root-child coordinate, so one route lies in one root subtree.
General subtree dynamic programming and its complexity are not delivered here.
