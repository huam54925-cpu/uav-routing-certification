# Tree service budgets: edge-count matrices and splitting normalization

This batch follows `674120ef954dbddef40acbf315f8b461e2b24fe0` on
`research/structural-service-cuts-20261023`. It formalizes the next mathematical
stage of Issue #15. Routes are nonempty depot excursions without intermediate
depot visits, and repeated task visits each incur their service fee. Travel
costs and time windows are outside this model.

## Four-constraint theorem

For a finite rooted tree R, let h(v) be the natural multiplicity of the edge
from parent(v) to v in each direction. Assume the resulting `edgeFlow R h`
has the prescribed degrees d and m. A matrix n : Fin m -> V -> Nat is feasible
exactly when it satisfies:

1. For each non-root v, sum_r n(r,v) = h(v).
2. For each row r, sum over root children of n(r,w) = 1.
3. If n(r,v)>0 and parent(v) is non-root, then n(r,parent(v))>0.
4. For each row, C(r) <= T, where
   a(r,v) = n(r,v) + sum over children w of n(r,w), for non-root v,
   and C(r) = sum over non-root v of s(v)*a(r,v).

The root coordinate of h and of every matrix row is deliberately ignored;
`rowVisits` is zero at the root. In particular, the depot fee is not charged,
even if the supplied service function has a nonzero value there.

`TreeBudgetMatrix.exact_iff_matrix` proves equivalence with `ExactFeasible`.
It allows arbitrary rational service fees and arbitrary rational T.
`canonical_exact_iff_matrix` specializes it to integer-recursion multiplicities
`(requirement R d v).toNat`, under `FlowCompatible`.

The public `TreeBudgetCriterion.exists_tree_budget_routes_iff` accepts a finite
simple tree, its `IsTree` proof, a depot, demands, fleet size, fees and budget.
It constructs the rooted representation internally and derives flow
compatibility in the forward direction. Its right-hand side is compatibility
AND the four-constraint matrix predicate. No extra unproved rooted-tree data
or positive-demand feasibility condition is supplied by the caller.

## Single rows and cost sufficiency

`TreeBudgetRow.ancestor_iff_connected` identifies ancestor closure with depot
connectivity of the symmetric row flow. `row_decomposable` realizes such a row
using as many routes as its root degree. `single_row_realization` specializes
this to root degree one and supplies both exact edge flow and visit counts.
`zero_root_row` proves that an ancestor-closed row of root degree zero has no
non-root positive entry.

`counts_of_flow` and `service_of_flow` apply to any legal realization of a row,
not just to the selected existence witness. Thus changing a route's legal
visit order while preserving its edge counts preserves visit counts and cost.

With s_bar(root)=0 and s_bar(v)=s(v) elsewhere, `rowCost_linear` proves

```text
C(r) = sum_{v != root} (s(v) + s_bar(parent(v))) * n(r,v).
```

Ancestor closure requires positivity only. There is no inequality requiring
a child's multiplicity to be at most its parent's multiplicity.

## Nonnegative splitting normalization

`TreeBudgetNormalization.RelaxedMatrixFeasible` drops constraint 2 while
retaining the same m rows and constraints 1, 3 and 4. For nonnegative
NON-DEPOT fees, `matrix_iff_relaxed` proves that the two matrix predicates are
equivalent, under the prescribed-degree premise.

The proof decomposes row r into k(r) routes, where k(r) is its root degree.
Each resulting route costs at most the row's total cost, because all individual
route costs are nonnegative. Column sums and the target root degree give
sum_r k(r)=m. The dependent family of all split routes is then reindexed by
Fin m. Empty rows produce no routes. Exact flow, demands and per-route budgets
are preserved. The proof needs no additional assumption T>=0; for m>0 and
T<0 both feasibility predicates are false.

This is an existence normalization. Root degree one remains necessary for a
given row to represent exactly one legal route. With signed fees, combining
expensive and negative-cost branches may hide an infeasible route, so this
normalization is not claimed for signed fees.

## Single satellite

For the strict non-depot hub a with one satellite b, satellite demand n and
m>0, the compatible hub demand is m+n. The theorem
`SingleSatelliteClosed.exact_iff_closed` proves, for nonnegative hub and
satellite fees,

```text
ExactFeasible iff s(a) + (s(a)+s(b)) * ceil(n/m) <= T.
```

The source uses natural ceiling division `n ⌈/⌉ m`, defined as
`(n+m-1)/m`. The proof uses the existing `HubSpokePacking.exact_iff_matrix`,
proves a general bounded-allocation lemma, and proves the matching lower
bound via `exists_large_row`. Zero satellite demand and zero fees are allowed.
The general tree matrix theorem handles m=0 separately.

## Source and regression scope

| Module | Content |
| --- | --- |
| `TreeBudgetRow` | Row connectivity, realization, zero rows, visits and linear cost |
| `TreeBudgetMatrix` | Signed-fee exact matrix iff and canonical-flow specialization |
| `TreeBudgetNormalization` | Nonnegative splitting, relaxed matrix iff |
| `TreeBudgetCriterion` | Direct finite-tree budget criterion |
| `SingleSatelliteClosed` | Allocation arithmetic and single-satellite closed formula |
| `TreeBudgetExamples` | Boundary and counterexample guards |

Regression source includes the signed-fee two-leaf counterexample (fees 2 and
-2, T=1); successful nonnegative splitting of a row of root degree two plus
an empty row; the path counterexample to dropping ancestor closure; an empty
fleet; the distinction between budgets 6 and 7 for three visits across two
routes with base fee 1 and incremental fee 3; zero satellite demand; zero fees;
and realization of repeated child-edge multiplicities exceeding the parent
multiplicity. Ten named regression proofs have axiom reports in the source.

## Verification and publication boundary

On 2026-11-01 the targeted Lake build below completed successfully in the
original local development project, with exit code 0 (8337 jobs). All six new
modules and the ten named regression proofs compiled. The reported main
theorems and regression proofs depend only on `propext`, `Classical.choice`
and `Quot.sound`; no `sorryAx` occurs in the successful final build report.
Non-fatal linter warnings remain, including style, unused instances and a
deprecated tactic spelling.

This validation used the pinned Lean 4.30.0-rc2 toolchain and existing local
project/dependency caches. It is a local cached build, not an independent
clean rebuild. The standalone publication package was not rebuilt. Earlier
intermediate compile failures are local development logs, not PASS evidence.

Reproduction command from the project root:

```powershell
lake build LeanCompletion.UAV.TreeBudgetExamples
```

Only the six new Lean modules and this authored document are intended for
publication. Existing Lean sources, frozen targets, root imports, toolchain
and dependency pins are unchanged. Raw logs and build products remain local
under ignored `verification/runs/` and `.lake/` paths. This batch does not
deliver a compiled route generator, matrix search algorithm, or general-tree
dynamic program; their correctness and complexity require separate work.
