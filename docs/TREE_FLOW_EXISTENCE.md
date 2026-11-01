# Tree flow existence and budget-free route decomposition

This batch implements the four mathematical targets following commit
`101fddd7a947f751afd6fb060de08978ad4c82a6`. It introduces no service costs,
budget inequalities or general-tree budget dynamic program.

## Main criterion

For a finite tree rooted at the depot, define the integer recursion

```text
H(v) = d(v) - sum_{w child of v} H(w).
```

The root value of H and the depot entry of d are ignored by the criterion.
`TreeFlowCriterion.exists_tree_routes_iff` states that a family of exactly m
legal depot routes, supported on the tree and covering the task demands,
exists if and only if:

1. H(v) >= 0 for every non-root v;
2. m = sum_{w child of depot} H(w);
3. d(v) > 0 implies H(v) > 0 for every non-root v.

The public entry point takes `SimpleGraph.IsTree` and a depot. It constructs
the parent map and a decreasing child rank internally using
`RootedTree.ofIsTree`; these are not extra feasibility assumptions.

## Proof modules

| Module | Main content |
| --- | --- |
| `TreeFlowSymmetry` | Transpose argument using `tree_flow_unique`; `ExactDecomposable` without costs or budgets; coverage from exact flow via `total_outFlow_eq_visit_count`. |
| `TreeFlowExistence` | Integer recursion, natural canonical flow, and `exists_flow_iff` (nonnegative H and root degree equation). |
| `RootedTreeAdapter` | Constructs rooted data from any finite simple tree and chosen depot. |
| `PositiveFlowConnectivity` | Positive-support graph and necessity of depot connectivity for legal route decompositions; zero-flow isolated vertices are allowed. |
| `TreeFlowConnectivity` | `canonicalFlow_connected_iff`: under degree compatibility, positive-demand parent-edge positivity is equivalent to depot connectivity. |
| `RouteSplice` | Legal out-and-back insertion, exact two-arc increment, repeated insertion and finite-family insertion. The inserted vertex may already occur. |
| `TreeRouteDecomposition` | Depot connectivity iff budget-free exact decomposition for symmetric loop-free integer flows; tree corollary derives symmetry. |
| `TreeFlowAlternating` | Exact alternating subtree formula using actual graph distance and a finite set of all child-reachable descendants. |
| `TreeFlowCriterion` | Combined existence criterion and direct route-only entry point. |
| `TreeFlowExamples` | Kernel-checked boundary and counterexample guards. |

The decomposition proof initializes a depot-star family and selects a partial
family of maximum total arc multiplicity, bounded by the target flow. An
out-and-back insertion contradicts maximality whenever a visited node has a
missing arc. Connectivity propagates saturation from the depot to every
positive-flow node. This uses the requested edge-flow invariant, without
maintaining visit-demand equations during insertion. Coverage follows at the
end from exact flow and prescribed degrees. This proves the stronger symmetric
flow theorem without invoking a general Euler-tour interface.

The integer `H` is never computed using truncated natural subtraction.
`Int.toNat` appears only when constructing the candidate natural flow, with
nonnegativity used to prove its exact degrees.

## Boundary coverage

- A four-node path with m=1 and all three task demands equal to one has
  H=(1,0,1): a compatible flow exists, but the parent-edge positivity condition
  fails at the middle task.
- A demand pattern with a negative H value is rejected, guarding integer
  subtraction against accidental truncation.
- Zero demands satisfy flow compatibility with m=0.
- The empty family realizes zero flow and zero task demand.
- A tree consisting only of its depot has a decomposition exactly when m=0,
  regardless of the ignored depot demand.
- Re-inserting an already visited vertex preserves legality and adds exactly
  one unit to each direction of the inserted edge.
- Integration examples apply the final criterion to prove no route family
  exists for the disconnected case, and that a one-route family exists for
  the four-node path with task demands (2,2,1).

## Verification and scope

On 2026-11-01 the targeted Lake build below passed in the existing local project (exit code 0). All new modules and the boundary/integration examples compiled. The reported main theorem axioms are only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs. Non-fatal style and unused-instance warnings remain.
The development environment is the pinned Lean 4.30.0-rc2 toolchain with
existing project and dependency caches. No independent clean rebuild is
claimed. Raw logs and scratch checks remain local under `verification/runs/`.

Reproduction targets from the project root:

```powershell
lake build LeanCompletion.UAV.TreeFlowCriterion LeanCompletion.UAV.TreeFlowExamples
```

No existing theorem source, frozen target, root library import, toolchain or
dependency pin is changed. This publication adds only the ten Lean modules
listed above and this document to the research branch, based on commit
`101fddd7a947f751afd6fb060de08978ad4c82a6`. Logs and build products are excluded.
The verification record describes the local cached build performed before
publication; the standalone publication package has not had an independent
clean rebuild. This batch proves no budget-feasibility theorem or efficient
search algorithm.
