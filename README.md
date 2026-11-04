# UAV Routing Certification

**Lean 4 formalization of exact route decomposition, structural service constraints, and budget certificates.**

This research branch studies when an integer edge flow can be realized by legal depot routes with exact visit demands and individual service budgets. The current focus is tree-supported routing: explicit flow existence, exact decomposition, and a complete edge-count matrix characterization of budget feasibility.

**Research snapshot: November 4, 2026** · Branch: `research/structural-service-cuts-20261023`

The November 3 batch adds a verified full-state cache contract for [Issue #18](https://github.com/huam54925-cpu/uav-routing-certification/issues/18), a reachable-state separation example, and an exact encoding of rational service plus directional travel costs into the existing service-budget checker. The November 4 batch completes memoized recursion, certificate and root-branch integration, and reachable-state/cache-entry bounds; see [implementation and validation](docs/TREE_BUDGET_MEMO_SEARCH_STATUS.md). See [cache contract and validation](docs/TREE_BUDGET_MEMO_STATE_STATUS.md) and [cost encoding, state limits, and comparison with Xu, Döring, and Dias](docs/TREE_BUDGET_STATE_AND_LINEAR_COST_20261103.md).

[Budget matrix results](docs/TREE_BUDGET_MATRIX.md) · [Tree existence and decomposition](docs/TREE_FLOW_EXISTENCE.md) · [Tree uniqueness and hub packing](docs/TREE_HUB_FORMALIZATION.md) · [Research roadmap](https://github.com/huam54925-cpu/uav-routing-certification/issues/15)

The small-scale measurement package now includes proved statistics erasure and controlled comparisons: [performance report and reproduction commands](docs/TREE_BUDGET_MEMO_PERFORMANCE.md). On these tiny cases, memoization reduces repeated expansions but association-list overhead makes cold search slower; pre-generated warm hits and full-entry repeated calls are measured separately.

## Current mathematical results

| Question | Formalized result |
| --- | --- |
| What determines a tree-supported flow? | Specified incoming and outgoing degrees determine at most one flow. An integer recursion gives an explicit existence criterion and an alternating subtree-sum formula. |
| When does a compatible tree flow admit legal depot routes? | Exactly when all positive-flow edges are connected to the depot; equivalently, every positive-demand non-root vertex has a positive parent-edge multiplicity. |
| What information determines a route's service cost? | Its parent-edge multiplicities determine every visit count and its service cost, independently of the chosen legal visit order. |
| When are individual budgets feasible on a tree? | Exactly when flow compatibility and a four-constraint edge-count matrix hold: column sums, one depot departure per row, ancestor closure, and row budgets. |
| Can the one-departure condition be relaxed? | For nonnegative non-depot fees, rows can be split and normalized without changing feasibility. A signed-fee counterexample shows why nonnegativity matters. |
| Is there a closed-form special case? | For a non-depot hub with one satellite, nonnegative task fees and a nonempty fleet, feasibility is determined by a ceiling-allocation formula. |
| Can service and travel budgets reuse the checker? | Rational directional edge costs have an exact signed virtual-service encoding, preserving route costs and matrix/certificate feasibility. |
| Can a few aggregate totals replace the residual vector? | Two states of the same input have the same route count, total cost, visit totals, and positive support, but opposite feasibility. This particular summary is insufficient. |
| What is proved for caching? | Complete memoized recursion preserves the fixed-input answer contract, returns a witness iff the residual problem is feasible, and integrates with the original checker and root-branch interfaces. Reachable-key and actual cache-entry bounds are proved; the executable key remains full `(k,r)`. |
| Do statistics describe the same search? | Erasing counters preserves the exact answer and cache of the memoized executor and the exact answer of the uncached executor. Controlled small-instance measurements are complete; general operation-count and bit-cost bounds remain open. |

The public theorem [`exists_tree_budget_routes_iff`](LeanCompletion/UAV/TreeBudgetCriterion.lean) accepts a finite tree, depot, demands, fleet size, service fees, and budget. It derives flow compatibility in the forward direction and constructs the rooted representation internally. No preselected route ordering or additional unproved rooted-tree data is required.

### Model

Routes start and end at the depot, have a nonempty internal visit list, never visit the depot internally, and have distinct consecutive vertices. Repeated task visits are allowed and each incurs its service fee. Demands count visits exactly; the depot's demand and service fee are ignored. Support means containment, so some tree edges may carry zero flow.

The tree matrix equivalence allows arbitrary rational service fees and budgets. Splitting normalization assumes nonnegative fees only at non-depot vertices. The new cost bridge covers additive rational service and directional travel costs on tree edges. Its virtual fees may be negative even for nonnegative physical costs, so nonnegative-service pruning needs separate justification. Time windows, waiting, order-dependent costs, and exact irrational distances remain outside this bridge.

## Illustrated mathematical overview

The three historical November 1 pages below explain the definitions, proof ideas, matrix constraints, normalization, and that batch's verification boundary. Later executable search and cost/cache results are described in the linked status documents above. Click a page to open the full-resolution image.

[![Page 1: model, tree-flow uniqueness, integer existence criterion, and positive-flow connectivity](docs/images/tree-routing-20261101/page-01.png)](docs/images/tree-routing-20261101/page-01.png)

[![Page 2: exact decomposition, four matrix constraints, linear service cost, nonnegative splitting, and the single-satellite formula](docs/images/tree-routing-20261101/page-02.png)](docs/images/tree-routing-20261101/page-02.png)

[![Page 3: formalization entry point, recorded verification, and remaining algorithmic work](docs/images/tree-routing-20261101/page-03.png)](docs/images/tree-routing-20261101/page-03.png)

## Proof and source map

| Layer | Lean source | Explanation |
| --- | --- | --- |
| Tree-flow uniqueness and support/exact equivalence | [TreeSupportExact](LeanCompletion/UAV/TreeSupportExact.lean) | [Tree and hub baseline](docs/TREE_HUB_FORMALIZATION.md) |
| Integer recursion and flow existence | [TreeFlowExistence](LeanCompletion/UAV/TreeFlowExistence.lean), [TreeFlowAlternating](LeanCompletion/UAV/TreeFlowAlternating.lean) | [Tree existence](docs/TREE_FLOW_EXISTENCE.md) |
| Connectivity and budget-free decomposition | [TreeFlowConnectivity](LeanCompletion/UAV/TreeFlowConnectivity.lean), [TreeRouteDecomposition](LeanCompletion/UAV/TreeRouteDecomposition.lean), [TreeFlowCriterion](LeanCompletion/UAV/TreeFlowCriterion.lean) | [Decomposition and boundary cases](docs/TREE_FLOW_EXISTENCE.md) |
| Row realization, visit counts, and linear cost | [TreeBudgetRow](LeanCompletion/UAV/TreeBudgetRow.lean) | [Single rows and cost sufficiency](docs/TREE_BUDGET_MATRIX.md#single-rows-and-cost-sufficiency) |
| Budget matrix iff and direct tree entry point | [TreeBudgetMatrix](LeanCompletion/UAV/TreeBudgetMatrix.lean), [TreeBudgetCriterion](LeanCompletion/UAV/TreeBudgetCriterion.lean) | [Four-constraint theorem](docs/TREE_BUDGET_MATRIX.md#four-constraint-theorem) |
| Nonnegative splitting normalization | [TreeBudgetNormalization](LeanCompletion/UAV/TreeBudgetNormalization.lean) | [Splitting](docs/TREE_BUDGET_MATRIX.md#nonnegative-splitting-normalization) |
| Hub packing and the single-satellite formula | [HubSpokePacking](LeanCompletion/UAV/HubSpokePacking.lean), [SingleSatelliteClosed](LeanCompletion/UAV/SingleSatelliteClosed.lean) | [Single satellite](docs/TREE_BUDGET_MATRIX.md#single-satellite) |
| Boundary and regression proofs | [TreeFlowExamples](LeanCompletion/UAV/TreeFlowExamples.lean), [TreeBudgetExamples](LeanCompletion/UAV/TreeBudgetExamples.lean) | Nine tree-flow checks and ten budget regression proofs |
| Residual cache contract and regression proofs | [TreeBudgetMemoState](LeanCompletion/UAV/TreeBudgetMemoState.lean), [TreeBudgetMemoStateExamples](LeanCompletion/UAV/TreeBudgetMemoStateExamples.lean) | [Issue #18 first package](docs/TREE_BUDGET_MEMO_STATE_STATUS.md) |
| Complete memoized search, interfaces, and state bounds | [TreeBudgetMemoSearch](LeanCompletion/UAV/TreeBudgetMemoSearch.lean), [TreeBudgetMemoIntegration](LeanCompletion/UAV/TreeBudgetMemoIntegration.lean), [TreeBudgetMemoReachability](LeanCompletion/UAV/TreeBudgetMemoReachability.lean), [TreeBudgetMemoBounds](LeanCompletion/UAV/TreeBudgetMemoBounds.lean), [TreeBudgetMemoExamples](LeanCompletion/UAV/TreeBudgetMemoExamples.lean) | [Recursion and validation](docs/TREE_BUDGET_MEMO_SEARCH_STATUS.md) |
| Verified statistics and controlled measurements | [TreeBudgetSearchStats](LeanCompletion/UAV/TreeBudgetSearchStats.lean), [TreeBudgetBenchCases](LeanCompletion/UAV/TreeBudgetBenchCases.lean), [TreeBudgetBench](LeanCompletion/UAV/TreeBudgetBench.lean), [bounded runner](LeanCompletion/UAV/run_tree_budget_bench.py) | [Performance report and reproduction](docs/TREE_BUDGET_MEMO_PERFORMANCE.md) |
| State separation and travel-cost encoding | [TreeBudgetStateSeparationExamples](LeanCompletion/UAV/TreeBudgetStateSeparationExamples.lean), [TreeBudgetLinearCost](LeanCompletion/UAV/TreeBudgetLinearCost.lean), [TreeBudgetLinearCostExamples](LeanCompletion/UAV/TreeBudgetLinearCostExamples.lean) | [Results and literature comparison](docs/TREE_BUDGET_STATE_AND_LINEAR_COST_20261103.md) |

The decomposition layer also proves a more general result for **symmetric, loop-free integer flows**: with prescribed degrees, depot connectivity of positive flow is equivalent to exact budget-free decomposition. Its proof uses a bounded maximal partial route family and an excursion-insertion argument.

## Verification status

November 3: the new cache contract and examples are checked in the existing local development project; the [cache status](docs/TREE_BUDGET_MEMO_STATE_STATUS.md) records commands, axiom reports, and publication-source comparison. The accompanying [cost/state report](docs/TREE_BUDGET_STATE_AND_LINEAR_COST_20261103.md) retains its separate validation record. These are local cached checks, with no claim of a clean rebuild or of running a complete memoized solver.

The November 1 proof batches add **18 Lean modules and three explanatory documents**:

- [`101fddd`](https://github.com/huam54925-cpu/uav-routing-certification/commit/101fddd7a947f751afd6fb060de08978ad4c82a6): tree-flow uniqueness and strict-hub packing.
- [`674120e`](https://github.com/huam54925-cpu/uav-routing-certification/commit/674120ef954dbddef40acbf315f8b461e2b24fe0): tree-flow existence, connectivity, insertion, decomposition, and alternating sums.
- [`e04db4c`](https://github.com/huam54925-cpu/uav-routing-certification/commit/e04db4c37376e65d252553e241f23f2d1b74453b): tree budget matrices, splitting normalization, and the single-satellite formula.

**November 1 recorded validation: local cached builds passed in the original development project. No independent clean rebuild or standalone publication-package rebuild is claimed.** That batch records exit code 0 and main-theorem/regression axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Non-fatal linter warnings remain. Editing this README does not constitute a new Lean build or axiom audit.

Toolchain: Lean `4.30.0-rc2`, with dependency revisions pinned in [lake-manifest.json](lake-manifest.json). Targeted commands from the project root:

```powershell
lake build LeanCompletion.UAV.TreeFlowCriterion LeanCompletion.UAV.TreeFlowExamples
lake build LeanCompletion.UAV.TreeBudgetExamples
lake build LeanCompletion.UAV.TreeBudgetMemoStateExamples LeanCompletion.UAV.TreeBudgetLinearCostExamples
lake build LeanCompletion.UAV.TreeBudgetMemoExamples LeanCompletion.UAV.TreeBudgetMemoBounds
lake build LeanCompletion.UAV.TreeBudgetBenchCases LeanCompletion.UAV.TreeBudgetBench
```

The earlier November 1 batch supplied existence and equivalence theorems. Subsequent modules provide complete finite and uncached residual search, root-branch integration, and stable certificate compression. The November 4 recursion batch (`c4f9dfe`) records five new modules, 30 kernel regressions, and 89 theorem axiom reports; the 30 regressions are included in the 89 theorems.

The subsequent [measurement batch (`612b075`)](https://github.com/huam54925-cpu/uav-routing-certification/commit/612b07505ce9a4850a11400b128d69751cf88c39) completes Issue #18's agreed small-scale package. Its separate local validation records three new Lean modules and 19 theorem axiom reports (9 statistics-erasure theorems plus 10 case theorems), with no `sorryAx`. The controlled run used 65 timing phases and 1,365 recorded timing samples; the process took 51.94 seconds including startup/loading, not the whole development or build effort. In the two shared-state examples, cold memoization reduced expansions by 33.3% and 40.7%, but search-only median times were 3.59 and 3.06 times the uncached times. Pre-generated warm hits and full-entry repeated calls were measured separately. These are observations for the documented tiny inputs and execution environment, not a general speedup claim.

The measurements and builds came from the existing local development environment; publication and this status synchronization did not rerun them. Raw samples, logs, and build products remain local. General operation-count bounds, memory-bit bounds, and polynomial-time/FPT/XP guarantees are not supplied; follow-up cost analysis is tracked in [Issue #20](https://github.com/huam54925-cpu/uav-routing-certification/issues/20).

## Earlier general certificate framework

The tree results build on the broader study of repeated visits and exact resource-constrained decomposition:

- Visit-copy lifting and exact decomposition: [decomposition status](docs/COPY_PROFILE_DECOMPOSITION_STATUS.md).
- Profile cuts, fixed-lift enumeration, and violation reports: [cuts](docs/COPY_PROFILE_CUTS_STATUS.md), [checker](docs/COPY_PROFILE_CHECKER_STATUS.md), [reports](docs/COPY_PROFILE_REPORT_STATUS.md).
- Local pairing, ranks, and service potentials: [completeness](docs/LOCAL_VISIT_PAIRING_COMPLETENESS_STATUS.md).
- Next-only and bounded certificates: [bounded certificate status](docs/BOUNDED_NEXT_CERTIFICATE_STATUS.md).
- Finite candidates, a single-candidate checker, and representation bounds: [finite certificate status](docs/FINITE_CERTIFICATE_STATUS.md), [input-size module](LeanCompletion/UAV/LocalVisitPairingInputSize.lean).

Each stage retains its own verification record. The general certificate checker and fixed-lift profile checker should not be confused with a tree-matrix search algorithm.

## Next research directions

1. **General execution-cost bounds:** Issue #18's [verified statistics and small-scale measurements](docs/TREE_BUDGET_MEMO_PERFORMANCE.md) are complete. In [Issue #20](https://github.com/huam54925-cpu/uav-routing-certification/issues/20), relate the defined counters to returned-cache size and prove general expansion, candidate-check, and association-list maintenance bounds before analyzing bit costs. Small-instance equalities are evidence for targets, not general theorems.
2. **Internal-subtree interfaces:** use the [literature comparison](docs/TREE_BUDGET_STATE_AND_LINEAR_COST_20261103.md) to specify sufficient endpoint, resource, multiplicity, and pairing information; prove extraction and reconstruction before compression.
3. **Model correspondence:** formalize the depot-splitting bridge to weighted source-to-sink walks, preserving exact visits, edge flow, and per-route cost. Representation refinement remains a separate direction. Further performance experiments should answer a specific open question; the completed measurement package need not be rerun to close Issue #18. General DP, memoization, and weighted flow decomposition already have established prior work.

Encoding matters: a matrix with `m(|V| - 1)` natural-number entries is not automatically polynomial-size in a binary-encoded fleet size. See [Issue #15](https://github.com/huam54925-cpu/uav-routing-certification/issues/15) for the research roadmap and [Issue #14](https://github.com/huam54925-cpu/uav-routing-certification/issues/14) for input representation and verification-cost work.

## Historical application and repository materials

<details>
<summary>Original UAV benchmark, Case1 baseline, papers, and archived programs</summary>

The project originated in a multi-UAV inspection benchmark. The original paper, the repeated-visit correction, the formal lower-bound proof, and the independently checked feasible witness are separate evidence layers. They remain available as historical material; current research concentrates on general route-decomposition theory.

For the fixed historical Case1 model, the lower bound is formalized in Lean and the four-UAV witness was checked by a separate Python verifier. The combined minimum-fleet conclusion is mixed verification, not a Lean theorem of four-UAV feasibility or globally optimal completion time. Its scope and historical validation are documented below.

| Material | Location |
| --- | --- |
| Original paper, appendices, and figures | [paper/original](paper/original/README.md) |
| Repeated-visit correction | [paper/revised](paper/revised/README.md) |
| Historical Case1 proof and model boundary | [Kernel closure record](docs/CASE1_KERNEL_CLOSURE_STATUS.md), [model correspondence](docs/MODEL_CORRESPONDENCE.md) |
| Problem statements and input tables | [source_materials/problem_A](source_materials/problem_A/README.md) |
| Question 1–3 programs and published attachments | [submission_package](submission_package/README.md) |
| ALNS research and selected certificates | [research](research/README.md) |
| Historical Lean module index | [LeanCompletion/UAV](LeanCompletion/UAV/README.md) |
| Provenance and reproduction notes | [Sources](docs/SOURCES.md), [reproducibility](docs/REPRODUCIBILITY.md), [timeline](docs/RESEARCH_TIMELINE.md) |

Historical PASS records refer to their original environments and dates. They are not new validation runs performed by this branch-homepage update.

</details>

## License and attribution

The repository retains its [Apache-2.0 license](LICENSE). Problem statements and third-party materials retain their original sources and attribution; provenance notes do not relicense those materials.
