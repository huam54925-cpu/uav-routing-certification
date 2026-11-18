# Subtree budgets, deduplication and explicit routes

## Fixed tree, edge masses and service costs

`TreeBudgetSubtreeBudgetProfile.optimize` returns a least rational budget and its certificate, an all-budgets certificate for a feasible empty fleet, or infeasibility for every budget. For a least result `q`, the original solver returns the same certificate at `q`. Matrix feasibility holds exactly for budgets at least `q`. Under `HasDegrees`, the same interval characterizes exact route families.

Use `prepareQueries R H s m` once and call `table.lookup T` for each budget. Preparation tests root mass before constructing route vectors. A positive compatible fleet uses one automatically scaled root table. The retained entries are the strict prefix minima of the signed row peaks. Lookup returns the same first successful certificate as `solveAuto` and counts the tested thresholds. The count is at most `table.breakpoints`. The cost of forming the table, rational scaling and building the selected certificate are separate from that count.

For positive route count $m$, write $S=\sum_{v\ne o}w_vH(v)$ and $W_+=\sum_{v\ne o}\max(w_v,0)H(v)$. Let $g$ be the gcd of integer weights on positive-mass non-root columns. If $g>0$, each breakpoint divided by $g$ is an integer from $\lceil S/(mg)\rceil$ through $\lfloor W_+/g\rfloor$. The number of full-use candidates also bounds the number of breakpoints. With $g=0$ or $m=1$, at most one breakpoint remains. When a query must preserve the selected position, every retained position is necessary.

## Addressed deduplication

`TreeBudgetSubtreeHeapDedup.dedup` accepts the input heap, shared nil reference, head and length of an ordered entry chain. An entry holds a key-blob address and a payload address. Equality reads key contents. The returned chain shares the original entry addresses, preserving the rightmost representative at each collision.

For input length $n$, output length $d$, and the scalar trace's full suffix-key-map count $K$, the returned heap grows by exactly $3n+6K+3d$ slots. The input and nil sentinel are already present. For keys $a,a,b$, the regression checks the right-hand payload, two membership comparisons, three mapped keys, and 33 new slots.

`TreeBudgetSubtreeHeapDedup.Work.dedupD` additionally reports steps for reference loads, node creation, and key reads/comparisons. It records temporary primitive allocations and persistent node slots separately. On a well-formed input heap it returns the same complete result, and the accumulated persistent writes equal the measured heap growth. The accounting covers these primitives within deduplication. Control and observation-counter maintenance, other DP stages, and a whole-solver addressed time bound remain open.

## From a checked certificate to vertex lists

`TreeBudgetSubtreeRouteOutput.vertices R c` expands rows in certificate order with their multiplicities. The construction uses the repository's child order. On the first crossing of a positive child edge it serves the descendants. Subsequent crossings of that edge go out and back. `round_trip` proves that projection recovers the normalized row and preserves visits and arbitrary signed service costs. `output_word` supplies legality and budget compliance for each word of a checked certificate.

For $M=\sum_{v\ne o}H(v)$ the output comprises exactly $m$ lists, $2M$ edge moves and $2M+m$ stored vertices. On the two-route chain with optimal budget $-3$, the regression obtains two copies of $[0,1,2,1,0]$. The regression projects each word back to every row coordinate and sums the signed fees directly from its visits. It also checks the expanded word length for edge multiplicities from $2^0$ through $2^5$. A running-time bound for the list construction requires a separate implementation analysis.

## Reproduce the targeted checks

From the repository root, build the modules and the example dependencies, then run the executable regressions and axiom reports.

```text
lake build LeanCompletion.UAV.TreeBudgetSubtreeBudgetQueries LeanCompletion.UAV.TreeBudgetSubtreeBreakpointBounds LeanCompletion.UAV.TreeBudgetSubtreeHeapDedupWork LeanCompletion.UAV.TreeBudgetSubtreeRouteOutput LeanCompletion.UAV.TreeBudgetSubtreeAutoExamples
lake env lean verification/CheckTreeBudgetSubtreeBudgetProfile.lean
lake env lean verification/CheckTreeBudgetSubtreeBudgetQueries.lean
lake env lean verification/CheckTreeBudgetSubtreeBreakpointBounds.lean
lake env lean verification/CheckTreeBudgetSubtreeHeapDedup.lean
lake env lean verification/CheckTreeBudgetSubtreeHeapDedupWork.lean
lake env lean verification/CheckTreeBudgetSubtreeRouteOutput.lean
```
