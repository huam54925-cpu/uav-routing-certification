# Tree-budget route decomposition: literature comparison and research directions

**Date:** 2026-11-03  
**Research branch:** \`research/structural-service-cuts-20261023\`  
**Code baseline reviewed:** \`2466e0b4b91744045618c78fdb61ecc986863b39\`  
**Scope:** Selective, source-linked literature review and model comparison, **not** a claim of novelty, priority, exhaustive bibliographic coverage, or a new Lean verification.

> **Attribution rule:** Machine checking a theorem does not mean its mathematical content was first discovered here. Separate (i) established mathematical methods, (ii) model-specific theorems and proof engineering, (iii) executable kernel-checked interfaces, and (iv) speculative research proposals. Do not advertise any of the items below as a first result without an exhaustive related-work analysis, exact reduction/model correspondence, and independent assessment.

## 1. Exact model being compared

Our current tree-budget modules use a finite rooted tree with depot \`o\`, natural-number visit demand at non-depot vertices, an exact number \`m\` of depot-to-depot walks, no internal depot visit, no consecutive equal vertices, and repeated visits allowed. **Every** non-depot visit contributes to demand and service cost. Service fees \`s(v)\` and route budget \`T\` are rational, including signed values. The predicate \`BudgetRoutes\` excludes travel distance, edge weights, timing windows, recharging, and time-dependent costs. A root-subtree is a structural restriction on available tree edges, not a tree metric on a complete graph. The original application model's different repeated-visit counting rule is not covered by an automatic equivalence.

The project proves an exact connection between legal routes, a parent-edge multiplicity matrix, legal per-route patterns, certificates, and complete finite search. The corrected parent-edge demands satisfy \`h(v) = d(v) - Σ_{w child of v} h(w)\` at non-root nodes when compatible. The route multiplicity pattern \`p\` has root-child sum one and ancestor-closed positive support, and per-visit service cost is computed using the derived visit counts \`p(v) + Σ_{w child of v} p(w)\`. A valid grouped certificate has weights \`z_p ≥ 0\` with \`Σ_p z_p p(v)=h(v)\`, total routes \`Σ_p z_p=m\`. For exact source theorems see:

- [TreeBudgetCriterion.lean](../LeanCompletion/UAV/TreeBudgetCriterion.lean)
- [TreeBudgetRootFactorization.lean](../LeanCompletion/UAV/TreeBudgetRootFactorization.lean)
- [TreeBudgetResidualSearch.lean](../LeanCompletion/UAV/TreeBudgetResidualSearch.lean)
- [TreeBudgetCertificateCompression.lean](../LeanCompletion/UAV/TreeBudgetCertificateCompression.lean)
- [VisitCopyLift.lean](../LeanCompletion/UAV/VisitCopyLift.lean) and [LocalVisitPairingNextCertificate.lean](../LeanCompletion/UAV/LocalVisitPairingNextCertificate.lean) for the distinct general-flow line of work.

**Non-equivalence caveats:** Most tree CVRP papers constrain transported load, route length, or total distance and generally serve customer demand differently. Their complexity/approximation theorems cannot simply be copied into this signed, per-visit service-budget model. Conversely, changing one constraint does not by itself establish mathematical originality.

## 2. Prior literature: primary-source comparison

| Prior source | Verified prior results or subject | Relation to this repository | Novelty implication |
|---|---|---|---|
| Labbé, Laporte, Mercure (1991), *Capacitated Vehicle Routing on Trees*, Operations Research 39(4):616–622, [DOI](https://doi.org/10.1287/opre.39.4.616) | Classical tree CVRP, NP-hardness, bounds via bin packing, heuristic and enumeration | Tree structure, depot routes and packing are longstanding research topics; capacity and objective differ | Do not call tree routing hardness or packing connection new |
| Asano, Katoh, Kawashima (2001), *A New Approximation Algorithm for the Capacitated Vehicle Routing Problem on a Tree*, [DOI](https://doi.org/10.1023/A:1011461300596) | Approximation on splittable-demand tree CVRP | Different demand/cost semantics, but mature tree-specific combinatorial arguments | Do not present tree-specific decomposition/approximation as unexplored |
| Mathieu & Zhou (2022), *A PTAS for Capacitated Vehicle Routing on Trees*, ICALP, [DOI](https://doi.org/10.4230/LIPIcs.ICALP.2022.95) | PTAS for unit-demand and splittable tree CVRP | Illustrates sophisticated tree routing approximation machinery | Our full exponential checker is not a competitor to that approximation guarantee |
| Mathieu & Zhou (2025), *A tight (1.5+ε)-approximation for unsplittable capacitated vehicle routing on trees*, Mathematical Programming, [DOI](https://doi.org/10.1007/s10107-024-02094-z) | Arbitrary unsplittable terminal load, improved approximation/hardness bounds | Distinct demand assignment but closest evidence of active tree CVRP research | No claim of first tree capacity algorithm |
| Xu, Zhang, Hu & Guo (2021), *A Polynomial-Time Exact Algorithm for k-Depot Capacitated Vehicle Routing Problem on a Tree*, [DOI](https://doi.org/10.1155/2021/6648044) | For specified fixed-k vehicle/depot setting, network-flow-based DP; flow enumeration and splitting; compares prior subtree-joining DP | **Direct precedent for combining internal tree flow states.** Assumptions differ (vehicle count, weighted distance, customer demand) | General internal-subtree DP is not a new idea |
| Döring et al. (2025), *Parameterized Complexity of Vehicle Routing*, IPEC, [DOI](https://doi.org/10.4230/LIPIcs.IPEC.2025.10), [HTML](https://drops.dagstuhl.de/storage/00lipics/lipics-vol358-ipec2025/html/LIPIcs.IPEC.2025.10/LIPIcs.IPEC.2025.10.html) | Load/gas capacities can yield hardness even on trees; treewidth alone insufficient for several CVRP variants; XP algorithms for combinations of treewidth and capacity; tree-decomposition states and generalized multidimensional Bin Packing with endpoint/depot fingerprints | **Strongest direct comparison** for the proposed internal interface and parameterized complexity agenda | Neither generic interface-state DP nor reduction from Bin Packing should be described as novel |
| Gilmore & Gomory (1961), *A Linear Programming Approach to the Cutting-Stock Problem*, [DOI](https://doi.org/10.1287/opre.9.6.849) | Classical pattern-based linear programming/column generation | Counting legal route patterns with integer multiplicities belongs to a mature modeling family | Pattern columns and duplicate-pattern aggregation alone are not new |
| Valério de Carvalho (2002), *LP models for bin packing and cutting stock problems*, [DOI](https://doi.org/10.1016/S0377-2217(02)00124-8) and Delorme, Iori & Martello (2016), *Bin packing and cutting stock problems: Mathematical models and exact algorithms*, [DOI](https://doi.org/10.1016/j.ejor.2016.04.030) | Comparative reviews of pattern-, arc-flow-, DP-, and branch-price models | Natural baselines for residual-demand DP and certificate formats | Do not claim pattern-count formulation or memoization technique itself as an invention |
| Dias et al. (2025), *Minimum flow decomposition in graphs with cycles using integer linear programming*, [DOI](https://doi.org/10.1007/s10898-025-01556-8) | Established flow decomposition; distinguishes paths, trails and walks; optimization versions are combinatorially difficult | Reinforces precise distinction between aggregate flow and types of route decompositions | Basic flow decomposition is classical; our exact repeated-visit budget semantics must be compared separately |
| Cheung, Gleixner & Steffy (2017), *Verifying Integer Programming Results*, [DOI](https://doi.org/10.1007/978-3-319-59250-3_13), [VIPR](https://github.com/scipopt/vipr) | Independent exact-rational MIP certificates, checking and compression | Strong prior art for independent certificates and certificate compression | Do not claim general certificate checking/compression as novel |
| Wood et al. (2026), *Satisfiability modulo theories for verifying MILP certificates*, [DOI](https://doi.org/10.1016/j.jsc.2025.102543) | Formalized verification schema in Why3 and SMT-oriented certificate checker | Formal verification of optimization certificate systems also has prior art | Claim only *specific proven interfaces/model*, not first formal optimization verification |
| Eßmann, Nipkow, Robillard & Sulejmani (2022), *Verified Approximation Algorithms*, [DOI](https://doi.org/10.46298/lmcs-18(1:36)2022), [AFP](https://www.isa-afp.org/entries/Approximation_Algorithms.html) | Isabelle verified approximation algorithms including bin packing/load balancing | Relevant formal algorithm literature across provers | Lean 4 formalization does not by itself prove novel mathematics or an unprecedented formal method |

These are targeted representative primary sources, **not** a systematic proof that no more directly identical theorem exists. Especially before a novelty claim: track backward/forward citations to the 1991 paper, 2021 DP, 2025 IPEC work, Gilmore–Gomory, and formalized optimization libraries.

## 3. What our current theorems do and do not uniquely contribute

| Current item | Status in code | Honest positioning |
|---|---|---|
| Parent-edge count recursion; tree-supported flow uniqueness | Formal theorems | Structural flow conservation on trees is elementary/closely related to established network-flow facts; contribution is the exact Lean statement and linkage to this model |
| Aggregate flow does not certify budget-feasible route decomposition | Counterexamples and copy-lift/paired-flow line | Known qualitative concern in capacitated routing and flow decomposition; model-specific machine-checked separation has reproducibility value |
| Per-route parent-edge pattern criterion and realization | Verified matrix criterion/route equivalence | Model-specific exact iff and constructive realization; mathematical novelty **undetermined**, not a general breakthrough in tree routing |
| Root-child unique ownership; branch matrix iff | Verified | Follows from no intermediate depot return and tree support. Useful mathematically precise decomposition, but root branch decomposition is intuitively classical; no first-discovery claim |
| Finite candidates, complete residual search, correctness/none-iff | Verified for the exact finite model | Classical exhaustive enumeration/backtracking implemented and proved correct/complete; no polynomial-time or performance guarantee |
| Stable complete-row count aggregation, weighted columns, idempotence | Verified | Standard multiset aggregation as a machine-checked representation transformation; subtle one-way checker property with invalid zero-count rows is a useful *implementation-specific* boundary, not a broadly new algorithm |
| Kernel regressions, axioms reports | Reported in existing local cached builds | Evidence of formalization under fixed definitions/toolchain; NOT peer-reviewed novelty, clean-room rebuild, or independent external semantic verification |

**Best present contribution claim:** A reusable, model-specific Lean 4 formalization of exact equivalences (walks ↔ row/matrix ↔ pattern multiplicities), root-local factorization, a proved complete search/checker, and a sound stable certificate-representation transform, with explicit evidence boundaries. Whether identical formalization already exists is **not established by this search**; avoid assertions such as “first Lean formalization of tree CVRP.”

## 4. Research direction A — internal-subtree interface sufficiency

**Prior work that must be analyzed first:** Xu et al. 2021 flow-based / subtree-joining DP; Döring et al. 2025 partial-walk “fingerprints”, multidimensional generalized Bin Packing and join transitions. Both precede our idea of keeping boundary/route identity information.

**Our more precise question:** Given *this exact per-visit-count, fixed-multiplicity, per-route service-cost* model, find a sufficient finite interface for an internal subtree, including boundary traversal copies, pairing/partition into global routes and route-wise resource contributions. Show extraction and reconstruction:
1. Every legal global route family yields consistent interfaces (soundness).
2. Every family of compatible interfaces can be assembled into actual legal global routes (completeness), with no illegal intermediate-depot visit and no double-charged visit.
3. Explore compression/equivalence of interfaces under all valid outside completions; no minimality assertion before proof.
4. Start at one non-depot hub, height-2 / height-3 trees, then lift by induction. Test signed fees and T≤0 separately; use nonnegative-restricted first theorem if necessary and state it.

**Distinctive if achieved:** A formal iff plus verified reconstruction *for our exact service-visit semantics*, possibly a smaller interface with rigorously compared state counts. Not the general idea of tree DP itself.

## 5. Research direction B — verified memoization and precise complexity

**Prior art:** Ordinary DP, bin-packing pattern enumeration, classical memoization; tree VRP PTAS and parameterized algorithms are substantially more advanced in other models. Do not call caching or \`(k,r)\` recursion original.

**Immediate baseline:** [Issue #18](https://github.com/huam54925-cpu/uav-routing-certification/issues/18) already contains executable associative-list cache specification. Do **not** open duplicate implementation issue.

1. Prove \`AnswerValid\` and \`CacheValid\`, including the distinctions cache miss / cached infeasible / cached valid empty rows.
2. Prove memoized recursion preserves cache validity, returns a valid residual witness or justified infeasibility, with fully scanned candidate lists.
3. Connect original matrix/demand input, root branches, compressed successful output; preserve no-extraneous-axioms checks.
4. Bound *reachable* residual vectors by \`S(H)=∏_{v≠o}(H(v)+1)\`; \`k=rootCount(r)\` only for states reached from compatible initial states, while general \`(k,r)\` API must retain \`k\`. Analyze candidate-generation, arithmetic bit costs, association-list lookup, and witness storage separately. \`O(|P|·|V|·S(H))\` is an **idealized candidate-scan count**, not a proved runtime for current code.
5. Cold-cache comparisons, state expansion/hit counts, and sound instrumentation; do not claim real speedups before measurements.

**Hardness caution:** Tree CVRP NP-hardness predates this project (Labbé et al. 1991); Döring et al. 2025 explicitly derive tree hardness from bin packing. A height-2 tree / 3-PARTITION reduction in our exact visit-service model is a **candidate model-correspondence and hardness proof**, not an original discovered hardness phenomenon. If developed, verify hub demand equals parent multiplicity plus children multiplicities, route feasibility in *both* directions, exact fleet count, signed/nonnegative restrictions, binary encoding, and strong-NP-hardness conditions before claiming any theorem. Distinguish our model from load and edge-distance capacity. Check whether standard 3-PARTITION yields a reduction and characterize its strength precisely.

## 6. Research direction C — certificate abstraction and representation

**Prior art:** Classical flow decomposition, patterns and cutting stock, route set partitioning, exact certificate checking/compression; prior exact tree DP retains interface “fingerprints.” Our earlier visit-copy and next-certificate work is not a claim to invent local pairing or finite certificates.

**A substantive, testable target:** Define explicit maps between (i) general-graph visit-copy/local-next certificates, (ii) tree-supported legal route families, (iii) per-route parent-edge matrices, and (iv) grouped pattern-count certificates. Each map must carry exact model assumptions. Prove:
- projection soundness;
- a reconstruction/existence theorem where valid (tree specialization);
- identify information erased (visit ordering, route IDs, pairings, signed fee coordination);
- a strict separation/counterexample when moving from aggregate flow to budget decomposition in general graphs;
- compare representation lengths and verifier costs, without assuming all maps are bijections or efficiently executable.
- For stable compression, distinguish \`Valid(C) → Valid(compress(C))\` from false general \`check(C)=check(compress(C))\`, because an invalid zero-count row can disappear.

**Distinctive if achieved:** A compositional, kernel-checked *map of exact abstraction/refinement interfaces and counterexamples*, rather than a new multiset trick.

## 7. Correct next steps and verification/novelty gates

- **Literature gate:** Read the theorem statements and models of Labbé et al. (1991), Xu et al. (2021), Mathieu–Zhou (2022, 2025), Döring et al. (2025); review source bibliographies and later citing work. Search relevant formal repositories/AFP beyond this short survey. Record paper-model vs our-model matrices (depot rule; repeated visits; load vs service; edge length; signs; exact vs at most fleet).
- **Proof gate:** New claims must be distinctly marked as either *already proved in this repository*, *a proposed mathematical lemma*, or *an established external literature result*. Keep special cases and nonnegative-fee assumptions explicit.
- **Implementation gate:** Keep existing Lean sources, frozen modules, package/toolchain pins and historic input files intact. If formalization is later implemented, use existing cached local environment; no “clean rebuild passed” unless it actually occurs.
- **Efficiency gate:** Distinguish certificate validity, exhaustive-search failure, timeouts, pseudo-polynomial state bounds, real measured runtime and parameterized FPT/XP.
- **Attribution gate:** Cite prior algorithms and include links in any public discussion. Neither a new Lean file nor an AI-generated proof establishes priority.

**Current action status (2026-11-03):** This document adds literature positioning and a research agenda only. No new Lean code, no local build, no complexity theorem, no empirical performance study, no academic priority claim.

## 8. Reference URLs (stable access points)

1. Labbé, Laporte, Mercure (1991): https://doi.org/10.1287/opre.39.4.616
2. Asano, Katoh, Kawashima (2001): https://doi.org/10.1023/A:1011461300596
3. Mathieu & Zhou (2022): https://doi.org/10.4230/LIPIcs.ICALP.2022.95
4. Mathieu & Zhou (2025): https://doi.org/10.1007/s10107-024-02094-z
5. Xu, Zhang, Hu & Guo (2021): https://doi.org/10.1155/2021/6648044
6. Döring et al. (2025): https://doi.org/10.4230/LIPIcs.IPEC.2025.10
7. Gilmore & Gomory (1961): https://doi.org/10.1287/opre.9.6.849
8. Valério de Carvalho (2002): https://doi.org/10.1016/S0377-2217(02)00124-8
9. Delorme, Iori & Martello (2016): https://doi.org/10.1016/j.ejor.2016.04.030
10. Dias et al. (2025): https://doi.org/10.1007/s10898-025-01556-8
11. Cheung, Gleixner & Steffy (2017): https://doi.org/10.1007/978-3-319-59250-3_13
12. Wood et al. (2026): https://doi.org/10.1016/j.jsc.2025.102543
13. Eßmann et al. (2022): https://doi.org/10.46298/lmcs-18(1:36)2022
