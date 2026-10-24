# Case1 proof and certificates

The thirteen `.lean` files are preserved from [the completed proof commit](https://github.com/huam54925-cpu/Drone-Issues/commit/0d4466cbfacf3fe01ca98494663742f9a612b645).

```text
WeakDuality / Flow
  → RouteToFlow → TotalFlow → Connectivity
  → LPBridge → Case1Data
  → Case1Distance / Case1Budget
  → Case1Certificate → Case1Numerics
  → Case1Fleet → Case1Infeasible
```

This is a reading order; the source imports specify the exact dependency graph. The final theorem is `UAVProof.Case1Infeasible.feasible_fleet_card_ge_four`.

`certificates/` includes the fixed instance and dual certificate, the JSON-to-Lean binding and distance-comparison helpers, the independent exact dual verifier, and the previously local-only four-UAV feasibility verifier. The four-UAV witness is the existing [`solution.json`](../../submission_package/question1/results/solution.json); it is not duplicated here.

[`verification/Case1Audit.lean`](../../verification/Case1Audit.lean) contains the ten audit commands used in the completed local proof work, without publishing the raw audit output. Historical outcomes are recorded in [the closure report](../../docs/CASE1_KERNEL_CLOSURE_STATUS.md). New-package execution instructions and limitations are in [REPRODUCIBILITY.md](../../docs/REPRODUCIBILITY.md).

## Service-cut research extensions

The research branch also contains ResourceCuts, AggregateCounterexample,
StructuralServiceCuts, LargeServiceCuts, FixedFlowObstruction and
FixedFlowStructuralCutExample. See [service-cut verification and build commands](../../docs/SERVICE_CUTS_VERIFICATION.md)
for the new results, dependency targets and local-cache limitations. These
extensions do not replace the thirteen frozen Case1 modules above.

SharedReturnServiceCuts generalizes forced-return accounting to a set of nodes,
and SharedReturnLargeServiceCuts combines that accounting with large-service
counting while retaining the number of routes serving the threshold set.
See [shared-return results and verification](../../docs/SHARED_RETURN_SERVICE_CUTS.md)
for build commands, singleton specializations, redundancy results, and the
scope of strict-strength comparisons.

SharedReturnSeparationExample supplies the six-node strict-separation witness
relative to its explicit PreviousConditions. See the [completion and resume note](../../docs/SHARED_RETURN_SEPARATION_STATUS.md)
for the preserved decidableAllowed repair, user-reported Lean verification,
and the exact point at which research was paused.

## Research direction and related work (2026-10-24)

See [the literature comparison and decomposition research plan](../../docs/RESOURCE_DECOMPOSITION_RESEARCH_PLAN_20261024.md)
for the two current questions: how repeated visits affect aggregate sufficiency,
and how exact edge multiplicities differ from support-only feasibility.
The note distinguishes existing results from proposed single-visit, occurrence-lift,
and hub-spoke decomposition theorems, and links the existing research issues.
It records a literature review and plan, not new Lean verification or a novelty claim.

## Single-visit baseline and visit-copy foundations (2026-10-24)

[SingleVisitDecomposition.lean](SingleVisitDecomposition.lean) proves that, under
the single-visit structural assumptions, nonnegative service fees and a positive
budget, all rounded service-capacity cuts are equivalent to a budget-feasible
exact legal route decomposition.

[VisitCopyLift.lean](VisitCopyLift.lean) defines visit copies, their physical
projection and aggregate edge-flow projection. Exact projection to a loop-free
physical flow forces every edge between copies of the same physical node to
have zero flow; this is a derived theorem, not an additional lift assumption.
It also projects supported copy routes to legal physical routes. The updated
snapshot adds visit-count identities, prescribed-demand coverage, and exact
edge-flow projection, together with source proofs of service-cost and budget
preservation.

See [the theorem scope and verification record](../../docs/SINGLE_VISIT_COPY_LIFT_STATUS.md)
for hypotheses, the service-only budget boundary, build commands, and the pause
point. The latest user-reported audit prints 19 declarations through
`projected_copy_routes_exact`; the three service declarations still need their
own axiom-output record. This upload was not independently compiled.
The full lift sufficiency assembly and the physical-route-to-copy construction
remain unfinished.
