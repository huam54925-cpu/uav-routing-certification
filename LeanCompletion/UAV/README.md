# Case1 proof and certificates

The thirteen frozen Case1 `.lean` files are preserved from [the completed proof commit](https://github.com/huam54925-cpu/Drone-Issues/commit/0d4466cbfacf3fe01ca98494663742f9a612b645).

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
point. The October 24 user-reported local run exits with code 0 and prints all 22
axiom checks, including the three service-cost and budget declarations, with no
`sorryAx`. The source update only adds those three audit commands; proofs are
unchanged. This upload was not independently compiled.
At that October 24 snapshot, the full lift sufficiency assembly and the
physical-route-to-copy construction were unfinished. Both directions were
subsequently completed in [f7147cf](https://github.com/huam54925-cpu/uav-routing-certification/commit/f7147cf13d043537fc1a2f2d361eee251b3685e6);
see the current-status update in the linked verification record.

## Copy obstructions and profile cuts (2026-10-26)

Building on the lift/decomposition equivalence added in `f7147cf`, five new
modules connect copy-level obstructions, the limits of fibre-count compression,
service identities, attained minimum cuts, and exact regrouping of all copy
capacity cuts by realizable count profile. The earlier unfinished-work statement
above describes the October 24 snapshot, before that equivalence was added.

See [the results and current verification scope](../../docs/COPY_PROFILE_CUTS_STATUS.md).
Build the new chain with `lake build LeanCompletion.UAV.CopyProfileCuts`.
The October 26 build succeeded in the existing local project, compiling the
final module and replaying cached results for the other four new modules.

## Bounded profiles and exact decomposition (2026-10-27)

CopyProfileRealizability characterizes realizable profiles by explicit integer
bounds. CopyProfileDecomposition connects these bounded profile cuts to exact
service-budget-feasible route decomposition. CopyProfileExample computes the
existing four-node witness's minimum cut as 1 against a rounded requirement of 2.

See [the statements and user-reported verification record](../../docs/COPY_PROFILE_DECOMPOSITION_STATUS.md).
Build this chain with `lake build LeanCompletion.UAV.CopyProfileExample`.
The user supplied three local verification rounds: a direct Lean check of
CopyProfileRealizability (4 axiom reports), a successful build of
CopyProfileDecomposition (3), and a successful build of CopyProfileExample (7).
All three exited with code 0; the 14 distinct reports contain no `sorryAx`.
Replayed dependency reports are not counted as new checks. This documentation
update did not rerun Lean or bind the historical builds to source hashes.

## Executable profile enumeration and checking (2026-10-27)

CopyProfileEnumeration computes the exact minimum cut and all minimizing
subsets for a specified profile. CopyProfileChecker checks all bounded profiles
of a fixed copy flow and proves equivalence with the mathematical capacity-cut
conditions. These are exponential enumeration tools; structural lift conditions
remain separate.

See [the interfaces, examples and verification scope](../../docs/COPY_PROFILE_CHECKER_STATUS.md).
The local `lake build LeanCompletion.UAV.CopyProfileChecker` completed
successfully using cached results for both new modules, including 17 axiom
reports without `sorryAx`. No fresh standalone build is claimed.

## Violation reports and budget-four proof (2026-10-27)

CopyProfileReport renders the four-node witness's violating profiles and
minimizing subsets, proves report soundness, and uses `decide +kernel` to
certify the budget-four check. This yields a service lift and an exact
service-budget-feasible decomposition for the fixed physical flow.
See [the results and build record](../../docs/COPY_PROFILE_REPORT_STATUS.md).
`lake build LeanCompletion.UAV.CopyProfileReport` built this module from
source successfully with cached dependencies; its seven axiom reports contain
no `sorryAx`.
