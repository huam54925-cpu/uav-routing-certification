# Six-node separation: completion and resume note

Recorded on 2026-10-23. Research is paused at the user's request after publishing
the latest local correction to `research/structural-service-cuts-20261023`.

## Preserved source and theorem

- Source: [SharedReturnSeparationExample.lean](../LeanCompletion/UAV/SharedReturnSeparationExample.lean).
- Final theorem: `UAVProof.SharedReturnSeparationExample.strict_separation`.
- The uploaded source preserves the local `decidableAllowed` instance following
  the definition of `allowed`. It unfolds `allowed` and uses `infer_instance`.
- The local proof source is uploaded without edits, including its older draft
  header. That header predates the successful check reported below; it is not
  the current verification status.

## Completed result and precise scope

The instance has six vertices: depot 0, shared-return node 1, satellites
{2,3,4}, and auxiliary node 5. Service costs are (0,1,2,2,2,1), demands are
(0,5,1,1,1,1), the fleet has two routes, and each route has budget 6.
Travel cost is zero and repeated task visits are charged separately.

The final theorem combines:

1. A feasible packing and actual alternative legal routes with exact coverage
   and per-route budgets. Their visit lists are [1,2,3,1] and [1,5,1,4,1].
2. A prescribed integer flow satisfying PreviousConditions: incoming/outgoing
   degrees, no self-loops, arc bounds, connectivity, total service budget, all
   depot-free rounded ordinary capacity cuts, and all applicable immediate
   shared-return volume bounds against both fleet size and cut flow.
3. A legal exact decomposition of that flow when route budgets are omitted.
4. Violation of the new effective large-service count: each satellite has
   effective service 3, remaining capacity is 5, and 3 > 5/2. A supported
   budget-feasible route can therefore serve at most one satellite, whereas
   total satellite demand is three and fleet size is two.
5. No budget-feasible exact decomposition of the prescribed flow.

The stronger helper `no_dominated_cover` also excludes any selected family of
at most two routes whose total edge flow is dominated by the prescribed flow,
whose satellite coverage is exact, and whose route budgets hold.

The alternative feasible routes are not required to use the prescribed flow's
support. Strict separation is relative to the explicitly listed
PreviousConditions, not every conceivable structural or capacity inequality.
It does not change the frozen Case1 result or prove sufficiency of the new cuts.

## Verification provenance

The user confirmed that the final local revision with `decidableAllowed`
passed Lean with exit code 0 and that the printed axiom list for
`strict_separation` contained no `sorryAx`.

This publication pass inspected the source, confirmed the repair and theorem,
and checked that SharedReturnServiceCuts and SharedReturnLargeServiceCuts match
their existing remote versions. It did not rerun Lean, repeat the proofs, or
perform a fresh standalone checkout build. The earlier compilation results
for those dependencies remain documented in SHARED_RETURN_SERVICE_CUTS.md.
Raw logs and build products are not published.

For a future explicit recheck, from the existing project root:

```powershell
lake build LeanCompletion.UAV.SharedReturnLargeServiceCuts
lake env lean LeanCompletion/UAV/SharedReturnSeparationExample.lean
```

## Resume point

Continue from the completed `strict_separation` theorem and its explicit
PreviousConditions baseline. Preserve `decidableAllowed`. Earlier shared-return
counting, resource bounds, singleton specializations, and effective large-service
counting have already been connected; do not restart those proofs. No further
research is scheduled by this publication, and the next task is left for the user.
