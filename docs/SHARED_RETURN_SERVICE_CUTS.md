# Shared-return service cuts — 2026-10-23

New sources: `LeanCompletion/UAV/SharedReturnServiceCuts.lean` and
`LeanCompletion/UAV/SharedReturnLargeServiceCuts.lean`.
Namespaces: `UAVProof.SharedReturnServiceCuts` and
`UAVProof.SharedReturnLargeServiceCuts`.
They reuse StructuralServiceCuts and LargeServiceCuts; no earlier proof is changed.
Publication branch: `research/structural-service-cuts-20261023`.

## Implemented statements

- `SharedReturnPattern`: depot and a are outside B, a differs from depot,
  and departures from the depot or any member of B can only enter a.
- `forced_count_lower_bound`: count(a) >= 1 + sum over B of count(b).
  The proof sums incoming edges from `insert depot B`, so the depot is
  counted once. B may be empty; visits may repeat; other incoming edges
  at a are permitted.
- `forced_service_lower_bound`: the original task service is at least
  s(a) + sum over B of (s(a)+s(b))*count(b). All charged vertices must be
  tasks, and every task service cost is nonnegative.
- `fleet_charged_capacity`: exact coverage on B gives W <= q(B)*(T-s(a)),
  where W = sum over B of (s(a)+s(b))*required(b). Coverage outside B is
  not required. q(B) counts selected routes visiting B, once per route.
- `servingCount_bounds`: q(B) <= |ks| and q(B) <= outgoing cut flow of
  the actual aggregate route flow.
- `capacity_bounds`: with C >= 0, W <= q(B)*C transfers to both fleet
  size and edge cut bounds. Instantiate C = T-s(a) and use the preceding
  fleet theorem. `integer_capacity_bounds` retains q(B) and rounds W/C
  when C > 0.
- `singleton_pattern_iff`, `singleton_count`, `singleton_service`, and
  `singleton_fleet_capacity`: B={b} recovers the earlier hypotheses and
  counting, resource, and serving-fleet conclusions through the new set
  theorems, rather than invoking the old conclusions.

The serving-count resource inequality and combinatorial bounds do not
require a sign hypothesis on T-s(a). Multiplying count upper bounds by
remaining capacity requires T-s(a) >= 0; division requires T-s(a) > 0.
The fleet size means the number of selected legal nonempty routes; if m
is an available fleet upper bound, additionally use |ks| <= m.

## Strength boundary proved in Lean

`cut_eq_sum_singletons` proves x(delta+(B)) equals the sum of the singleton
cut flows for any nonnegative integer flow supported on the pattern.
`rounded_set_cut_of_singletons` then derives the rounded set cut by
summing the unrounded singleton inequalities and rounding once.

Thus this set edge cut cannot exclude an aggregate flow already satisfying
all those singleton inequalities under the stated support assumptions.
This does not identify q(B) with the sum of singleton serving counts, nor
show that the bound retaining q(B) and fleet size is redundant.

## Combined large-service counting

SharedReturnLargeServiceCuts now connects effective fees w(b)=s(a)+s(b)
and capacity C=T-s(a) to the existing large-service counting framework:

- `effective_subset_budget` derives the effective service budget for H subset B.
- `route_count_le_of_effective_threshold` proves at most k occurrences in H
  when every effective fee is strictly greater than C/(k+1), assuming C >= 0.
- `demand_count_le_serving_capacity` is a general exact-coverage bridge that
  counts only routes actually serving H.
- `required_effective_large_count_le` yields sum over H of required(i) <= k*q(H).
- `required_effective_large_count_bounds` also gives bounds by k*|ks| and
  k*outCutFlow(H). Coverage is needed only on H.
- `required_effective_threshold_count_le` supplies the filtered threshold-set
  interface with coverage assumed on B.

The threshold is strict. No claim is made at equality. A subsequent six-node
witness is now provided by SharedReturnSeparationExample, relative to its
explicit PreviousConditions. See [the separation status and resume note](SHARED_RETURN_SEPARATION_STATUS.md).
No additional four-node counterexample was added.

A mathematical observation, not a separate theorem formalized in these files:
under the shared-return support and exact coverage, all outgoing edges of
H subset B go to a outside H. Hence outCutFlow(H)=sum over H of required(i).
For k >= 1, the new counting edge bound therefore reduces to D <= k*D.
The k=0 case can still exclude positive demand. The bounds retaining q(H)
and fleet size are the relevant candidates for strict-strength comparisons.

## Verification performed

On 2026-10-23, from the existing local JSP extension project:

```powershell
lake env lean LeanCompletion/UAV/SharedReturnServiceCuts.lean
```

The final invocation returned exit code 0, with no errors or warnings for
this file. Its twelve printed axiom reports contain only propext,
Classical.choice and Quot.sound, or a subset; none contain sorryAx.
Lean is 4.30.0-rc2 and the existing pinned mathlib revision is
5450b53e5ddc75d46418fabb605edbf36bd0beb6.

The file was elaborated from source; imported modules and mathlib used
the existing local build cache.

After the large-service module was added, the following command was also
executed successfully on 2026-10-23 in the same local project:

```powershell
lake build LeanCompletion.UAV.SharedReturnServiceCuts LeanCompletion.UAV.SharedReturnLargeServiceCuts
```

Lake returned exit code 0. It built SharedReturnLargeServiceCuts from source
and reused existing dependencies/caches, including SharedReturnServiceCuts.
The six new axiom reports contain only propext, Classical.choice and Quot.sound;
none contain sorryAx. Lake reports linter warnings about Fintype assumptions
in these modules, unlike the earlier direct Lean invocation described above.
The publication edit to SharedReturnLargeServiceCuts changes only its outdated
verification header; its checked proof code is unchanged.

These checks are not a fresh standalone UAV checkout build. Raw logs, caches,
and build products remain local. The frozen Case1 proof and dependency pins
are unchanged.
