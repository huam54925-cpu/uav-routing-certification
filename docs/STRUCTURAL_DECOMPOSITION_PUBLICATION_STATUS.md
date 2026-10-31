# Structural decomposition source publication — 2026-10-29

Published to `research/structural-service-cuts-20261023`, based on
`3594b596ccbfb500483c0d1f84d69ebc0ac84e4c`.

## Current-status pointer — 2026-10-31

The record below describes the October 29 publication only. Completeness was
subsequently proved in [46be65c](https://github.com/huam54925-cpu/uav-routing-certification/commit/46be65c20534bfdd537c270ecdb596bf43d9120c):
LocalVisitPairingCompleteness adds the reverse construction and canonical-count
and fixed-count exact-feasibility equivalences. See the
[complete theorem and verification status](LOCAL_VISIT_PAIRING_COMPLETENESS_STATUS.md).
The earlier four modules retain their original source bytes, including draft
pending-verification headers; use the dated records here for validation status.
The historical 58 cached reports are not the later module's 22 reports.

## New modules and scope at the October 29 publication

- [SupportExactFeasibility](../LeanCompletion/UAV/SupportExactFeasibility.lean)
  defines support containment and exact edge-flow feasibility with the same
  demands, route count and service budgets. Exact feasibility implies support
  feasibility; uniqueness from support and prescribed degrees gives equivalence.
- [SameSupportSeparation](../LeanCompletion/UAV/SameSupportSeparation.lean)
  gives a four-node support-feasible instance whose prescribed flow has no
  budget-feasible exact decomposition, despite satisfying the stated aggregate
  conditions and admitting an exact decomposition when budgets are omitted.
- [HubSpokeSupportExact](../LeanCompletion/UAV/HubSpokeSupportExact.lean)
  proves support/degree uniqueness for the stated hub structure and conditional
  equivalence of the two feasibility predicates. It does not assert existence.
- [LocalVisitPairing](../LeanCompletion/UAV/LocalVisitPairing.lean)
  uses occurrence-level predecessor/successor pairing, a decreasing rank and
  budget potentials to derive copy cuts and a physical exact decomposition.
  This is a sufficient certificate, without a completeness or search guarantee.

All four modules concern service budgets; travel costs are excluded. Support
means containment, not equality of positive edge sets or domination of edge
multiplicities. Source bytes, including original pending-verification headers,
are preserved from the local drafts. Those headers do not describe this
publication check; the precise evidence is recorded below.

## Check performed for this publication

On 2026-10-29, in the existing JSP/Prim development project with Lean
`4.30.0-rc2`, the following command returned exit code 0:

```powershell
lake build LeanCompletion.UAV.SupportExactFeasibility LeanCompletion.UAV.SameSupportSeparation LeanCompletion.UAV.HubSpokeSupportExact LeanCompletion.UAV.LocalVisitPairing
```

Lake reported all four requested modules as **Replayed**. This was a successful
cached build check, not fresh compilation of these modules, an independent
proof audit, or a clean build of the standalone UAV package. Cached axiom
reports contained 7, 21, 11 and 19 entries respectively; their combined axiom
set was `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
Linter warnings remain. No earlier verification result is relabeled as new.

The four publication files were checked byte-for-byte against the local source
used by that command. Existing remote proof sources, their newer verification
comments, frozen Case1 modules and dependency pins are preserved. Raw build
output stays local under ignored `verification/runs/publish-20261029/`.
