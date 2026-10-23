# Service-cut research verification (2026-10-23)

This update targets `research/structural-service-cuts-20261023`.
It adds three modules and extends ResourceCuts; the StructuralServiceCuts
proof already on that branch is unchanged.

| Module | Contribution |
| --- | --- |
| ResourceCuts | Ceiling capacity bounds, a serving-count/cut-flow chain, and impossibility for positive demand with nonpositive remaining capacity |
| LargeServiceCuts | Large-service counting bounds and a parameterized family showing rounded capacity cuts are insufficient |
| FixedFlowObstruction | Feasible service packing with an aggregate fixed flow that has no budget-feasible exact route decomposition |
| FixedFlowStructuralCutExample | A concrete structural cut that rejects that fixed flow |
| StructuralServiceCuts (existing) | General support-aware structural service bounds used by the example |

## Dependency and reproduction commands

Run from the project root with its pinned Lean 4.30.0-rc2 and mathlib
5450b53e5ddc75d46418fabb605edbf36bd0beb6:

```powershell
lake build LeanCompletion.UAV.ResourceCuts LeanCompletion.UAV.LargeServiceCuts LeanCompletion.UAV.StructuralServiceCuts LeanCompletion.UAV.FixedFlowObstruction LeanCompletion.UAV.FixedFlowStructuralCutExample
lake env lean LeanCompletion/UAV/LargeServiceCuts.lean
```

The default LeanCompletion entry remains the frozen Case1 proof. Use the explicit
targets above to check these research modules.

## Checks performed and limitations

Both commands succeeded on 2026-10-23 in the existing local JSP extension project.
The Lake invocation reused dependency and module caches; its output explicitly
replayed ResourceCuts, StructuralServiceCuts and FixedFlowObstruction, and built
LargeServiceCuts and FixedFlowStructuralCutExample. LargeServiceCuts also passed
the separate Lean invocation. Printed axiom lists contained propext,
Classical.choice and Quot.sound (or a subset), with no sorryAx.

There are linter/style warnings. This was not a fresh-clone build of the standalone
UAV package. Publication changes only verification comments in the three new
modules, not their proof code. The existing StructuralServiceCuts proof matches
the local checked proof; its earlier verification comment is retained as history.
The unchanged route/flow dependency sources were compared with the target
repository. No frozen Case1 proof, instance, certificate, toolchain or dependency
pin is changed.

Raw command output and build products are local-only. The new examples concern
abstract service/flow models and do not change the established Case1 four-UAV
conclusion.
