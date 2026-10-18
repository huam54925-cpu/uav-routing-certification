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
