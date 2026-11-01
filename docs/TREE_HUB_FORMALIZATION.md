# Tree uniqueness and strict-hub packing

Proof and publication status, 2026-11-01. These additions implement the two
mathematical targets discussed in
[issue #15](https://github.com/huam54925-cpu/uav-routing-certification/issues/15).

## Statements

`LeanCompletion/UAV/TreeSupportExact.lean` proves:

- `tree_flow_unique`: two natural-valued directed flows supported on the same
  finite simple tree with equal outgoing and incoming degrees are equal.
  The proof deletes a leaf and uses induction on the number of vertices.
- `tree_support_determines_flow`: specializes this to the existing
  `SupportDeterminesFlow` predicate. The target flow itself must satisfy
  `HasDegrees`; support means containment, not equality of positive supports.
- `tree_support_iff_exact`: applies the existing feasibility interface while
  preserving the same routes and budgets.

`LeanCompletion/UAV/HubSpokePacking.lean` proves `exact_iff_matrix` for the
existing canonical strict-hub flow and demand definitions. `MatrixFeasible`
requires natural numbers `n r b` whose column sums are the satellite demands,
and whose row budgets are

```text
service hub + sum_b (service hub + service (satellite b)) * n r b <= T.
```

Both directions are proved: extraction from arbitrary supported legal routes,
and construction of legal routes from lists realizing the matrix rows.
Zero rows become hub-only routes. The statement includes zero route count,
zero satellite demands and repeated visits. The identity holds for rational
service costs without sign restrictions; ordinary bin-packing interpretation
uses nonnegative costs.

## Verification

During proof development on 2026-11-01, the following targeted build passed
in the existing local `jsp_001022_extension` environment with Lean 4.30.0-rc2:

```powershell
lake build LeanCompletion.UAV.TreeSupportExact LeanCompletion.UAV.HubSpokePacking
```

**Local cached build passed; no independent clean rebuild has been performed.**
This reused the existing dependency/build cache; it is not a fresh-clone or
standalone-package rebuild. The three main theorem axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
Style and unused-hypothesis linter warnings remain non-fatal.
Raw build output and local regression inputs are ignored under
`verification/runs/tree-hub/`.

The local-only `lake env lean verification/runs/tree-hub/Examples.lean` also
passed during proof development: two
satellite visits fit in two routes of budget three; a third cannot fit;
zero routes and zero demand impose no budget condition; and a hub-only route
cannot evade a positive hub service cost. That regression input and its raw
output are not included in this publication.

## Publication scope

Publication follows the existing
`research/structural-service-cuts-20261023` branch, based on commit
`284d9b5634ae639ed8812615b4510e44cacefda9`. Only the two new Lean source files
and this explanation are added. The nine-file project import closure matches
the validated local source after line-ending/trailing-blank-line normalization;
the toolchain and every dependency revision in the publication manifest match
the development environment. The latter also contains additional dependencies.
This comparison does not constitute an independent rebuild.

These results do not assert that every tree flow admits budget-feasible routes,
that route decomposition is unique, or that packing has a polynomial-time
algorithm. No general-tree dynamic program or separate bridge-balance lemma
is introduced. The root library import, frozen target and dependency pins
are unchanged. Issue #15 remains open for the broader research programme and
the outstanding independent clean rebuild.
