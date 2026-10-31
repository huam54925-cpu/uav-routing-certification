# Finite candidates, executable checking and representation capacity

This stage of Issue #13 connects the canonical potential grid to actual finite
candidate data, a verified checker for one supplied candidate, and exact raw
candidate counts. The model charges service fees per visit; repeated visits
are distinct copies. The depot's demand is ignored.

## Published interfaces

- `LocalVisitPairingFiniteCertificate` defines `FiniteCandidate` with exactly
  three functions: successor, finite rank and finite potential numerator.
  The input fixes the positive service denominator and both range bounds.
  `ValidFiniteCertificate` constrains those same fields, including `0 ≤ T`.
  Existence is equivalent to exact feasibility under the established hypotheses.
- `LocalVisitPairingFiniteChecker` computes task successor edges and depot
  departures using finite enumeration, then checks exact physical projection.
  It ignores the stored depot successor. Its executable definitions do not call
  classical predecessor recovery or enumerate the candidate space.
  `checkCandidate_eq_true_iff` identifies acceptance with existing validity
  without additional assumptions.
- `LocalVisitPairingCertificateSize` counts the actual raw candidate type and
  bounds its cardinality by fixed-width representation capacity. It does not
  change the three-field candidate definition or remove redundant depot entries.

The fixed-fleet feasibility theorem retains

```text
ExactFeasible depot x required m service T
  ↔ m = outFlow Finset.univ x depot
    ∧ ∃ code, checkCandidate depot required x service T code = true.
```

Its assumptions remain physical loop-freeness, nonnegative service fees and
`0 < T`. Rejecting one candidate only invalidates that candidate; it does not
establish instance infeasibility. Empty instances with negative budget are
rejected, even though truncation still gives a natural grid bound.

## Cardinality and capacity

Write `N = totalVisits depot required`, `M = N+1`, and
`B = gridBound service T`. The proved counts are

```text
card (VisitCopy depot required) = N+1
card (FiniteCandidate depot required service T)
  = M^M * (N+1)^M * (B+1)^M
  = (N+1)^(2*(N+1)) * (B+1)^(N+1).
```

These count raw data, including invalid candidates and redundant depot fields,
not valid certificates or distinct route families. They require no budget-sign
assumption. In particular, at `N=0` the raw candidate count is still `B+1`.

If `N+1 ≤ 2^wN` and `B+1 ≤ 2^wB`, then the candidate cardinality is at most
`2^L`, for `L = (N+1)*(2*wN+wB)`. A concrete sufficient choice is
`wN = Nat.size N` and `wB = Nat.size B`; singleton ranges use zero bits.
After fixing copy indices, each copy stores a successor index, a rank and a
potential numerator, with widths `wN`, `wN`, `wB` respectively.

This is a cardinality and numerical capacity result. No binary encoder, parser,
serialization round trip, search algorithm, checker runtime bound or polynomial
bound in the original binary input length has been proved. In particular,
binary-encoded demands can have a large expanded visit count `N`. Relating the
denominator and grid-bound bit sizes to rational input sizes remains future work.

## Reproduction and evidence

```powershell
lake build LeanCompletion.UAV.LocalVisitPairingCertificateSize
$buildCode = $LASTEXITCODE
Write-Host "LeanExitCode=$buildCode"
```

The earlier local finite-candidate build was Built (23s), exit code 0, with
11 selected axiom reports and no `sorryAx`. The earlier checker build was
Built (27s), exit code 0, with 11 selected axiom reports and no `sorryAx`.
Its seven actual evaluations returned `true, false, true, true, false, false,
false`; each also has a `decide +kernel` theorem. The two-return example
deliberately stores a task as the depot successor and is accepted.

The size module was freshly Built (62s) in the existing local dependency
environment, with `LeanExitCode=0`, eight selected axiom reports containing
only standard axioms, no `sorryAx` and no warnings from the new module.
Dependencies, including the two modules above, were replayed from cache;
their earlier evaluations are not reported as new executions in this run.
All 53 pre-existing local Lean/configuration files retained their baseline
hashes, as did all 49 pre-existing publication-worktree Lean/configuration files.
The three published modules match the verified local sources byte for byte.
This is not a fresh standalone rebuild. Raw logs and hash inventories remain
local under ignored `verification/runs/` and are not part of publication.
