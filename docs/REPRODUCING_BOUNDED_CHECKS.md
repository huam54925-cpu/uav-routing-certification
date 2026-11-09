# Reproducing the bounded mathematical checks

Run these independent Python models from the repository root with Python 3.10
or later. They use only the standard library; there is no network access,
download, machine-specific configuration, or dependency on ignored run files.

```powershell
py tools/check_hub_encoding.py
py tools/check_single_excursion.py
py tools/check_single_excursion_generalization.py
```

On systems where the launcher is unavailable, use `python3` instead of `py`.
Each script exits nonzero on a failed check and prints a JSON summary to stdout.
The scripts do not write files. To retain output, redirect it to a directory
under ignored `verification/runs/`; generated output is not repository source.

## What is checked

| Entry point | Finite scope |
| --- | --- |
| `check_hub_encoding.py` | Integer and structured binary-code round trips, sparse parent/H records, exact output length and the valid-input `4L+3` inequality, malformed/large headers, canonical target shape, fixed no-instance, certificate checking, and actual route-list reconstruction. Exhausts valid small sources with `m ∈ {1,2}`, `1 ≤ B ≤ 16`, and all binary source strings of length at most 12; also uses explicit boundary cases and fixed-seed integer samples. |
| `check_single_excursion.py` | The original star-interior contract with two leaves, excursion words of length at most three, two participating routes, four exterior slots per route, four signed rational fee schedules and six budgets. Checks exact visits, directed edge flow, service costs, cut/rejoin, fixed/permutable matching, context replacement and the star matrix realization image for `k,H(a),H(b) ∈ {0,1,2}`. Arithmetic uses exact `fractions.Fraction`. |
| `check_single_excursion_generalization.py` | Two nonstar interiors (a path and a branching tree), closed internal walks with at most eight edges, exact gluing and extraction, contextual replacement and multiple-crossing rejection. Separately enumerates sorted rational cost vectors of length at most four, all permutations, and budgets around attained thresholds; checks the sorted iff and nonempty minimax identity. Uses exact rational arithmetic. |

The first model distinguishes syntactic canonical shape from feasible target
membership: a canonical target may be infeasible. Its general-target parser
does not turn the restricted assignment checker into a checker for every tree.
Empty fleets, zero fees/budgets and empty assignment rows are tested separately
from validity of a 3-PARTITION source.

These are bounded executable checks of the specifications in
[the encoding note](HUB_THREE_PARTITION_ENCODING.tex) and
[the original single-excursion contract](TREE_BUDGET_SINGLE_EXCURSION_CONTRACT.tex).
They do not prove the unbounded assertions, polynomial time, or Lean kernel
correctness. In particular, the second entry point tests star interiors; the
arbitrary-subtree and sorted-matching paper results are tested by the third
entry point, with scope in [the new package record](HUB_INTERFACES_STATUS.md).

## Lean reduction representation and length package (November 9)

The unbounded binary parsing, semantic bridge, exact/linear lengths, and total
bitstring transformation now have their own Lean proofs. From the repository
root with the locked toolchain and dependencies, run:

```powershell
lake build LeanCompletion.UAV.HubReductionExamples
lake env lean verification/AuditHubReduction.lean
```

The audit enumerates all declarations in the five new namespaces and fails
on any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. The
[acceptance record](HUB_REDUCTION_ENCODING_STATUS.md) reports 85 named theorems
(19 regressions) and 303 audited declarations, including generated auxiliaries.
The Python checks above remain separate finite reference tests. Machine
running costs and general-tree NP membership are not proved by this package.

## Historical and current records

Commit `dcc3db8` published the Lean semantic package and the original
single-excursion paper; commit `86993ec` published the binary-encoding paper.
Their original run paths and counts remain historical records. Those paths
were never fresh-clone reproduction commands. The two entry points above are
curated source versions of those local models with file-output and timing
bookkeeping removed. The current reruns, new Lean checks and mathematical
scope are recorded separately in [HUB_INTERFACES_STATUS.md](HUB_INTERFACES_STATUS.md).
The third entry point belongs to the new A/B paper package. Run scripts without
Python's `-O` option; the third uses assertions and explicitly rejects that option.

Source preparation, later PDF generation/review, and Lean checking are separate
events. This package does not compile or visually review a PDF, and does not
retroactively turn a historical source-only check into a rendered-document check.
