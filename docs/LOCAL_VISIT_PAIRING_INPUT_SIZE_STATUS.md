# Rational input bounds for finite certificate capacity

Issue #14's mathematical input-size work is complete. The new module is
[`LocalVisitPairingInputSize.lean`](../LeanCompletion/UAV/LocalVisitPairingInputSize.lean).
It imports `LocalVisitPairingCertificateSize`, transitively reusing the existing
potential grid, finite candidate and checker. No existing Lean module changes.

## Mathematical result

Write `D = serviceDenominator service`, `B = gridBound service T`,
`N = totalVisits depot required`, `Sden = serviceDenominatorSize service`,
and `p = T.num.natAbs`. The new `Sden` abbreviation is the sum of the canonical
service denominator binary sizes; D, B, N and representationLength are reused.

- For every finite physical type, `D ≤ 2^Sden` and `Nat.size D ≤ Sden+1`.
- With an explicit `[Nonempty V]`, `Nat.size D ≤ Sden`. A depot supplies
  nonemptiness in the routing application. Empty V instead gives D=1, Sden=0.
- For `0 ≤ T`, `T ≤ p`, `B ≤ D*p`, and strictly `B < 2^(Sden + Nat.size p)`.
- Consequently `Nat.size B ≤ Sden + Nat.size p` and
  `representationLength ≤ (N+1)*(2*Nat.size N + Sden + Nat.size p)`.
- The existing raw candidate cardinality is bounded by 2 to this last exponent.

The denominator bounds do not require nonnegative services or a budget.
The budget bounds require only `0 ≤ T`; they do not assume a route family,
positive demand, integral D*T, or positive service fees. `gridBound_cast` is
used only after supplying the nonnegative-budget hypothesis. Strictness in
the exponential bound comes from `p < 2^(Nat.size p)`, also valid at p=0.

## Core Lean interfaces

The following signatures use namespace `UAVProof.LocalVisitPairingInputSize`
and the existing namespaces opened by the source. Universe parameters are
implicit as usual; all required typeclasses and hypotheses are shown.
The module emits `#check` and `#print axioms` for all 18 new theorems.

```lean
serviceDenominator_le_two_pow {V : Type*} [Fintype V] (service : V → ℚ) :
  serviceDenominator service ≤ 2 ^ serviceDenominatorSize service

serviceDenominator_size_le_succ {V : Type*} [Fintype V] (service : V → ℚ) :
  (serviceDenominator service).size ≤ serviceDenominatorSize service + 1

serviceDenominator_size_le {V : Type*} [Fintype V] [Nonempty V]
  (service : V → ℚ) :
  (serviceDenominator service).size ≤ serviceDenominatorSize service

gridBound_le_denominator_mul_num {V : Type*} [Fintype V]
  (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
  gridBound service T ≤ serviceDenominator service * T.num.natAbs

gridBound_lt_two_pow_inputSize {V : Type*} [Fintype V]
  (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
  gridBound service T < 2 ^ (serviceDenominatorSize service + T.num.natAbs.size)

gridBound_size_le {V : Type*} [Fintype V]
  (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
  (gridBound service T).size ≤ serviceDenominatorSize service + T.num.natAbs.size

representationLength_le_inputSize {V : Type*} [Fintype V] [DecidableEq V]
  (depot : V) (required : V → ℕ) (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
  representationLength depot required service T ≤
    (totalVisits depot required + 1) *
      (2 * (totalVisits depot required).size + serviceDenominatorSize service +
        T.num.natAbs.size)

finiteCandidate_card_le_inputCapacity {V : Type*} [Fintype V] [DecidableEq V]
  (depot : V) (required : V → ℕ) (service : V → ℚ) (T : ℚ) (hT : 0 ≤ T) :
  Fintype.card (FiniteCandidate depot required service T) ≤
    2 ^ ((totalVisits depot required + 1) *
      (2 * (totalVisits depot required).size + serviceDenominatorSize service +
        T.num.natAbs.size))
```

## Boundary coverage

General lemmas prove B=0 at T=0, D=1 when every service denominator is 1,
and representationLength=Nat.size B when all task demands vanish (arbitrary
depot demand). Five concrete `decide +kernel` theorems additionally check:

1. Empty physical type: D=1, Sden=0, Nat.size D=1.
2. D=1 and T=1/2: positive fractional budget, B=0.
3. D=2 and T=3/4: D*T=3/2, B=1, Nat.size B=1.
4. Zero demand and positive grid bound B=2: raw representationLength=2.
5. Zero demand and zero budget: representationLength=0, numerator size=0.

The checker and negative-budget rejection semantics are unchanged. No new
negative-budget extension of the main size theorems is claimed.

## Actual local validation (2026-10-31, Asia/Tokyo)

```powershell
cd G:\lean666\jsp_001022_extension
lake build LeanCompletion.UAV.LocalVisitPairingInputSize
$buildCode = $LASTEXITCODE
Write-Host "LeanExitCode=$buildCode"
```

The final run freshly **Built LocalVisitPairingInputSize (27s)** and returned
**LeanExitCode=0**. All 18 new theorem types and axiom reports were emitted.
The reports contain only `propext`, `Classical.choice`, `Quot.sound` or subsets;
none contains `sorryAx`. The new module has no warnings. Existing dependency
warnings and output were replayed; in particular the old checker evaluations
are not newly executed tests in this run. Two preceding development attempts
failed on numerator cast syntax/proof elaboration and are not PASS evidence.

This uses the existing Lean 4.30.0-rc2 environment and Mathlib revision
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. No dependency was updated or downloaded.
All 53 pre-existing local Lean/configuration files and 51 pre-existing
publication-worktree Lean/configuration files retained their baseline SHA256.
All nine dependency revisions in the publication manifest match the local
manifest; the local parent project also has additional existing dependencies.
Of 26 transitive local project imports, 24 match the publication baseline after
line-ending normalization; the remaining two differ only in historical status
comments (`CopyProfileRealizability` and `FixedFlowObstruction`).

The publication baseline is research-branch commit
`db88a43f23225011e4dd7dd9ab5af8dc6fa2c265`. The new module SHA256 is
`7ABB07E4470F3D4EBF774EB0526818B08A271B25C56E0B55D4C5E2DEDCD97B4B`.
Raw logs, theorem output and hash inventories stay local under ignored
`verification/runs/issue14-input-size/`. This is an incremental local build,
not a standalone or clean-environment rebuild.

## Scope and deferred work

This completes the rational-denominator/budget-numerator connection to the
existing numerical certificate capacity. It is not a full input-format or
bit-complexity theorem. N counts expanded visits and may be large relative to
binary-encoded demands. Physical vertex count, service numerators, budget
denominator, edge-flow entries, demands, signs and framing remain distinct
parts of the full input and arithmetic costs.

Binary encoding/decoding, serialization, checker bit-operation complexity,
candidate-space search and independent clean rebuild remain deferred. Issue
#14 stays open for those later batches. Issue #15 is not started in this task.
Earlier stage documents describe their historical baseline; the input-size
gap recorded there is resolved by this module, without revising old results.
