# Strict-hub reduction: binary representation and length

This package implements the fourth work block from issue #23. The wire format
is the one in `HUB_THREE_PARTITION_ENCODING.tex`: MSB-first gamma coding of
`n + 1`, no format tag, no extra list headers, and interleaved parent/multiplicity
fields. It is separate from the tree-budget executor's binary codec.

## Public contracts

| Module under `LeanCompletion/UAV/` | Contracts |
| --- | --- |
| `HubGammaCodec.lean` | `parseGamma_append`, `parseGamma_eq_some_iff`, strict consumption, prefix freedom, exact gamma length, `decodeAll_eq_some_iff`, and field-count bound |
| `HubReductionCodec.lean` | EOF source and general sparse-tree target parsers, exact successful-decoding characterizations, round trips, injectivity, nonempty-tail rejection, and `4*N+1` target field count |
| `HubReductionEncoding.lean` | Canonical target well-formedness; independent parent-edge flow, demand, and service interpretation; equality with the numbered model; route/three-partition equivalences; exact and linear bit-length bounds |
| `HubReductionTotal.lean` | The fixed NO output; total transformation on all bitstrings; source-language iff target-language; `4*input.length+129` bound; every output decodes to a canonical target |
| `HubReductionExamples.lean` | Kernel-reduced wire-format and boundary regressions, plus the feasible direct target of the invalid empty zero-budget source |

All five modules use the namespaces `UAVProof.<module name>`.

For `L = (encodeSource s).length`, the exact formula is

```text
(encodeTarget (canonicalTarget s)).length =
  L + gammaLength (3*s.m+2) + gammaLength s.m +
  gammaLength (4*s.m) + 27*s.m + 4.
```

The formula is proved even for raw source records of the wrong item count:
the unchanged item list contributes the same summand on both sides. The
well-formed target and semantic theorems require `SourceShape s`.

`canonicalTarget_length_le_of_positive` assumes only source shape, positive
budget, and positive items. It proves the `4*L+3` bound.
`canonicalTarget_length_le_of_valid` derives this from the existing
`HubThreePartition.ValidInput`. Neither source validity nor positivity is
imposed by the format parsers. The route equivalence itself needs only shape;
the three-partition equivalence additionally needs `ValidInput`.

## Parser and semantic details

The integer parser scans leading zeros in the supplied input, reads exactly
that many payload bits after the first one, and checks the canonical encoding
of the resulting natural. It returns the unconsumed suffix. The executable
canonicality check supports the full reverse contract, not just round trips.

The integer stream parser uses fuel equal to the actual input bit count.
Structure parsing first decodes actual fields to EOF, then checks the declared
counts. Target arrays are split only after the field-count check; parent
indices are checked after splitting. Decoded `m` or `N` does not set a parsing
loop bound on a short input. This is an implementation property, not a formal
machine running-time theorem.

The sparse target interprets each parent edge in both directions with its
stored multiplicity. The three pointwise bridge theorems identify this flow,
the demand list, and the service list with `HubNumberedInstance`. List-to-`Fin`
conversion is concentrated in `sourceWeights`.

The target language requires a canonical strict-hub shape and actual exact
routing feasibility. It does **not** require source numerical promises.
The total transformation checks source validity separately. In particular,
`m=0, B=0` parses, and its direct target is feasible, but its total-reduction
output is the fixed NO instance. That NO instance has source length 54 and
target length 129, with infeasibility inherited from the existing semantic
theorem for `[9,9,9,13,10,10]` at budget 30.

## Reproduction and evidence boundary

Run from the repository root with the locked toolchain and dependencies:

```powershell
lake build LeanCompletion.UAV.HubReductionExamples
lake env lean verification/AuditHubReduction.lean
py tools/check_hub_encoding.py
```

`AuditHubReduction.lean` enumerates every declaration in the five new
namespaces, including generated instances and auxiliaries. It fails on any
axiom outside `propext`, `Classical.choice`, and `Quot.sound`. Raw output belongs
under ignored `verification/runs/`, never in this status document.

The local implementation uses the preexisting development workspace. All 12
preexisting transitive project dependencies were compared with research
baseline `af411745b18842bf269bd588c8c5587d59b19ce0`: 11 blobs match exactly,
including `HubNumberedInstance.lean` and `HubThreePartition.lean`; the sole
difference in `HubSpokePacking.lean` is extra blank lines at EOF. No existing
dependency source was changed.
It reuses the installed toolchain and cached dependencies; it is not a
fresh-clone replay. The original working branch and unrelated files remain
unchanged. Publication to `research/structural-service-cuts-20261023` reuses
the completed checks below. Two source files have only extra EOF blank lines
removed for publication; no declarations changed. The publication step is not a new Lean
build or independent acceptance run.

### Current local acceptance: 2026-11-09 (Asia/Tokyo)

The fourth block is complete within its representation, semantic-bridge, and
length scope. The all-bitstring totalization is also complete.

- **Targeted Lake build: PASS.**
  `lake build LeanCompletion.UAV.HubReductionExamples` completed successfully,
  covering all five new modules. The final sources produce no new warnings;
  Lake still replays warnings and audit messages from existing dependencies.
  Its 8,329-job build graph includes cached work, not 8,329 newly rebuilt jobs.
- **General proofs and regressions:** 85 named theorems, including 19 regression
  theorems. Concrete computations use `decide +kernel`; general contracts use
  proofs for arbitrary inputs, not finite enumeration.
- **Axiom audit: PASS, exit code 0.** All 303 declarations found in the five
  namespaces, including generated auxiliaries and instances, use only the
  three allowed standard axioms. No `sorryAx` or other added axiom is present.
- **Python reference rerun: PASS, Python 3.13.4.** The unchanged reference
  checker reports 5,124 integer round trips, 943 valid length cases, 945
  source/target round trips, and all 8,191 bitstrings of length at most 12,
  among its other finite checks. This is independent format evidence, not
  another Lean proof or a runtime certification.
- **Local output:** `verification/runs/hub-reduction-20261109/`. This directory
  is confirmed ignored. Neither raw output nor dependency sources are part of
  the delivery.

## Remaining scope

The formalized bitstring map and output-size bounds do not establish a
Turing-machine construction or verification cost. They do not internalize the
external strong NP-completeness theorem for 3-PARTITION, prove general-tree NP
membership, or settle issue #19. Those remain separate work. Historical
validation of the other three work blocks is not relabeled as a new unified
acceptance run by this package.
