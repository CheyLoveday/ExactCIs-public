# Bounded Boschloo U1 qualification

The source-bound packet contains 1,440 fixed-null comparisons. It enumerates
every observation with positive groups and `n1+n0 <= 6`, plus `(4,4),(0,2)`,
at exact beta values `1/3`, `1`, `7/3`, both directions and side level `1/40`.
Cases through total four and the larger anchor also use levels zero and one
half. No scientific float enters the packet.

| Lane | Accepted | Rejected | Inconclusive |
| --- | ---: | ---: | ---: |
| Direct compact-effect tensor Bernstein | 1,341 | 99 | 0 |
| Independent normalized Fisher cutoff / finite witness | 1,337 | 48 | 55 |
| Exact projected signed-root decision | 1,341 | 99 | 0 |

Every certified decision agrees. The tensor objective is constructed directly
from the product-binomial sum and independently compared coefficient by
coefficient with the projected-event objective. Independent normalized Fisher
tails reconstruct per-margin cutoffs and the expanded mask. Threshold equality
is inclusive; strict negative rejection and unresolved mixed controls remain
different outcomes. The original signed threshold is retained through exact
root counting, including repeated roots and non-dyadic tangencies.

The additional whole-cell experiment attempts all 156 table/observation cases
at side level `1/40`, with every refusal and wall timeout retained. Generic
lower/upper masks and monotone cutoff bands bound the moving mask over rational
intervals enclosing the exact CAD-lite event cells. Sufficient witnesses and
strict rejection covers refine both effect and nuisance coordinates. CAD-lite
retains all event roots, inclusive event masks, structural leaves, components
and the hull. These whole-cell lanes can remain inconclusive even when the
projected-event reference decides. Their measured results and units are in
[U2 capability](u2-capability.md).

## Reproduce

```sh
python -m tools.unconditional_oracle.compare_lanes --output tests/references/unconditional/qualification_v1.json
python -m tests.unconditional._lane_comparison --verify tests/references/unconditional/qualification_v1.json
python -m tests.unconditional._capability_replay
python -m tools.unconditional_oracle.measure_capability --max-total 6 --output measurement.json
python -m pytest tests/unconditional
```

Both scientific replay commands and the stored packet replay test work in an extracted
sdist, without `tools/`. Existing CI runs shipped tests on supported Python and
platform lanes. Local source and extracted-sdist receipts must be assessed
separately from the hosted results on the merged revision.

Packets use sorted compact UTF-8 JSON with one terminal LF. Every scientific
rational has reduced signed decimal `num` and positive `den` strings. Exact
beta and `s=beta/(1+beta)`, alpha and alpha/2, masks, objective coefficients,
schema/procedure versions, primitive/output hashes and the complete local
source dependency closure are bound. Payload hashes use an explicit domain,
NUL and canonical bytes. Scientific reconstruction rejects corruption even
when output hashes are recomputed. Source mutation, omitted cases, booleans in
integer positions, orientation errors, mask/coefficients/probability mutations
and real polynomial-budget refusal have focused tests.

All 21 historical fixed-null records and topology v1–v4 packets remain
byte-identical. The v4 full `(4,4),(0,2)` topology remains a separate completed
expanded-profile reference; a timeout in the new wall-bounded measurement does
not erase it. Conversely, an earlier completed reference does not make a timed
attempt successful.

This evidence is finite. It does not prove universal producer completeness,
Python/Lean equivalence, binary64 outward rounding, production capability or a
release. [Issue #42](https://github.com/CheyLoveday/ExactCIs-public/issues/42)
retains its owner acceptance gate. The target remains Boschloo-only T1-min
global hull endpoint excess; full topology is optional.
