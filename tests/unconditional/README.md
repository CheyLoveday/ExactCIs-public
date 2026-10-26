# Independent Boschloo reference calculations

These modules are standard-library test/reference infrastructure for the merged
[U0 specification](../../docs_md/unconditional_exact_specification.md).
They do not provide public production methods or close implementation issues
[#44](https://github.com/CheyLoveday/ExactCIs-public/issues/44) and
[#45](https://github.com/CheyLoveday/ExactCIs-public/issues/45).

The fixed-null packet contains 21 exact-rational diagnostic records. The
version-4 topology packet contains seventeen complete effect topologies and one
**event-mask-only** record for the cubic ordering transition. It includes the
complete `(4,4),(0,2)` example with 93 events and two accepted components, under
the separately declared expanded diagnostic profile.

Historical v1, v2 and v3 topology packets/manifests remain byte-identical. Replay
v1 with `8776f74329ba20bd173d9bf3e6329e5be19dd916` and v2 with
`b9e49f674e7ca3bdfc25386b20aee99bb255b528`. Replay v3 with `17860a0ed84e9b68422377742fadc71a27a97851`. Current replay selects v4,
binds both named profiles and rejects altered source/version/profile identities.
The fixed-null packet is unchanged.

```sh
python -m tests.unconditional._replay
python -m tests.unconditional._topology_replay
python -m pytest tests/unconditional -q
```

Both replay commands work in the extracted sdist. They reconstruct scientific
outputs from primitive inputs, verify canonical typed JSON and source hashes,
and reject discrepancies even when an attacker recomputes record digests.
Generation tools are repository-only:

```sh
python -m tools.unconditional_oracle.generate
python -m tools.unconditional_oracle.generate_topology
python -m tools.unconditional_oracle.measure_topology --max-total 4 --output measurement.json
python -m tools.unconditional_oracle.measure_topology --expanded --output expanded.json
```

The measurement enumerates **every observation** with positive groups and
`n1+n0 <= 4`, plus the larger `(4,4),(0,2)` example. It retains every exact
resource refusal. This is a declared partial corpus toward #42; the grammar
bound of 12 per group is not a promise that all such cases finish.
The default limits remain 100,000 wrapper calls and degree 64. `--expanded`
declares a separate diagnostic of 500,000 calls and degree 128, retaining the
4,096-refinement and 16,384-bit caps. Both profiles record every refusal; the
expanded diagnostic is not a production capability proposal.

## Algebraic topology argument

1. Compactify finite positive effects using `s=psi/(1+psi)`. Clear comparison
   denominators by strictly positive factors. Isolate every nonzero comparison
   polynomial's real roots and retain equality in the event-point masks.
2. In each ordering stratum construct the original signed threshold `H(s,q)`.
   Over `Q(s)`, construct its squarefree representative `S`, signed Sturm chain,
   and checked polynomial identities `H=S*D` and `S^m=H*T`. The smallest checked
   exponent avoids unnecessary degree growth. Primitive fraction-free
   remainders clear removable content at each elimination. Signed chain terms
   retain every numerator and divisor scale as factored exact data. Preserve
   the original threshold for signs; a squarefree representative defines only
   a root set.
3. Project all nonconstant coefficient denominators, leading coefficients and
   endpoint sign polynomials needed to specialize those identities and the
   chain, including both sets of scale factors. Guard polynomials are
   squarefree primitive representatives of their zero sets. Their complete
   root partition keeps the original endpoint signs
   and the squarefree root count constant on each remaining open cell.
   A rational representative supplies the constant decision; it alone is not
   authority for the whole cell.
4. Rebuild every exceptional point over its selected real embedding. Defining
   polynomials may be reducible: arithmetic uses `P(alpha)/D(alpha)` with
   nonzero-denominator checks at the selected root. Modular inversion is used
   only after a Euclidean unit calculation and a verified inverse identity;
   a denominator that vanishes only on other components permits their removal
   by checked exact division and a reverified selected-root isolator. Existing
   elements retain their selected embedding. At that embedding, remainders are
   normalized by a nonzero field coefficient, retaining its signed scale;
   ambient rational-polynomial content is not used as field normalization.
   Exact caches are scoped to one bounded work context; root-sign keys include
   the selected isolator. Equal roots can use the common defining factor,
   verified refinements are reused, and endpoint factors are removed before
   isolating the remaining roots. Recompute both inclusive masks at that effect. Zero polynomials,
   even-multiplicity tangencies, and degree drops retain equality acceptance.
   Before a full root decision, exact endpoint/rational witnesses or strictly
   negative Bernstein controls can settle the original signed threshold.
   Otherwise the exact root fallback remains mandatory, including at tangencies.
   Rational effects use the original rational certificate directly. Strict
   interval signs precede unnecessary gcds; fixed-mask threshold polynomials
   are cached within the bounded run.
5. Use U0's separate structural pairs at zero/infinity. Alternate owned points
   and open intervals over the entire compact domain; retain singleton and
   disconnected components, endpoint attainment, and the ideal hull.

This argument and implementation received development self-review. No Lean
soundness proof or independent implementation checker for these topology
records is supplied here. The tests independently use normalized Fisher sums,
fixed-rational-null reconstruction, and an analytic quadratic discriminant.
They include a synthetic irrational singleton and rejection of rehashed
missing-event, missing-leaf, sign, guard, cutoff and hull corruptions.
The factored chain is also expanded and compared with the exact negative
remainder recurrence over both `Q(s)` and a selected real embedding. The
positive primitive rational Sturm calculation is checked against the original
rational oracle on every nonzero coefficient vector in `{-1,0,1}^5`, with
three intervals and separate open/closed endpoint counts.

## Limits and remaining work

`Limits` freezes maximum wrapper calls, refinements, polynomial degree,
coefficient bits and per-polynomial-call Fraction operations. Telemetry counts
wrapper calls; it is **not** a cumulative count of all Fraction operations.
An exhausted limit raises `OracleLimitError` without a successful partial
topology. Failures already occur below the grammar limit; these constants
are diagnostic reference settings, not proposed production capabilities.

The three-lane qualification packet adds **1,440** finite fixed-null comparisons:
all 155 observations with positive groups and total at most six, plus the
`(4,4),(0,2)` observation, at three rational effects and both directions. The
side level is exactly `1/40`; cases through total four and the larger anchor
also include levels zero and one half. Tensor and projected-event decisions
agree on all cases (1,341 accepted, 99 rejected). The independent cutoff/witness
lane certifies 1,337 acceptances and 48 rejections, retaining 55 inconclusions.
Its finite constant-witness search does not claim complete witness covers.
These levels are exact mathematical inputs, distinct from decoded binary64
API arguments. Each record stores exact beta, compact s, alpha, side level,
mask, coefficients, source identities and domain-tagged hashes.

The packet binds the specification and its complete local source dependency
set. Replay rejects changed science even after an output digest is recomputed,
wrong JSON numeric types, missing cases and source drift. Generation writes
compact sorted-key UTF-8 LF bytes directly. Repository generation and standalone replay are:

```sh
python -m tools.unconditional_oracle.compare_lanes --output tests/references/unconditional/qualification_v1.json
python -m tests.unconditional._lane_comparison --verify tests/references/unconditional/qualification_v1.json
python -m tests.unconditional._capability_replay
```

Both scientific replay commands also work in an extracted sdist. Tests additionally retain
generic moving-ridge, irrational tangency and effect-only stall attacks,
explicitly distinguished from Boschloo table fixtures. A bounded lane's
inconclusion never becomes rejection; the exact signed-root fallback remains
necessary.

The all-total-six whole-cell attempts, exact attack bank and capability proposal
are recorded in [U1 qualification](../../docs_md/evidence/u1-qualification.md)
and [U2 capability](../../docs_md/evidence/u2-capability.md). They preserve every
inconclusion, resource refusal and wall timeout. Bounded whole-cell tensor and
cutoff bands certify rational intervals enclosing exact CAD-lite event cells;
a sample alone never licenses a cell decision. Generic attacks remain explicitly
separate from actual Boschloo anchors. Closure of the owning issues requires
the declared acceptance review; no finite corpus supplies a general producer
completeness bound or activates a production cap.

The unchanged default profile now completes 41/42 measured cases (all observations
with positive groups and total at most four). The larger disconnected case
refuses the default degree limit. The unchanged expanded profile completes all
42 measured cases; the disconnected case uses 475,691 of 500,000 wrapper calls.
This finite result is not a completeness or latency claim beyond the corpus.

Version 4 fixes the root-comparison schedule with an explicit stable merge sort
and orders guards before cache-sensitive normalization. This makes exact work
counters reproducible across Python versions. Its LF checkout attributes retain
canonical source/specification/fixture bytes on Windows. The disconnected case
retains 93 events and the same accepted components/hull; one interior isolator
and its cell witness differ from v3. Historical v3 evidence remains version-bound.
