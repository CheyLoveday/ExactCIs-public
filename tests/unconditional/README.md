# Independent Boschloo reference calculations

These modules are standard-library test/reference infrastructure for the merged
[U0 specification](../../docs_md/unconditional_exact_specification.md).
They do not provide public production methods or close implementation issues
[#44](https://github.com/CheyLoveday/ExactCIs-public/issues/44) and
[#45](https://github.com/CheyLoveday/ExactCIs-public/issues/45).

The fixed-null packet contains 21 exact-rational diagnostic records. The
version-2 topology packet contains fourteen complete effect topologies on declared small
inputs and one **event-mask-only** record for the cubic ordering transition
at groups `(4,4)`, observation `(0,2)`. It does not compute that larger table's
complete disconnected confidence set.

The earlier `boschloo_topology_v1.json` and `topology_manifest_v1.json` are
preserved historical bytes. Replay those with commit
`8776f74329ba20bd173d9bf3e6329e5be19dd916`; the current checker selects v2 and
rejects historical source/version identities. The fixed-null packet is unchanged.

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
   nonunits at other components retain the rational-function representation.
   Exact caches are scoped to one bounded work context; root-sign keys include
   the selected isolator. Equal roots can use the common defining factor,
   verified refinements are reused, and endpoint factors are removed before
   isolating the remaining roots. Recompute both inclusive masks at that effect. Zero polynomials,
   even-multiplicity tangencies, and degree drops retain equality acceptance.
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

Outstanding U1 work includes the full measured corpus through the intended
scope, larger disconnected topology, and comparisons among generic tensor,
cutoff/witness-cover and projected-event lanes. Production certificates and
checkers, outward binary64 hulls, mathematical prerequisite integration and
release qualification remain later stages.
