# Boschloo exact oracle: first U1 tranche

The original packets below retain their bytes. The additional
`qualification_v1.json` contains 1,440 exact fixed-null comparisons through
total six, and `capability_measurement_v1.json` retains all 156 whole-cell
attempts with named refusals/timeouts. `adversarial_manifest_v1.json` binds the
historical anchors, generic attacks and two strict production failures. See
[U1 qualification](../../../docs_md/evidence/u1-qualification.md) and
[U2 capability](../../../docs_md/evidence/u2-capability.md) for exact scope,
commands, measurements and the unactivated capability proposal.

These fixtures exercise the merged Boschloo-only U0 specification at fixed
rational effects. They are independent standard-library reference calculations
under `tests/unconditional/`, with no production-kernel imports. The normative
definition is `docs_md/unconditional_exact_specification.md`; its exact source
hash is included in the packet.

The packet contains 21 records: equality and near-equality tangency; four
disconnected-acceptance witnesses; multiple nuisance maxima; full-mask,
identically-zero threshold, and zero-level cases; exact decoding of public
binary64 alpha; eight tagged structural cases; and the signed ordering
breakpoint with a rational isolating bracket. Every rational uses reduced
decimal `num`/`den` strings. Ordinary levels and deliberately exact mathematical
side levels have distinct input tags.

## Generate and replay

From a source checkout:

```sh
python -m tools.unconditional_oracle.generate
python -m tests.unconditional._replay
pytest tests/unconditional
```

Generation is repository-only. Replay and fixture data are included in the
sdist and require no `tools/` import. Replay verifies source hashes, the U0
source hash, canonical bytes, schema/procedure versions, primitive hashes and
output hashes, then reconstructs every scientific output. When the generator
source is present, its hash is checked too; sdist replay reports explicitly
that this repository-only source is absent. The source-checkout test executes
fresh generation and requires byte-identical packet and manifest output.

Payload hashes use SHA-256 over `domain + NUL + canonical_JSON_bytes`.
Canonical JSON is UTF-8 with sorted keys, compact separators and one final
newline. Source hashes are ordinary SHA-256 over exact file bytes. Hashes bind
identity, while independent identities, analytic anchors and mutation tests
check the calculation. A source change requires deliberate regeneration after
reconciliation; a checksum update alone is not validation.

## What is established by the reference calculation

The direct product-binomial mass and the common-degree rational Bernstein
representation are reconstructed separately. Per-margin Fisher cutoffs are
reconstructed independently of the generic mask. Tests exercise exact mass
normalization, positive denominator coefficients, control values, de Casteljau
subdivision, inclusive ties, group swap, outcome complementation and structural
endpoint pairs.

For a fixed rational effect, the oracle constructs the original signed
threshold `H=A-alpha_side*B`. If either nuisance endpoint has `H>=0`, it accepts.
Otherwise both endpoint values are negative, and an interior zero is equivalent
to existence of `H>=0` somewhere on the closed interval. A signed Sturm chain
counts distinct roots of a squarefree representative. Endpoint roots are
removed and owned separately. Root normalization is never used to infer the
sign of the original threshold. Thus repeated roots and non-dyadic equality
tangencies accept. The zero polynomial is handled separately.

The recorded stationary polynomial is `A'B-AB'`; `B` is reconstructed from
the complete sample-space mass. In the multiple-maxima anchor there are three
interior stationary roots and an additional endpoint root. The four
disconnected witnesses have respectively 4, 0, 2 and 0 interior threshold
roots, giving accept/reject/accept/reject.

The ordering-breakpoint record establishes one candidate's exact tie and its
membership at the rational bracket endpoints. It does not establish full masks
at the algebraic event or certify that those bracket endpoints occupy the
immediately adjacent complete mask strata.

## Finite scope and outstanding work

The default tests cover every observation for group sizes 1 through 4 at three
rational effects for the mass/control/cutoff identities. Finite coverage checks
use group sizes through 2, three effects, four side levels and four true
nuisance values; each acceptance decision itself uses the exact continuum root
criterion. These checks are finite diagnostics, not the general coverage proof.

Replay accepts group sizes through 12 as an input grammar bound; exhaustive
verification through 12 has not been performed. Polynomial degree, coefficient
bit and operation budgets are explicit diagnostic-oracle safeguards. They are
not proposed production capability limits. Exceeding them raises
`OracleLimitError`.

U1 remains open. Its next tranches include the wider measured corpus and the
complete effect-topology oracle: all ordering and projection events, algebraic
event-point masks, complete accepted components, inner/outer hull evidence,
and the three-lane comparison required by issue #42. U2 strict production
failures are frozen after that oracle authority is complete. The production
fixed-null engine, global inversion and release integration remain later
stages. Barnard and score-RR are outside the Boschloo-only manifest.
