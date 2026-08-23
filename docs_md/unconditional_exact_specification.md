# Certified unconditional exact intervals: U0 statistical specification

Status: **specified but unshipped.** This document is U0 authority only when
introduced to `main` by an explicitly owner-approved immutable-head merge. It
does not authorize unconditional production implementation. It is the candidate
U0-A/U0-B contract for programme issue #41 and records the #64-ratified
structural OR endpoint lock. It changes no runtime behaviour, does not add a
registry row, and does not represent an unconditional method as available in
ExactCIs 1.1.2.

The release manifest is deliberately narrower than the research programme.
Boschloo odds-ratio inversion is the only method specified for the 1.2.0
train. Other unconditional constructions remain banked, nonblocking research.
Downstream work must consume this manifest rather than treating deferred work
as a hidden release blocker, documentation claim, or placeholder.

## A) Formal statement

Fix a table

```text
             outcome +   outcome -
exposed +        a           b
exposed -        c           d
```

with integer counts `a,b,c,d >= 0`, positive group totals
`n1 = a+b > 0`, `n0 = c+d > 0`, and `N = n1+n0`. Let the design be
`Design.COHORT_BINOMIAL` or `Design.CROSS_SECTIONAL`. In the latter design all
probability and coverage statements below are conditional on the observed
positive group totals. Zero-total observations produce no return. Mixing the
positive-total event bounds over the group-total distribution preserves the
event-level noncoverage bound below.

There are three distinct alpha domains:

```text
generic mathematical validity:  0 <= alpha <= 1 where theorem-appropriate
ordinary confidence intervals:  0 < alpha < 1
executable capability:          the narrower current validate_alpha envelope
```

The executable envelope is a runtime-capability restriction, not a restriction
on the statistical estimand or the mathematical coverage theorem. For a finite
public float accepted by that envelope, write

```text
alpha_num, alpha_den = alpha.as_integer_ratio()
alpha_exact = alpha_num / alpha_den, reduced exactly.
alpha_side  = alpha_num / (2*alpha_den), reduced exactly.
```

All released exact threshold and coverage claims use this decoded binary
rational `alpha_exact` and its side level, never a rounded decimal surrogate.

For every manifest-approved method `m`, the statistical effect domain is the
extended real interval `beta in [0,+infinity]`. At every finite positive **real**
effect and direction `dir in {greater, less}`, U0 fixes a common total preorder
on the finite product-binomial sample space. For an observed table `x`, its
rejection set `R[m,beta,dir](x)` is the inclusive principal set of tables at
least as extreme as `x`. The preorder and rejection set may depend on `beta`
but not on the unconditional nuisance coordinate, which ranges over its full
compact real interval.

The exact fixed-null executable specialization represents a tested finite
effect by a reduced positive rational and uses rational coefficients and
certificates. This is a representation restriction only: it must agree with
the corresponding real statistical ordering after coercion, and it never
changes the real effect/nuisance domain of the method or its coverage claim.

For the point-null model `P[beta,q]`, define

```text
p[m,dir,x](beta)
    = sup over q in Q(beta) of
      P[beta,q](R[m,beta,dir](x)).

A[m,x]
    = {beta in [0,+infinity] :
         p[m,greater,x](beta) >= alpha_side and
         p[m,less,x](beta)    >= alpha_side}.
```

Exact equality with `alpha_side` is accepted. A null is rejected only when a
certificate proves its directional p-value is **strictly less** than
`alpha_side`.

For a nonempty accepted set, the ideal mathematical target is

```text
H_star = the smallest closed interval containing A[m,x].
```

A successful computation may enclose finite transition boundaries, but it must
produce a complete certified partition with no `UNRESOLVED` leaves and retain
an inner set `I` and outer enclosure `O` of the same two-sided accepted-set
contract. A nonempty, non-full interval return is licensed only by
`HULL_CERTIFIED`, which satisfies the ratified T1-min conditions in B.11:
`A subseteq O`, `empty != I subseteq A`, exact structural endpoints, and both
global beta-space endpoint-excess bounds. Consequently

```text
H_star subseteq H_return = hull_beta(O).
```

`BOUNDARY_ENCLOSURE` leaves are neither accepted nor rejected: they contribute
to `O`, not `I`. Component matching is not a `HULL_CERTIFIED` premise; the
stronger `TOPOLOGY_CERTIFIED` state owns component and gap claims. Certified
emptiness and certified fullness are separate terminal branches: the former
requires `O` itself to be empty, while the latter requires `I` to equal the
complete compact effect domain. The implementation may not infer connectedness,
monotonicity, or a first crossing without the named hypotheses and theorem for
that fast path.

For every true effect and nuisance value in an admissible independent-binomial
model, the ideal total procedure has coverage at least `1-alpha`. A
resource-bounded implementation instead satisfies the fail-closed event
contract

```text
P(return and true effect not in returned interval) <= alpha.
```

It does **not** generally claim coverage conditional on return, because refusal
may depend on the observed table. The theorem premise is the fixed-effect
inclusive total preorder above. Nuisance independence and self-inclusion alone
are not sufficient.

## B) Definitions / notation

### B.1 Release boundary and manifest

The following block is the machine-readable candidate U0 release-manifest
contract. It freezes scope only; it does not make the method public or shipped.

<!-- exactcis-unconditional-release-manifest:start -->
```json
{
  "schema": "exactcis.unconditional.release_manifest.v2",
  "status": "specified-unshipped",
  "target_release": "1.2.0",
  "scope_lock": "owner-ratified-boschloo-only",
  "widenable_for_target_release": false,
  "methods": [
    {
      "construction_id": "boschloo_or",
      "designs": ["cohort_binomial", "cross_sectional"],
      "estimand": "odds_ratio",
      "entrypoint": "exact_ci_boschloo",
      "method_key": "boschloo",
      "signature": "exact_ci_boschloo(a: int, b: int, c: int, d: int, alpha: float, *, design: Design) -> tuple[float, float]"
    }
  ],
  "deferred_nonblocking_research": [
    {
      "research_id": "barnard_efficient_score_or",
      "reason": "formal research only; no 1.2.0 public surface or release blocker"
    },
    {
      "research_id": "exact_efficient_score_rr",
      "reason": "formal research only; no 1.2.0 public surface or release blocker"
    }
  ]
}
```
<!-- exactcis-unconditional-release-manifest:end -->

The 1.2.0 manifest is owner-locked and cannot be widened by an implementation
decision or a later U0 amendment. A different method can enter only a later
release after a new owner scope decision. Deferred research has no public
entrypoint, proposed signature, method key, root export, registry row,
compatibility alias, capability row, example, documentation claim,
expected-failure blocker, or placeholder.

U0 freezes exactly one proposed raw-function signature:

```python
exact_ci_boschloo(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float,
    *,
    design: Design,
) -> tuple[float, float]
```

It returns only `(lower, upper)`, requires an explicit design, uses no
continuity correction, and never substitutes another method. No deferred
research name or validation surface is frozen as a Python API contract.

Berger--Boos nuisance adjustment is excluded from the 1.2.0 method identity,
both as a public method and as an internal success or fallback path. The current
authority lacks theorem-complete validity evidence for its required nonempty-set
premise; this is an evidence exclusion, not a cost decision. It cannot enter
without a separate theorem-complete specification and owner decision.

### B.2 Sampling model and validation

For fixed positive `n1,n0`, candidate successes are

```text
X1 ~ Bin(n1,p1),  X0 ~ Bin(n0,p0), independently.
```

`COHORT_BINOMIAL` uses this model directly. `CROSS_SECTIONAL` uses it
conditional on the observed exposure-group totals, so its ratio is a prevalence
odds ratio rather than a prospective odds ratio. For every fixed pair of
positive totals, `P(return and miss | n1,n0) <= alpha`; mixing over positive
totals preserves the bound, while a zero-total table produces no return. Zero
group totals are rejected by `validate_independent_groups` before any
method-specific work. Zero outcome totals are valid structural observations and
must not be rejected.

`CASE_CONTROL_FIXED_MARGIN`, both stratified designs, Boolean counts,
non-integer counts, negative counts, counts above the central package limit,
and alpha outside the current executable capability envelope fail through
existing validation or design errors. The formal mathematical statements instead
use the explicit alpha domains in A; runtime correspondence later proves that
the executable envelope is a permitted specialization.

### B.3 Effect domain and structural fibres

For the Boschloo OR `beta` in its extended real statistical domain, global
inversion uses

```text
s = beta/(1+beta) in [0,1],
beta = s/(1-s) for s < 1.
```

`s=0` and `s=1` are tagged structural states for `beta=0` and
`beta=+infinity`; they are not finite search sentinels. Subdivision may use
exact rational cells in `s`, but each cell denotes every real effect in its
image. A finite boundary cell is small enough only when its image
`[beta_left,beta_right]` satisfies the later evidence-sized rational contract

```text
beta_right - beta_left
    <= effect_abs_tolerance
       + effect_rel_tolerance * max(beta_left,beta_right).
```

Neither tolerance receives a numeric value in U0.

For the odds ratio

```text
psi = p1*(1-p0) / (p0*(1-p1)),
```

the finite positive **real** null curve is defined by

```text
p1*(1-p0) = psi*p0*(1-p1).
```

Writing the finite-null formula in compact coordinates gives

```text
D(s,q) = (1-s)*(1-q) + s*q,
p1(s,q) = s*q / D(s,q).
```

On the closed square `[0,1]^2`, `D` vanishes exactly at the two corners
`(s,q)=(0,1)` and `(s,q)=(1,0)`. Generic joint continuity, polynomial
normalization, moving-mask topology, and tensor bounds therefore apply only on
a closed interior effect stratum

```text
[s_left,s_right] subset (0,1),
0 < s_left <= s_right < 1,
q in [0,1],
```

where `D(s,q) >= min(s_left,1-s_right) > 0`. The states `s=0` and
`s=1`, including both zero-denominator corners, are handled exclusively by the
structural certificates below. No continuity argument may cross or fill either
corner.

Its two structural fibres are unions of boundary faces, not tagged values of
the finite-psi nuisance formula:

```text
psi = 0:         p1 = 0  or p0 = 1,
psi = +infinity: p0 = 0  or p1 = 1.
```

The closure corners `(0,0)` and `(1,1)` are retained. This distinction is
necessary for both kinds of zero or infinite sample-odds-ratio table.

### B.4 Finite positive OR point-null model

For finite real `psi > 0` and real `q in [0,1]`, use

```text
p0(q) = q,
p1(q;psi) = psi*q / (1-q+psi*q),
q in [0,1].
```

For candidate successes `(x,y)` and `m=x+y`,

```text
Pr(X1=x,X0=y | psi,q)
  = C(n1,x) C(n0,y)
    * psi^x * q^m * (1-q)^(N-m)
    / [1+(psi-1)q]^n1.                         (OR-MASS)
```

The denominator exponent is the size of the transformed group and the effect
power is that group's success count. Here both belong to group 1. Swapping
groups maps `(x,y,n1,n0,psi)` to `(y,x,n0,n1,1/psi)` and reverses direction.

For a fixed rejection mask `R`, define

```text
A_R(q) = sum over (x,y) in R of
         C(n1,x) C(n0,y) psi^x q^(x+y)(1-q)^(N-x-y),
B_psi(q) = [1+(psi-1)q]^n1.
```

`B_psi(q)>0` on the full real interval `[0,1]`. For reduced rational `psi`,
exact degree elevation to one common degree `N` gives rational Bernstein
coefficients; after coercion, those coefficients represent the same real
objective. Raw numerator coefficients are not conditional rejection
probabilities. At control index `m`, the ratio of the common-degree numerator
and denominator coefficients is the conditional rejection probability given
total successes `m`.

The rational fixed-null path certifies a function on the real nuisance
continuum. Rational `q` values are witnesses or subdivision endpoints only;
they are never a grid over which the scientific supremum is taken.

### B.5 Exact Boschloo directional ordering

For finite real `psi>0`, candidate `(x,y)` with `m=x+y`, let

```text
lo(m) = max(0,m-n0),
hi(m) = min(n1,m),
w_psi(k;m) = C(n1,k) C(n0,m-k) psi^k,
W_psi(m) = sum from k=lo(m) to hi(m) of w_psi(k;m).
```

The exact inclusive conditional tails are

```text
F_less(x,y;psi)
    = sum[k <= x] w_psi(k;m) / W_psi(m),
F_greater(x,y;psi)
    = sum[k >= x] w_psi(k;m) / W_psi(m).
```

A singleton support has both tail values exactly `1`. For an observed table
`(a,c)`, the rejection masks are

```text
R_greater(psi)
    = {(x,y): F_greater(x,y;psi) <= F_greater(a,c;psi)},
R_less(psi)
    = {(x,y): F_less(x,y;psi) <= F_less(a,c;psi)}.
```

Equality is included. For rational `psi`, the executable comparator uses exact
unnormalised weights and cross multiplication; the current binary64 conditional
evaluator is not an ordering oracle. Its theorem obligation is agreement, after
coercion, with the displayed real-`psi` mathematical ordering. Each tail value
defines a common total preorder at fixed `psi` and direction. The resulting mask
depends on `psi` but is independent of the unconditional nuisance `q`.

This construction extends Boschloo's conditional-tail ordering from the
equality null to tested OR values and then inverts two directional tests. The
name does not claim that the original equality-null article specified this
confidence interval.

### B.6 Exact fixed-null decision

Let `r = alpha_side`. At a reduced rational tested OR, for an exact OR mask,
form the exact polynomial

```text
H_R(q) = A_R(q) - r*B_psi(q).
```

For a fixed mask, the corresponding real objective is continuous on the compact
interval `[0,1]`, so its supremum is attained. Because `B_psi` is positive,

```text
P[psi,q](R) >= r  iff H_R(q) >= 0.
```

Therefore

```text
accept the directional null
    iff there exists q in [0,1] with H_R(q) >= 0;

reject the directional null
    iff H_R(q) < 0 for every q in [0,1].
```

These are statements about every real `q in [0,1]`, not rational-grid
statements. This is an exact closed-interval polynomial sign problem. The
required certificate architecture has two layers:

1. exact Bernstein coefficient signs, exact endpoint or rational witnesses,
   and focused exact de Casteljau subdivision;
2. a complete exact root-and-sign certificate, such as a checked signed
   subresultant construction, for zero polynomials, constants, degree drops,
   endpoint roots, repeated roots, even tangencies, and multiple roots.

Bernstein subdivision alone is not complete for non-dyadic tangency. In
particular, `max H_R == 0` is acceptance, not rejection.

If ordering comparison yields certified masks

```text
R_minus subseteq R_true subseteq R_plus,
```

then the only sound conclusions are

```text
sup P(R_minus) >= r  -> accept,
sup P(R_plus)  < r   -> reject,
otherwise            -> refine or fail closed.
```

The full supremum and an argmax enclosure are optional diagnostics. The exact
threshold relation is the scientific result.

### B.7 Finite-positive exact-p validity and complete-domain coverage

At fixed **finite positive** real `psi` and direction, let `T` be the exact
Fisher-tail ordering value with smaller values more extreme, and let

```text
R(x) = {y: T(y) <= T(x)}.
```

These are nested inclusive principal sets of one total preorder. For every
point-null nuisance `q0`,

```text
p(x) = sup_q P[psi,q](R(x))
     >= P[psi,q0](R(x)).
```

The finite ordered-p lemma makes `p(X)` super-uniform under `q0`. The generic
validity theorem uses `0 <= alpha <= 1` where appropriate; the ordinary CI
corollary uses `0 < alpha < 1`. Hence, on the finite-positive effect branch, the
strict rejection event `p(X)<alpha_side` has probability at most
`alpha_side`. The two directional rejection events each satisfy that bound;
their union has probability at most `alpha`.

This finite ordered-p lemma does **not** certify the separately tagged endpoints
`psi=0` and `psi=+infinity`: B.9 values those by direct structural support, not
by a finite-`psi` preorder. For positive group totals, let
`P[n1,n0,p1,p0]` denote the product-binomial law with `b=n1-a` and `d=n0-c`.
The structural coverage bridge is:

```text
for every p1,p0 in [0,1] with p1 = 0 or p0 = 1:
    P[n1,n0,p1,p0](a = 0 or d = 0) = 1;

for every p1,p0 in [0,1] with p0 = 0 or p1 = 1:
    P[n1,n0,p1,p0](c = 0 or b = 0) = 1.
```

At every `0 < alpha_side <= 1`, B.9 rejects the zero endpoint only on
`a>0 and d>0`, and rejects the infinity endpoint only on `c>0 and b>0`.
Each structural rejection event therefore has probability zero on its own true
structural fibre. At `alpha_side = 0`, the inclusive predicate accepts every
endpoint pair, so structural rejection is identically absent. `U-COVER-001`
must join this structural branch (`U-STRUCT-OR-VALID-001`) with the finite
positive branch (`U-EXACT-P-001` twice) by the complete extended-effect domain
case split; neither branch may stand in for the other.

The all-failure corner `(p1,p0)=(0,0)` and all-success corner `(p1,p0)=(1,1)`
may satisfy more than one structural-fibre label. The validity theorem applies
separately to every such endpoint label; it does not invent a unique true OR at
either nonidentified corner.

The resulting ideal procedure has coverage at least `1-alpha` on the complete
extended OR domain. If the implementation returns only certified outward
enclosures of that ideal accepted-set hull, then
`{return and miss}` is a subset of the ideal noncoverage event and has
probability at most `alpha`. No conditional-on-return coverage follows without
an additional theorem about the refusal mechanism.

The finite-positive hypotheses are: a finite sample space, normalized point-null
masses, one common inclusive total preorder (equivalently, a nested family of
inclusive principal rejection sets) for each fixed effect and direction,
nuisance-independent masks, an exact real-continuum nuisance supremum, and
successful completion. The structural hypotheses are the two direct
product-binomial support identities above and B.9's inclusive endpoint rule. A
grid, sampler, local optimizer, non-nested family of ad-hoc self-containing
masks, finite sampling substituted for structural support, or resource-exhausted
call does not satisfy the theorem.

### B.8 Deferred research boundary

Barnard OR and exact-score risk-ratio research remain banked outside this
navigable 1.2.0 specification. Their formulas, candidate comparators, proposed
names, proof seeds, and fixtures live only in their issue-owned or private
research records. They create no public contract ID and cannot block or widen
the Boschloo-only release. Any later promotion requires a new versioned
manifest and an explicit owner decision after 1.2.0.

### B.9 Structural decisions and observed point estimates

Structural OR values use direct support tests, not finite search limits. They
are a directional Boschloo extension, with tuple order always

```text
(p_greater, p_less).
```

For positive group totals, the complete ratified endpoint valuation is:

| tested structural OR | support predicate | supported pair | unsupported pair |
|---|---|---|---|
| `psi = 0` | `a = 0 or d = 0` | `(1, 1)` | `(0, 1)` |
| `psi = +infinity` | `c = 0 or b = 0` | `(1, 1)` | `(1, 0)` |

The pairs are **values**, not a level-independent accept/reject label.
Structural membership is derived only from

```text
p_greater >= alpha_side and p_less >= alpha_side.
```

Thus, at an ordinary positive side level, an unsupported zero endpoint fails
the greater direction and an unsupported infinity endpoint fails the less
direction. At `alpha_side = 0`, inclusive equality accepts every endpoint,
including the pairs containing zero. No implementation may install an
unconditional structural-rejection state that overrides this threshold rule.
Under a true structural null, generated observations are supported almost
surely; the unsupported observation has null probability zero. The formal
probability identities and their complete-domain coverage role are frozen in
`U-STRUCT-OR-VALID-001`. This endpoint rule is a specified conservative
Boschloo extension, not a limit of the finite-`psi` preorder.

<!-- exactcis-unconditional-structural-or-endpoint-contract:start -->
```json
{
  "schema": "exactcis.unconditional.structural_or_endpoint_contract.v1",
  "scope": {
    "construction_id": "boschloo_or",
    "estimand": "odds_ratio",
    "excludes": ["risk_ratio"]
  },
  "tuple_order": ["p_greater", "p_less"],
  "support": {
    "zero": {
      "predicate": "a == 0 or d == 0",
      "supported_pair": [1, 1],
      "unsupported_pair": [0, 1]
    },
    "positive_infinity": {
      "predicate": "c == 0 or b == 0",
      "supported_pair": [1, 1],
      "unsupported_pair": [1, 0]
    }
  },
  "classification": {
    "accepted_if": "p_greater >= alpha_side and p_less >= alpha_side",
    "rejected_if": "p_greater < alpha_side or p_less < alpha_side",
    "threshold_relation": "inclusive",
    "zero_alpha": "all endpoint pairs are accepted when alpha_side == 0",
    "positive_alpha": "an unsupported endpoint pair is rejected when alpha_side > 0"
  },
  "symmetry": {
    "group_swap": "(a,b,c,d) -> (c,d,a,b)",
    "effect": "zero <-> positive_infinity",
    "directions": "greater <-> less"
  }
}
```
<!-- exactcis-unconditional-structural-or-endpoint-contract:end -->

This contract is OR/Boschloo-only. It must not be reused for risk ratio or any
deferred method.

For **ordinary positive** `alpha_side`, the positive-group-total OR cases are
exhaustive:

| observed condition | uncorrected OR point | threshold-derived structural membership | raw interval consequence | policy point |
|---|---:|---|---|---|
| `a=c=0` (both groups all failures) | non-unique | `0` and `+infinity` accepted; every finite null has p-value `1` | exactly `(0.0, inf)` | raise `NonIdentifiableError` |
| `b=d=0` (both groups all successes) | non-unique | `0` and `+infinity` accepted; every finite null has p-value `1` | exactly `(0.0, inf)` | raise `NonIdentifiableError` |
| `a*d=0`, `b*c>0` | `0` | `0` accepted; `+infinity` rejected by its less-direction zero | lower endpoint exactly `0.0` | point `0.0` |
| `b*c=0`, `a*d>0` | `+infinity` | `0` rejected by its greater-direction zero; `+infinity` accepted | upper endpoint exactly `inf` | point `inf` |
| `a*d>0`, `b*c>0` | finite positive | both endpoints rejected, each in its specified direction | global inversion determines boundedness; endpoint rejection alone does not exclude accepted finite sequences converging to an endpoint | finite sample OR |

At `alpha_side = 0`, replace every endpoint rejection in this table with
acceptance by the preceding inclusive predicate; the table does not create an
exception to zero-alpha semantics.

`EmptyConfidenceSetError(ExactCIsError, RuntimeError)` is the frozen planned
1.2.0 exception for mathematical certified emptiness; U0 specifies it but does
not add it, and it is not currently public. Its trigger is a completed sound
partition proving the certified outer enclosure `O` empty. Failure to find accepted content,
unfinished refinement, an invalid certificate, or exhausted resources cannot
enter this branch. A certified full set proves the complete compact effect
domain accepted, including both structural points, and returns exactly
`(0.0, inf)`. Every unresolved or resource-exhausted search raises
`NumericalError` with method, direction, null value or cell, bounds, counters,
active limits, and a machine-readable failure kind.

The terminal branches are distinct. After complete-partition replay, `O` empty
selects `CERTIFIED_EMPTY`; otherwise `I` equal to the full compact domain
selects `CERTIFIED_FULL`; otherwise a nonempty interval may return only when
T1-min selects `HULL_CERTIFIED`. `TOPOLOGY_CERTIFIED` is optional stronger
evidence attached to a hull result, not a replacement terminal outcome.

<!-- exactcis-unconditional-terminal-contract:start -->
```json
{
  "schema": "exactcis.unconditional.terminal_contract.v1",
  "states": {
    "CERTIFIED_EMPTY": {
      "evidence": "complete sound partition proves O is empty",
      "outcome": "raise EmptyConfidenceSetError"
    },
    "CERTIFIED_FULL": {
      "evidence": "complete sound partition proves I equals the full compact effect domain and I is a subset of A",
      "outcome": "return exactly (0.0, inf)"
    },
    "HULL_CERTIFIED": {
      "evidence": "ratified T1-min contract",
      "outcome": "return the outward-converted certified hull"
    },
    "RESOURCE_EXHAUSTED": {
      "evidence": "active deterministic resource limit exhausted",
      "outcome": "raise NumericalError"
    },
    "UNRESOLVED": {
      "evidence": "classification or certificate obligation remains open",
      "outcome": "raise NumericalError"
    }
  }
}
```
<!-- exactcis-unconditional-terminal-contract:end -->

### B.10 Metamorphic transformations

Freeze the following transformations:

```text
group swap (a,b,c,d) -> (c,d,a,b):
    OR maps to its reciprocal; direction reverses.

outcome complement (a,b,c,d) -> (b,a,d,c):
    OR maps to its reciprocal; direction reverses.
```

The exact OR group-swap map must transform the nuisance parameterization as
well as the effect value. At the tagged endpoints it maps zero to positive
infinity and reverses the ordered directional pair:

```text
structural_p(group_swap(table), +infinity)
    = reverse_directions(structural_p(table, 0)),
structural_p(group_swap(table), 0)
    = reverse_directions(structural_p(table, +infinity)).
```

This endpoint extension is part of the Boschloo OR symmetry, not a rule for
RR.

### B.11 Global accepted-set and hull contract

One semantic engine performs complete accepted-set inversion. An effect cell
`C` denotes every real effect in its compact-coordinate image, even when its
endpoints and internal witnesses are rational. For each direction it supplies
exact or certified table classifications

```text
always in, always out, ordering unresolved,
R_minus_dir(C) subseteq R_beta,dir subseteq R_plus_dir(C)
for every beta in C.
```

Whole-cell rejection proves that for every effect in the cell at least one
direction fails. The baseline certificate uses one fixed direction uniformly
rejected with its upper mask. Failures at unrelated effect points cannot be
combined.

Whole-cell acceptance proves, for each direction,

```text
for every beta in C there exists a nuisance q such that
P[beta,q](R_beta,dir) >= alpha_side.
```

The two directions may use different nuisance witnesses. A point witness at
one effect is insufficient.

Successful leaf states are

```text
ACCEPTED, REJECTED, BOUNDARY_ENCLOSURE,
STRUCTURAL_ACCEPTED, STRUCTURAL_REJECTED.
```

`STRUCTURAL_ACCEPTED` and `STRUCTURAL_REJECTED` are threshold-derived states,
not intrinsic endpoint valuations: each is computed from B.9's ordered pair at
the current `alpha_side`. In particular, `STRUCTURAL_REJECTED` is impossible
at `alpha_side = 0`. A successful structural endpoint record must retain the
pair, support predicate, threshold comparison, and selected direction rather
than storing only the state label.

`UNRESOLVED` is transient or failed. A successful result has a **complete
certified partition**, not necessarily a complete exact accepted/rejected
partition: a boundary enclosure is neither accepted nor rejected and
contributes to the certified outer enclosure, not the certified inner set.

Let the extended beta domain be `E_beta=[0,+infinity]`. Define the mutually
inverse, order-preserving compactification maps

```text
c(beta) = beta/(1+beta) for finite beta,   c(+infinity)=1,
b_ext(s) = s/(1-s) for 0 <= s < 1,        b_ext(1)=+infinity.
```

For the beta-domain accepted set `A[m,x]` in A, define

```text
A_s = c[A[m,x]]
    = {s in [0,1] : b_ext(s) belongs to A[m,x]}.
```

Membership of the tagged points `s=0` and `s=1` is decided by B.9; their
presence in the compact domain does not imply acceptance. For every nonempty
`S subseteq [0,1]`, define `lower_s(S)=inf S`, `upper_s(S)=sup S`, and

```text
hull_beta(S)
    = [b_ext(lower_s(S)), b_ext(upper_s(S))] in E_beta.
```

The hull-transport obligation in `U-HULL-TRANSPORT-001` must prove that
`hull_beta(A_s)` is the smallest closed beta-domain interval containing
`A[m,x]`; this is the `H_star` of A. Let

```text
I = certified inner accepted set in compact coordinate,
O = certified outer accepted enclosure in compact coordinate.
```

The earlier names `A_inner` and `A_outer` mean exactly `I` and `O`. The
nonempty, non-full interval-return assurance state is the owner-ratified
**T1-min** contract:

```text
HULL_CERTIFIED requires

    A_s subseteq O,
    empty != I subseteq A_s,

    b_ext(lower_s(I)) - b_ext(lower_s(O)) <= epsilon_beta,
    b_ext(upper_s(O)) - b_ext(upper_s(I)) <= epsilon_beta,

    exact structural zero/infinity handling,
    a sound partition of the complete compact effect domain,
    no invalid or unresolved leaf omitted from O,
    I and O derived from the same two-sided accepted-set contract.
```

The displayed differences are exact beta-space comparisons on finite endpoint
branches. On the lower structural branch, success requires `0 in I`, B.9
certification that `0 in A_s`, and `lower_s(O)=lower_s(I)=0`; the returned lower
endpoint is exactly `0.0`. If `s=0` is rejected, a **positive** lower claim
requires `lower_s(O)>0`; if that separation is not certified, the computation
refuses rather than emitting a structural zero tag.

On the upper structural branch, success requires `1 in I`, B.9 certification
that `1 in A_s`, and `upper_s(O)=upper_s(I)=1`; the returned upper endpoint is
exactly `inf`. If `s=1` is rejected, a finite upper claim requires
`upper_s(O)<1` and a finite certified beta-space fringe; otherwise the
computation refuses. Structural rejection alone does not prove either required
separation. No expression such as `infinity-infinity` is formed.

On the finite branches, T1-min proves that

```text
H_return = hull_beta(O)
```

contains the ideal hull and has at most `epsilon_beta` global excess at each
endpoint. It does not claim that every point of `H_return` is accepted.
`epsilon_beta` is exactly the capability field
`hull_endpoint_excess_tolerance`, a nonnegative reduced rational. It receives
its evidence-sized value in #52; an implementer cannot choose it. The separate
absolute and relative cell-width tolerances guide refinement and cannot be
substituted for this return-licensing bound.

Component-to-component matching, component counts, interior-gap
classification, and complete accepted-set topology are **not** premises of
`HULL_CERTIFIED`. A small unmatched extreme outer sliver is permitted when the
global beta-space endpoint bound passes. A large unmatched extreme sliver
forces refinement or fail-closed refusal. An unmatched interior outer component
does not invalidate the returned hull, but it forbids topology claims.

`TOPOLOGY_CERTIFIED` is the separate stronger state. It requires every accepted,
rejected, and boundary component and every interior gap to be completely
classified, enclosed, or matched under the stronger topology contract.
Matching remains a useful refinement and assurance strengthening; it is not a
soundness premise of the public interval.

<!-- exactcis-unconditional-assurance-contract:start -->
```json
{
  "schema": "exactcis.unconditional.assurance_contract.v1",
  "endpoint_tolerance_field": "hull_endpoint_excess_tolerance",
  "HULL_CERTIFIED": {
    "requires": [
      "accepted_subset_outer",
      "nonempty_inner_subset_accepted",
      "global_lower_beta_endpoint_excess_within_tolerance",
      "global_upper_beta_endpoint_excess_within_tolerance",
      "exact_structural_endpoints",
      "complete_sound_effect_partition",
      "no_invalid_or_unresolved_leaf_omitted_from_outer",
      "same_two_sided_accepted_set_contract"
    ],
    "does_not_require": [
      "component_matching",
      "component_count",
      "interior_gap_classification",
      "complete_accepted_set_topology"
    ]
  },
  "TOPOLOGY_CERTIFIED": {
    "requires": [
      "HULL_CERTIFIED",
      "complete_component_and_gap_classification_or_matching"
    ]
  }
}
```
<!-- exactcis-unconditional-assurance-contract:end -->

The optional monotone fast path is an optimization of the same method. It
requires a fixed mask on the complete branch, verified coordinate convexity or
monotonicity preconditions, a named theorem for the nuisance-maximized p-value,
separate structural endpoints, and the resulting single-crossing conclusion.
Failure of any premise dispatches to the general engine.

### B.12 Outward binary64 return conversion

Internal component and hull bounds are exact rationals or certified rational
enclosures. Conversion to the public float tuple is directional:

- a finite lower bound is rounded toward negative infinity;
- a finite upper bound is rounded toward positive infinity;
- the converted pair is rechecked against the exact rational bounds using
  `float.as_integer_ratio()`;
- `0.0` and `inf` are emitted only for their tagged structural endpoints.

If a positive finite endpoint cannot be represented without becoming `0.0` or
`inf`, or if binary64 widening violates the evidence-sized beta-space error
contract, the call fails closed. Round-to-nearest conversion alone is not an
outward certificate.

### B.13 Proposed registry text and policy

After all downstream gates, each supported design receives the following row:

| method key | construction | point estimator | interval/test type | calibration | limitations | entrypoint |
|---|---|---|---|---|---|---|
| `boschloo` | Inversion of inclusive directional exact conditional-tail orderings with an exact product-binomial nuisance decision | uncorrected sample odds ratio | exact-arithmetic fixed-null decisions plus certified inner/outer global confidence-set hull | the ideal procedure has at least `1-alpha` coverage; certified returns obey `P(return and miss)<=alpha`; cross-sectional statements condition on positive observed group totals | discrete and potentially disconnected; evidence-sized resource caps may fail closed; finite endpoints may be outward boundary enclosures | `exactcis.exact_ci_boschloo` |

The release status becomes `stable` only after the oracle, adversarial, formal,
implementation-correspondence, artifact, and release gates pass. U0 itself does
not add a planned or experimental row. The OR policy default remains `wald`.
After integration, the explicit policy route is
`compute_or_with_policy(a, b, c, d, design=design, method="boschloo",
alpha=alpha)`. Omitting `method` continues to select `wald` for the two
supported independent-binomial designs. Existing 1.1.2 results and errors must
remain byte-identical.

### B.14 Certificate and replay schema

The schema identity is `exactcis.unconditional.certificate.v1`. Canonical bytes
are UTF-8 JSON with sorted object keys, no insignificant whitespace, decimal
integers, and reduced rational pairs `[numerator,positive_denominator]`.
Structural effect values have exactly one of the canonical objects
`{"kind":"structural","value":"zero"}` and
`{"kind":"structural","value":"positive_infinity"}`; finite positive effect
values are reduced rational pairs and cannot use those objects. Scientific
fields contain no binary64 NaN or infinity. SHA-256 is computed over the
complete canonical object with its `digest` field omitted.

Candidate tables use lexicographic `(x,y)` order. The mask digest preimage is
the canonical JSON object
`{"schema":"exactcis.unconditional.mask.v1","ordering":"lexicographic_xy_v1",`
`"n1":n1,"n0":n0,"states":[...]}` with one state (`in`, `out`, or
`unresolved`) per candidate in that order. The domain tag, both dimensions,
ordering tag, and state array therefore commit the digest to orientation,
dimensions, and tie state. Coefficients use ascending Bernstein index after
exact common-degree normalization.

Every fixed-null certificate contains at least:

| field group | required content |
|---|---|
| identity | schema/procedure version, method, estimand, design, direction, claim ceiling |
| inputs | observed table, group sizes, decoded exact `alpha_exact` and side level, reduced rational tested effect or structural tag |
| ordering | construction ID, exact tie rule, lower/upper mask digests, unresolved count |
| objective | OR basis, exact degree, numerator/denominator or polynomial coefficient digests, arithmetic representation |
| decision | accepted/rejected/indeterminate, strict/equality relation to alpha, exact witness or root/sign leaves |
| bounds | optional p-value lower/upper rationals and argmax enclosure, always labelled diagnostic |
| proof map | contract IDs, theorem IDs, runtime hypotheses and checks |
| resources | states, coefficient bits/storage, subdivision nodes/depth, root-sign work, comparison refinements, active limits, exhausted flag |
| provenance | implementation revision, deterministic replay inputs, source classification, parent/child digests |

Every global certificate additionally contains the canonical effect-cell tree,
leaf ownership and state, the assertion that each cell covers its full real
effect image, direction-specific mask digests, witnesses, boundary widths on
both `s` and beta scales, `A_inner`, `A_outer`, accepted-inner-region records,
boundary-enclosure records, structural points, returned outward hull,
transient-unresolved count which must be zero on success, and the determinism
digest. Component and gap records are required only when the stronger
`TOPOLOGY_CERTIFIED` state is claimed. Its return-conversion record also
contains the exact pre-conversion
rational bounds or structural tags, each returned binary64 bit pattern as 16
lowercase hexadecimal digits, the finite `as_integer_ratio()` witnesses, the
exact directional-comparison results, the post-rounding beta-space error check,
and any underflow/overflow or finite-tag refusal reason.

Replay rebuilds all derived masks, coefficients, decisions, partitions, and
digests from primitive inputs. A verifier checks local certificate conditions
without trusting the producer's scheduling choices. Certificate bytes must be
identical across repeated runs with the same implementation and inputs.
Certificates and verifier types remain internal evidence in 1.2.0: no public
certificate class, root export, registry surface, or return-type change is
authorized.

### B.15 Capability fields and complexity vocabulary

U0 defines units but no values. Final evidence-sized limits live in
`_capability.py`, appear in structured diagnostics and generated documentation,
and receive at-cap/cap-plus-one mutation tests.

| field | unit and counting rule |
|---|---|
| `maximum_sample_space_states` | `M=(n1+1)(n0+1)` candidate tables before enumeration |
| `maximum_polynomial_degree` | exact degree after leading-zero removal |
| `maximum_coefficient_bit_length` | maximum `abs(numerator).bit_length()+denominator.bit_length()` over reduced coefficients |
| `maximum_exact_coefficient_storage` | sum of the preceding bit counts over live exact coefficient arrays |
| `maximum_bernstein_nodes` | visited nuisance-subdivision nodes, root included |
| `maximum_bernstein_depth` | maximum root-to-leaf subdivision edges |
| `maximum_root_sign_work_units` | primitive signed-remainder/subresultant operations under the frozen counter definition |
| `maximum_ordering_refinements` | exact algebraic isolating-interval refinements across all table comparisons |
| `maximum_effect_cells` | created global-effect cells, root included |
| `maximum_effect_depth` | maximum root-to-leaf effect subdivisions |
| `maximum_tensor_nodes` | visited joint effect/nuisance bound nodes |
| `maximum_certificate_bytes` | length of canonical UTF-8 certificate bytes |
| `effect_abs_tolerance` | exact nonnegative rational beta-space absolute width |
| `effect_rel_tolerance` | exact nonnegative rational beta-space relative width |
| `hull_endpoint_excess_tolerance` | exact nonnegative reduced rational `epsilon_beta` controlling each T1-min returned-hull endpoint excess |

Use

```text
M=(n1+1)(n0+1), N=n1+n0,
B=nuisance nodes, S=effect cells.
```

Approved arithmetic-operation claims are: mask construction `O(M)`, equality
or OR-numerator aggregation by total `O(M)`, root Bernstein hull `O(N)`, one
ordinary de Casteljau split `O(N^2)`, and a `B`-node nuisance tree
`O(B*N^2)`, all before integer bit complexity. No wall-clock promise or native
accelerator follows from these counts. Production remains standard-library-only
and the project runtime dependency list remains empty.

### B.16 Formalisation target table

These stable IDs are the proof-to-runtime handoff. Module and theorem names are
targets, not claims that the theorem already exists; issue #12 owns the formal
package substrate. A renamed theorem must retain the contract ID. Software-only
rows are checked by repository gates rather than presented as Lean theorems.

| contract ID | mathematical statement | formal target module/theorem | hypotheses | manifest applicability | future runtime consumer |
|---|---|---|---|---|---|
| `U-MANIFEST-001` | the 1.2.0 release surface contains Boschloo OR only and cannot be widened in this train | software-only manifest guard | owner-ratified release manifest v2 | Boschloo | packaging, registry, docs, installed-surface gates |
| `U-DESIGN-001` | product-binomial finite sample space and normalization | `ExactCIs.Unconditional.ProductBinomial.mass_sum` | positive group totals, probabilities in `[0,1]` | Boschloo | fixed-null mass builder |
| `U-XSEC-001` | fixed-positive-total ideal noncoverage bounds mix over the group-total distribution; the zero-total stratum lies outside the supported procedure | `ExactCIs.Unconditional.ProductBinomial.crossSectionalIdealMix` | conditional product-binomial model at every positive total | Boschloo | ideal cross-sectional coverage |
| `U-XSEC-RETURN-001` | fixed-positive-total return-and-miss bounds mix to the cross-sectional event bound, with zero totals producing no return | `ExactCIs.Unconditional.ProductBinomial.crossSectionalReturnMix` | fixed-positive-total return bounds from (`U-HULL-001` or `U-FULL-001`), plus zero-total no-return validation | Boschloo | returned-event calibration |
| `U-EFFECT-001` | compactification is an order isomorphism `(0,+infinity) <-> (0,1)` with separately tagged `0` and `+infinity` | `ExactCIs.Unconditional.Structural.effectOrderIso` | extended nonnegative effect domain and B.9 structural membership | Boschloo | global effect cells and coordinate bridge |
| `U-HULL-TRANSPORT-001` | the compactification order isomorphism maps the compact hull of every nonempty accepted set exactly to its smallest closed beta-domain interval hull, including tagged endpoints | `ExactCIs.Unconditional.Structural.hullTransport` | `U-EFFECT-001`, nonempty compact accepted set | Boschloo | ideal/returned hull correspondence |
| `U-OR-CORNER-001` | `D(s,q)` vanishes exactly at `(0,1)` and `(1,0)`; generic continuity is restricted to closed interior effect strata and composes with separate structural certificates | `ExactCIs.Unconditional.Structural.orCornerDecomposition` | `0<s_left<=s_right<1`, `q in [0,1]` | Boschloo | cell-domain validation and endpoint dispatch |
| `U-OR-NULL-001` | finite real OR null parameterization satisfies the cross-product equation; rational coefficients are a coercion-preserving specialization | `ExactCIs.Unconditional.ORNull.parameterization` | real `psi>0`, real `q in [0,1]` | Boschloo | OR mass builder |
| `U-OR-MASS-001` | equation OR-MASS with transformed-group exponent | `ExactCIs.Unconditional.ORNull.massIdentity` | `U-OR-NULL-001` | Boschloo | OR objective builder |
| `U-OR-BERN-001` | fixed-mask OR probability has a continuous real common-degree Bernstein ratio with positive denominator; rational specialization has rational coefficients | `ExactCIs.Unconditional.ORNull.bernsteinRatio` | exact fixed mask, real `psi>0` | Boschloo | OR coefficients |
| `U-OR-CONTROL-001` | ratio of common-degree control coefficients is the conditional rejection probability | `ExactCIs.Unconditional.ORNull.controlRatio` | fixed mask, total index | Boschloo | coefficient oracle |
| `U-NUISANCE-CONT-001` | every fixed-mask null objective is continuous on the full real compact nuisance interval | `ExactCIs.Unconditional.ORNull.continuous` | real finite effect, fixed mask | Boschloo | threshold bridge |
| `U-ATTAIN-001` | the nuisance supremum is attained and equals the `exists q`/`forall q` exact threshold decisions, including equality | `ExactCIs.Unconditional.ThresholdDecision.maximumAttained` | `U-NUISANCE-CONT-001`, compact interval | Boschloo | fixed-null decision |
| `U-BOSCH-ORDER-001` | Fisher tails define inclusive total preorders independent of `q` at each finite real OR | `ExactCIs.Unconditional.BoschlooOrdering.totalPreorder` | real `psi>0` | Boschloo | mask builder |
| `U-BOSCH-REP-001` | the rational exact comparator agrees after coercion with the corresponding real Boschloo ordering | `ExactCIs.Unconditional.BoschlooOrdering.rationalCoercion` | reduced rational `psi>0` | Boschloo | executable comparator |
| `U-BOSCH-BREAKPOINT-001` | the signed `(0,2)` versus `(1,3)` comparator has numerator, unique positive root, and mask-side orientation fixed in B.18 | `ExactCIs.Unconditional.BoschlooOrdering.signedBreakpointAnchor` | `n1=n0=4`, `psi>0`, direction `less` | Boschloo | comparator oracle and mutation gate |
| `U-BOSCH-SWAP-001` | group swap maps finite `psi` to `1/psi`, reverses direction, carries the actual finite masks by the reciprocal equivalence, and extends to the structural map `0 <-> +infinity` with reversed endpoint pairs | `ExactCIs.Unconditional.BoschlooOrdering.groupSwap` and `.groupSwapFiniteMask` | positive group totals; finite real `psi` or one tagged OR endpoint | Boschloo | finite and structural metamorphic checks |
| `U-MASK-001` | mask inclusion implies pointwise and supremum probability bounds | `ExactCIs.Unconditional.MaskBounds.sandwich` | normalized finite masses | Boschloo | ambiguity protocol |
| `U-THRESH-001` | positive-denominator threshold comparison equals the sign of `H` on the full real nuisance interval | `ExactCIs.Unconditional.ThresholdDecision.orEquiv` | decoded rational side level, real `q` | Boschloo | fixed-null decision |
| `U-BERN-CERT-001` | coefficient hulls and de Casteljau leaves give sound local signs | `ExactCIs.Unconditional.BernsteinSubdivision.signSound` | exact coefficients | Boschloo | fast certificate path |
| `U-ROOT-CERT-001` | the checker is sound and a checked normalized root/sign certificate exists for every rational polynomial and rational closed interval, including zero polynomials, endpoint/even roots, tangency, and degree drops | `ExactCIs.Unconditional.RootSignCertificate.checkerSound` and `.existsComplete` | canonical polynomial normalization and valid rational interval | Boschloo | completeness path/verifier |
| `U-EXACT-P-001` | nuisance supremum of inclusive principal ordered p-values is super-uniform at every finite positive effect | `ExactCIs.Unconditional.ExactPValueValidity.superUniform` | one total preorder or nested inclusive principal family; q-independent masks; real `psi>0` | Boschloo | finite-positive coverage branch |
| `U-COVER-001` | the ideal procedure has coverage at least `1-alpha` on the complete extended OR domain: `U-EXACT-P-001` supplies the finite-positive branch and `U-STRUCT-OR-VALID-001` supplies the tagged structural branches. `U-HULL-001` supplies ordinary returned-hull containment and `U-FULL-001` supplies the exact full-domain return, so all certified returns satisfy `P(return and miss)<=alpha`; cross-sectional mixing is split into ideal and returned-event lemmas | `ExactCIs.Unconditional.ExactPValueValidity.centralCoverage` | generic/ordinary alpha domains; complete extended-domain case split; `U-EXACT-P-001` twice on finite `psi>0`; `U-STRUCT-OR-VALID-001` at `0,+infinity`; `U-XSEC-001`; and (`U-HULL-001` or `U-FULL-001`) plus `U-XSEC-RETURN-001` for the returned-event clause | Boschloo | public calibration |
| `U-STRUCT-OR-001` | B.9's OR support predicates, ordered endpoint pairs, inclusive threshold-derived classification, and zero-alpha acceptance hold exactly | `ExactCIs.Unconditional.Structural.orEndpoints` | positive group totals; Boschloo OR only; `alpha_side in [0,1]` | Boschloo | endpoint dispatch |
| `U-STRUCT-OR-VALID-001` | on the zero fibre `p1=0 or p0=1`, `P(a=0 or d=0)=1`; on the infinity fibre `p0=0 or p1=1`, `P(c=0 or b=0)=1`. B.9 therefore makes true structural-endpoint rejection probability zero at positive side level and identically absent at zero side level | `ExactCIs.Unconditional.Structural.orFibreSupportAlmostSure` and `.orFibreTwoSidedValidity` | positive group totals; product-binomial structural fibres; B.9 endpoint contract; `alpha_side in [0,1]` | Boschloo | complete-domain coverage bridge |
| `U-STRUCT-OR-MASK-001` | for every unsupported observed `TableAt n1 n0` there is one finite endpoint neighbourhood: for all `0<psi<=delta`, every candidate in the actual finite `R_greater(psi)` mask satisfies `min(x,n0-y) >= min(a,d)`; for all `psi>=M`, every candidate in the actual finite `R_less(psi)` mask satisfies `min(y,n1-x) >= min(c,b)` | `ExactCIs.Unconditional.BoschlooOrdering.eventualZeroGreaterMaskStratum` and `.eventualPositiveInfinityLessMaskStratum` | fixed positive margins; unsupported observed endpoint; inclusive finite Fisher-tail ordering; one `delta`/`M` before all finite effects and candidates; nuisance-independent masks | Boschloo | endpoint tail valuation and mask replay |
| `U-STRUCT-OR-LIMIT-001` | consuming the eventual finite-mask theorems and the OR mass identity, unsupported zero and infinity endpoints have nuisance-uniform event-mass and nuisance-supremum bounds `finiteP(greater,psi) <= C0*psi^min(a,d)` near zero and `finiteP(less,psi) <= Cinf/psi^min(c,b)` near infinity, so the specified directional limits are zero | `ExactCIs.Unconditional.Structural.orEndpointUniformLimits` | `U-STRUCT-OR-MASK-001`, `U-OR-MASS-001`, the defined `finiteMaskMass`, and its real-continuum `finiteP` supremum; positive group totals; constants independent of nuisance | Boschloo | complete-domain endpoint composition |
| `U-MOVING-USC-001` | each exact nuisance-maximized directional p-value is upper semicontinuous over the complete compact effect domain under inclusive moving-mask ownership, interior USC, and the B.9 endpoint valuations and uniform limits | `ExactCIs.Unconditional.GlobalInversion.movingPUpperSemicontinuous` | exact comparator regions, inclusive ties, maximum attainment, interior-stratum continuity, `U-STRUCT-OR-001`, `U-STRUCT-OR-MASK-001`, `U-STRUCT-OR-LIMIT-001` | Boschloo | global topology and cell classifier |
| `U-ACCEPTED-CLOSED-001` | the two-sided accepted set `A_s={p_greater>=r} intersect {p_less>=r}` is closed in the compact effect domain | `ExactCIs.Unconditional.GlobalInversion.acceptedSetClosed` | `U-MOVING-USC-001`, exact inclusive threshold, structural composition | Boschloo | ideal hull/topology |
| `U-EFFECT-MASK-001` | cell lower/upper masks enclose every point mask over every real effect in the cell | `ExactCIs.Unconditional.GlobalInversion.maskCell` | canonical real-effect cell | Boschloo | global classifier |
| `U-EFFECT-QUANT-001` | whole-cell accept/reject certificates have the quantifiers in B.11 | `ExactCIs.Unconditional.GlobalInversion.cellDecision` | sound mask cells/objective bounds over real effects | Boschloo | global classifier |
| `U-INNER-OUTER-001` | a complete sound partition with no unresolved successful leaf implies `I subseteq A_s subseteq O` | `ExactCIs.Unconditional.GlobalInversion.innerOuter` | allowed leaf states, complete ownership, no unresolved omission | Boschloo | partition/verifier |
| `U-COMPLETION-001` | checked adaptive replay either yields a complete sound partition or a named fail-closed terminal; effect-only subdivision or degree-elevation stall must switch to nuisance refinement, exact fallback, or refusal | `ExactCIs.Unconditional.GlobalInversion.adaptiveCompletion` | deterministic finite budgets and checked transition relation | Boschloo | scheduler, replay, and refusal |
| `U-HULL-001` | T1-min and the compact/beta bridge prove ideal-hull containment and both finite beta-space endpoint-excess bounds, with exact structural branches and without component matching | `ExactCIs.Unconditional.GlobalInversion.t1MinHull` | `U-INNER-OUTER-001`, `U-HULL-TRANSPORT-001`, nonempty `I`, exact `hull_endpoint_excess_tolerance`, bounded finite extents or exact structural discharge | Boschloo | `HULL_CERTIFIED` and tuple conversion |
| `U-EMPTY-001` | a complete sound outer enclosure with `A_s subseteq O` and `O=empty` proves mathematical emptiness | `ExactCIs.Unconditional.GlobalInversion.certifiedEmpty` | complete partition and empty `O` | Boschloo | `EmptyConfidenceSetError` branch |
| `U-FULL-001` | a complete inner certificate equal to the compact effect domain proves every effect accepted | `ExactCIs.Unconditional.GlobalInversion.certifiedFull` | `I=domain` and `I subseteq A_s` | Boschloo | exact `(0.0, inf)` branch |
| `U-TOPOLOGY-001` | complete component and gap classification or matching licenses topology claims beyond T1-min | `ExactCIs.Unconditional.GlobalInversion.topologyCertified` | `U-HULL-001` plus stronger component/gap premises | Boschloo | optional `TOPOLOGY_CERTIFIED` evidence only |
| `U-FLOAT-001` | directed binary64 conversion is outward, preserves structural tags, and remains inside the certified beta-space budget | software-only replay obligation | exact hull bounds and B.12 conversion record | Boschloo | public tuple conversion and artifact replay |

Theorems do not by themselves verify Python scheduling, serialization, resource
limits, memory use, or binary64 behaviour. Runtime consumers must check every
hypothesis and record the mapping in the certificate.

`U-MANIFEST-001` and `U-FLOAT-001` are software-only correspondence
obligations. In particular, float tests and replay reconstruct B.12 from the
recorded exact bounds, verify IEEE-754 bit patterns and rational witnesses, and
force underflow, overflow, wrong-direction, and error-budget mutations to fail.

#### B.16.1 Theorem dependency DAG

```text
U-MANIFEST-001

U-DESIGN-001 -> U-OR-NULL-001 -> U-OR-MASS-001 -> U-OR-BERN-001
                    |                 |                 |
                    v                 v                 v
              U-OR-CORNER-001   U-OR-CONTROL-001  U-THRESH-001
                    |                                   |
                    `-> U-NUISANCE-CONT-001 -> U-ATTAIN-001

U-BOSCH-ORDER-001 -> U-BOSCH-REP-001 -> U-MASK-001
          |                    |              |
          |                    |              `-----------------.
          |                    |                                |
          |                    |-> U-BOSCH-BREAKPOINT-001       |
          |                    `-> U-BOSCH-SWAP-001              |
          |                                                     |
FIXED-NULL-BASE = U-OR-MASS-001 + U-THRESH-001 + U-ATTAIN-001
                + U-BOSCH-REP-001 + U-MASK-001
FIXED-NULL-EVIDENCE = exact witness acceptance
                   OR U-BERN-CERT-001 sound fast sign proof
                   OR U-ROOT-CERT-001 complete root/sign proof
FIXED-NULL-BASE + FIXED-NULL-EVIDENCE -> fixed-null exact decisions

U-DESIGN-001 + U-BOSCH-ORDER-001 -> U-EXACT-P-001
U-EXACT-P-001 twice -> finite-positive ideal coverage

U-DESIGN-001 + U-STRUCT-OR-001
    -> U-STRUCT-OR-VALID-001 -> zero/infinity ideal coverage

U-EFFECT-001 partitions the complete extended OR domain:
    finite positive uses finite-positive ideal coverage;
    zero or positive infinity uses zero/infinity ideal coverage.
The complete-domain case split -> fixed-positive-total ideal coverage
fixed-positive-total ideal coverage + U-XSEC-001
    -> ideal branch of U-COVER-001

U-EFFECT-001 -> U-HULL-TRANSPORT-001
U-BOSCH-ORDER-001 + B.9 endpoint support pairs
    -> U-STRUCT-OR-001 -> U-STRUCT-OR-MASK-001
U-STRUCT-OR-MASK-001 + U-OR-MASS-001
    -> U-STRUCT-OR-LIMIT-001
U-BOSCH-SWAP-001 + U-STRUCT-OR-001
    -> structural reciprocal/direction-reversal metamorphics
U-BOSCH-SWAP-001 + U-STRUCT-OR-MASK-001
    -> reciprocal finite-mask transport for the infinity theorem
U-BOSCH-REP-001 + U-ATTAIN-001 + U-OR-CORNER-001 + U-STRUCT-OR-001
        + U-STRUCT-OR-LIMIT-001
    -> U-MOVING-USC-001 -> U-ACCEPTED-CLOSED-001

fixed-null exact decisions + U-EFFECT-001 + U-OR-CORNER-001
        + U-STRUCT-OR-001 + U-STRUCT-OR-LIMIT-001 + U-MOVING-USC-001
        + U-EFFECT-MASK-001
        -> U-EFFECT-QUANT-001 -> U-COMPLETION-001
        -> U-INNER-OUTER-001
                |-> U-EMPTY-001
                |-> U-FULL-001
                `-> U-HULL-001 (also consumes U-HULL-TRANSPORT-001)

U-HULL-001 -> U-FLOAT-001
U-FULL-001 -> exact full tuple + U-FLOAT-001
ideal branch of U-COVER-001 + (U-HULL-001 OR U-FULL-001)
    -> fixed-positive-total returned-event bound
    + U-XSEC-RETURN-001 -> returned-event branch of U-COVER-001
U-HULL-001 + U-ACCEPTED-CLOSED-001
    -> U-TOPOLOGY-001 (strict strengthening only)
```

The fixed-null certificate path and global path must consume the applicable U1
oracle and U2 attacks before their issue can close. Bernstein and root/sign are
alternative sound evidence routes joined explicitly with the shared fixed-null
base, not a serial implication. Empty, full, and hull are sibling terminal
branches; in particular certified emptiness never consumes the nonempty-inner
premise of T1-min. Ideal cross-sectional mixing does not consume a returned
enclosure; returned-event mixing does. `U-TOPOLOGY-001` is not an ancestor of
`U-HULL-001`.

#### B.16.2 Hard-proof route and required infrastructure

1. Model the product sample space as a finite type, prove nonnegative normalized
   masses by finite sums and the binomial theorem, and state validity first over
   real probabilities. Rational arithmetic is a coercion-preserving executable
   specialization, not the statistical domain.
2. Prove denominator positivity on each closed interior effect stratum. Use real
   continuity plus compactness of `[0,1]` to obtain maximum attainment. For an
   unsupported zero observation, first prove one `delta>0` such that **for every
   finite** `0<psi<=delta` every candidate in the actual
   `R_greater(psi; observed)` mask satisfies
   `min(x,n0-y) >= min(a,d)`; only then derive the nuisance-uniform
   `C0*psi^r0` bound. Reciprocally, for an unsupported infinity observation,
   first prove one `M>1` such that **for every** `psi>=M` every candidate in the
   actual `R_less(psi; observed)` mask satisfies
   `min(y,n1-x) >= min(c,b)`; only then derive the nuisance-uniform
   `Cinf/psi^rinf` bound. The endpoint value one discharges the
   opposite-direction USC case at each endpoint. Compose those endpoint lemmas
   with interior USC;
   never assert continuity on the singular full square or infer a uniform bound
   from finite nuisance enumeration.
3. Define Fisher tail values as exact finite sums. Prove the inclusive total
   preorder and nuisance independence, then prove rational cross-product
   comparison agrees with the real ratio comparison because all denominators
   are positive. The signed breakpoint anchor checks orientation, not just its
   root set.
4. Normalize fixed-mask objectives as exact polynomials. Prove Bernstein hull,
   de Casteljau subdivision, degree elevation, and polynomial-normalization
   identities. Prove both checker soundness and existence of a checked complete
   root/sign certificate for zero polynomials, endpoint roots, repeated/even
   roots, degree drops, and exact tangency.
5. Derive finite-positive ordered-p super-uniformity from nested inclusive
   principal sets. Apply it separately to both directions and use the union
   bound; do not infer it from self-inclusion alone. Separately prove the direct
   product-binomial support identities on both structural fibres, including the
   nonidentified all-failure/all-success corners. Join finite and structural
   validity only through the complete extended-domain case split; never infer
   endpoint coverage from a finite-effect limit or a Fisher preorder.
6. Decompose the effect domain into exact ordering regions with inclusive
   breakpoint ownership. Prove each nuisance-maximized directional p-value is
   upper semicontinuous on interior strata, compose it with B.9's directional
   endpoint pairs and `U-STRUCT-OR-LIMIT-001`, and derive closedness of both
   directional superlevel sets and their two-sided intersection. The group-swap
   proof must map zero to infinity and reverse directions; it must not reuse an
   OR endpoint predicate for RR.
7. Represent global cells with explicit ownership and quantify over every real
   effect in the cell. Prove lower/upper-mask soundness, common-effect witnesses
   for acceptance, and one-direction rejection covers. Define a checked
   adaptive transition relation: after effect subdivision or degree elevation
   stalls it must switch to nuisance refinement, invoke the exact completeness
   path, or enter a named fail-closed terminal. Only a replayed complete
   partition may feed hull results.
8. Prove the compact/beta order isomorphism and its nonempty-set hull-transport
   theorem. Then prove T1-min using `Set` inclusion, bounded finite
   `sInf`/`sSup`, monotonicity of `b(s)=s/(1-s)` on interior strata, and a
   separate tagged structural endpoint split. Prove empty/full terminal
   theorems separately. Closedness plus component and gap lemmas feed only the
   stronger topology theorem.

Expected Mathlib foundations include finite sums and `Nat.choose`, ordered-field
cross multiplication, `Rat.cast`, `Polynomial`, real continuity, compactness,
`Set` inclusion and bounds, and extended-endpoint representations. Project-owned
infrastructure is still required for normalized Bernstein polynomials,
de Casteljau and elevation checkers, exact root/sign certificate replay,
cell-ownership trees, and the concrete finite/structural T1-min composition.
Absence of that infrastructure blocks the theorem; it does not license a weaker
statement.

#### B.16.3 Named adversarial attacks and attacked premises

| named attack | premise or claim it attacks | required consumer |
|---|---|---|
| exact equality tangency and even-multiplicity root | strict rejection, maximum attainment, complete root/sign checking | `U-ATTAIN-001`, `U-THRESH-001`, `U-ROOT-CERT-001` |
| signed ordering breakpoint near `2.9286857509700537` | comparator sign orientation and inclusive equality | `U-BOSCH-REP-001`, `U-BOSCH-BREAKPOINT-001` |
| nuisance-dependent-mask mutation | nuisance independence of the fixed-effect preorder | `U-BOSCH-ORDER-001`, `U-EXACT-P-001` |
| asymmetric moving-witness fixture | reversal of `forall effect, exists nuisance` into one reused witness | `U-EFFECT-QUANT-001` |
| directional rejection-cover fixture | combining failures from different directions or effect points | `U-EFFECT-QUANT-001` |
| effect-only subdivision and degree-elevation stalls | false adaptive completion or silent leaf loss | `U-COMPLETION-001`, `U-INNER-OUTER-001` |
| moving-mask equality boundary | loss of upper semicontinuity or closed accepted-set membership | `U-MOVING-USC-001`, `U-ACCEPTED-CLOSED-001` |
| disconnected accepted set | assumed connectedness, first crossing, or discarded interior outer cells | `U-ACCEPTED-CLOSED-001`, `U-INNER-OUTER-001`, `U-HULL-001` |
| denominator corners `(0,1)` and `(1,0)` | an invalid full-square continuity argument | `U-OR-CORNER-001`, `U-STRUCT-OR-001` |
| exact `n1=n0=1`, `(a,c)=(1,0)` rational-square anchor | reversed `(p_greater,p_less)` order, a false `(0,0)` endpoint pair, or an incorrect reciprocal group swap | `U-STRUCT-OR-001`, `U-BOSCH-SWAP-001` |
| structural-fibre validity mutation | direct endpoint valuation treated as finite ordered-p validity; an `or` fibre/support predicate weakened to `and`; a structural corner assigned one unique true OR | `U-STRUCT-OR-VALID-001`, `U-COVER-001` |
| zero-alpha and support-predicate mutations | level-independent endpoint rejection, `and` in place of the required `or`, or endpoint pairs used outside OR/Boschloo | `U-STRUCT-OR-001`, `U-STRUCT-OR-VALID-001` |
| eventual finite-mask, mass-link, or nuisance-uniformity mutation | a tagged endpoint mask or unrelated tail quantity substituted for one `delta`/`M` neighbourhood of actual finite masks and their defined product-binomial event mass; finite sampling substituted for the zero/infinity tail valuation or complete-domain limit | `U-STRUCT-OR-MASK-001`, `U-STRUCT-OR-LIMIT-001`, `U-MOVING-USC-001` |
| unmatched extreme sliver | matching-as-soundness and unbounded endpoint excess | `U-HULL-001` |
| unmatched interior outer component | accidental topology claim from a hull certificate | `U-TOPOLOGY-001` |
| certified empty/full mutations | conflation of mathematical results with unresolved or resource failure | `U-EMPTY-001`, `U-FULL-001` |

#### B.16.4 Lean-ready signatures and coercion boundaries

The following are exact declaration-head contracts for the issue-owned Lean
tranches, not already-proved declarations. `CompactEffect` is the subtype
`Set.Icc (0:Real) 1`; `BetaEffect` is the extended nonnegative real type;
`Structural.effectOrderIso : CompactEffect ≃o BetaEffect` implements B.11.
`InclusiveOrderedPModel` contains a finite normalized mass, one inclusive total
preorder, its nested principal sets, and the nuisance-independent-mask proof.
`CrossSectionalMixture` contains nonnegative group-total weights summing to one,
the positive-total conditional ideal-miss and return-and-miss probabilities,
their weighted mixed events, and proof that zero-total observations never
return. Its ideal theorem consumes only conditional ideal bounds; its returned
theorem separately consumes conditional return-and-miss bounds.
`StructuralOREndpoint` has exactly the tagged values `zero` and
`positiveInfinity`; `Structural.ORFibre endpoint p1 p0` is respectively
`p1=0 or p0=1` and `p0=0 or p1=1`; and `Structural.supports` is exactly B.9's
disjunctive observed-table support predicate. `TableAt n1 n0` is the
fixed-margin candidate type with success coordinates `x<=n1`, `y<=n0`.
`BoschlooOrdering.finiteMask z dir psi` is exactly B.5's inclusive finite-
`psi` mask over `TableAt n1 n0`, never an endpoint-tagged auxiliary mask.
For `0<psi` and `q in [0,1]`, its product-binomial law is the finite OR
parameterisation

```text
p0(psi,q) = q;
p1(psi,q) = psi*q / (1-q+psi*q).
```

Write `mu[psi,q]` for `ProductBinomial.mass n1 n0 p1(psi,q) p0(psi,q)` and
freeze the only admissible finite directional probability objects as

```text
finiteMaskMass(z,dir,psi,q)
    = mu[psi,q]({candidate in TableAt n1 n0 |
                   candidate in BoschlooOrdering.finiteMask z dir psi});

finiteP(z,dir,psi)
    = sup_{q in [0,1]} finiteMaskMass(z,dir,psi,q).
```

`TableAt.of table` is the exact coordinate-preserving bridge from a valid
positive-total table to its fixed-margin candidate type. In particular, a
generic `BoschlooDirectionalTail` name is not an admissible substitute for
`finiteMaskMass`: the U-STRUCT-OR limit theorems must state bounds on this
defined finite-mask event mass and then on its real-continuum nuisance
supremum.
`MovingMaskModel` contains a finite exact ordering-region cover of the compact
effect domain, a fixed nuisance-independent mask on every open region, inclusive
tie ownership on each algebraic boundary, the attained nuisance-maximized
directional objective, interior-stratum continuity proofs, and separate B.9
endpoint-pair, eventual finite-mask, and nuisance-uniform-limit certificates. Its
endpoint fields are tagged zero/infinity data, never coercions through the
finite formula; its `twoSidedAcceptedSet` is exactly the intersection of the
two inclusive directional superlevel sets.

For a cell `C`, threshold `r`, and directional objectives `P_g,P_l`, the fields
of `CellDecisionGuarantee` are frozen by its outcome:

```text
ACCEPTED:
    (for every s in C, there exists q_g in [0,1], P_g(s,q_g) >= r)
and (for every s in C, there exists q_l in [0,1], P_l(s,q_l) >= r).

REJECTED_GREATER:
    for every s in C and q in [0,1], P_g(s,q) < r.

REJECTED_LESS:
    for every s in C and q in [0,1], P_l(s,q) < r.

BOUNDARY_ENCLOSURE:
    C is retained in O and is not inserted into I or classified rejected.
```

The accepted witnesses may differ by effect and direction. The two rejected
outcomes each use one fixed direction across the complete cell.

For nonempty `I`, write `lS=lower_s` and `uS=upper_s`. The fields of
`T1EndpointPremises A I O epsilon` are exactly:

```text
epsilon_nonnegative: 0 <= epsilon;
inner_nonempty:       I is nonempty;
inner_outer:          I subseteq A subseteq O;

lower_branch: exactly one of
  FINITE:
    0 < lS(O), lS(I) < 1,
    b_ext(lS(I)) - b_ext(lS(O)) <= epsilon;
  STRUCTURAL(e), e in {0,1}:
    e in I, lS(O)=e, lS(I)=e;

upper_branch: exactly one of
  FINITE:
    0 < uS(I), uS(O) < 1,
    b_ext(uS(O)) - b_ext(uS(I)) <= epsilon;
  STRUCTURAL(e), e in {0,1}:
    e in I, uS(O)=e, uS(I)=e.
```

Because `I subseteq A subseteq O`, the structural fields also put `e` in `A`.
The fields of `HullGuarantee A O epsilon` are ideal-hull containment and,
respectively, the conclusions

```text
b_ext(lower_s(A)) - b_ext(lower_s(O)) <= epsilon,
b_ext(upper_s(O)) - b_ext(upper_s(A)) <= epsilon,
```

on finite branches; a structural branch concludes equality of the corresponding
`A` and `O` extrema to the same `e` and returns exactly `b_ext(e)`. Here the
Lean parameter `A` denotes the compact accepted set called `A_s` elsewhere in
this specification. Thus the T1 inequalities are consumed to prove endpoint
excess, rather than merely repeated as unused theorem hypotheses.

`AdaptiveCompletionGuarantee` has three fields: every checked `SUCCESS` owns a
complete sound partition with no unresolved omission; a stalled effect split or
degree elevation is followed only by nuisance refinement, the exact completeness
path, or named refusal; and every finite-budget replay terminates in `SUCCESS`,
`RESOURCE_EXHAUSTED`, or `UNRESOLVED`. `TopologyGuarantee` separately owns every
component and interior gap. These field definitions are part of the signatures;
the formal package may not replace them with opaque propositions.

```lean
-- #48: finite probability, compact attainment, and ordered-p validity.
#check @ProductBinomial.mass_sum :
  ∀ (n1 n0 : Nat) (p1 p0 : Real),
    p1 ∈ Set.Icc 0 1 → p0 ∈ Set.Icc 0 1 →
    (ProductBinomial.mass n1 n0 p1 p0).normalizes

#check @ThresholdDecision.maximumAttained :
  ∀ (objective : Real → Real),
    ContinuousOn objective (Set.Icc 0 1) →
    ∃ q ∈ Set.Icc (0 : Real) 1,
      ∀ u ∈ Set.Icc (0 : Real) 1, objective u ≤ objective q

#check @Structural.zeroDirectionalP :
  ∀ (table : Table), PositiveGroupTotals table →
    Structural.directionalP table .zero =
      if table.a = 0 ∨ table.d = 0 then ((1 : Real), 1) else (0, 1)

#check @Structural.positiveInfinityDirectionalP :
  ∀ (table : Table), PositiveGroupTotals table →
    Structural.directionalP table .positiveInfinity =
      if table.c = 0 ∨ table.b = 0 then ((1 : Real), 1) else (1, 0)

#check @Structural.orEndpoints :
  ∀ (table : Table) (alpha_side : Real), PositiveGroupTotals table →
    0 ≤ alpha_side → alpha_side ≤ 1 →
    (Structural.directionalP table .zero =
        if table.a = 0 ∨ table.d = 0 then ((1 : Real), 1) else (0, 1)) ∧
    (Structural.directionalP table .positiveInfinity =
        if table.c = 0 ∨ table.b = 0 then ((1 : Real), 1) else (1, 0)) ∧
    (Structural.accepts (Structural.directionalP table .zero) alpha_side ↔
      ((Structural.directionalP table .zero).1 ≥ alpha_side ∧
       (Structural.directionalP table .zero).2 ≥ alpha_side)) ∧
    (Structural.accepts (Structural.directionalP table .positiveInfinity)
        alpha_side ↔
      ((Structural.directionalP table .positiveInfinity).1 ≥ alpha_side ∧
       (Structural.directionalP table .positiveInfinity).2 ≥ alpha_side)) ∧
    (alpha_side = 0 →
      Structural.accepts (Structural.directionalP table .zero) alpha_side ∧
      Structural.accepts (Structural.directionalP table .positiveInfinity)
        alpha_side)

#check @Structural.orFibreSupportAlmostSure :
  ∀ {n1 n0 : Nat} {endpoint : StructuralOREndpoint} {p1 p0 : Real},
    0 < n1 → 0 < n0 →
    p1 ∈ Set.Icc (0 : Real) 1 → p0 ∈ Set.Icc (0 : Real) 1 →
    Structural.ORFibre endpoint p1 p0 →
    (ProductBinomial.mass n1 n0 p1 p0).eventMass
      {outcome | ¬ Structural.supports endpoint (Outcome.toTable n1 n0 outcome)} = 0

#check @Structural.orFibreTwoSidedValidity :
  ∀ {n1 n0 : Nat} {endpoint : StructuralOREndpoint} {p1 p0 r : Real},
    0 < n1 → 0 < n0 →
    p1 ∈ Set.Icc (0 : Real) 1 → p0 ∈ Set.Icc (0 : Real) 1 →
    Structural.ORFibre endpoint p1 p0 → 0 ≤ r → r ≤ 1 →
    (ProductBinomial.mass n1 n0 p1 p0).eventMass
      {outcome | ¬ Structural.accepts
        (Structural.directionalP (Outcome.toTable n1 n0 outcome) endpoint) r} = 0

#check @ExactPValueValidity.superUniform :
  ∀ {Omega : Type} [Fintype Omega] [DecidableEq Omega]
    (model : InclusiveOrderedPModel Omega) (alpha : Real),
    0 ≤ alpha → alpha ≤ 1 →
    model.mass.eventMass (model.strictSublevel alpha) ≤ alpha

#check @ProductBinomial.crossSectionalIdealMix :
  ∀ (model : CrossSectionalMixture) (alpha : Real),
    (∀ n1 n0 : Nat, 0 < n1 → 0 < n0 →
      model.conditionalIdealMiss n1 n0 ≤ alpha) →
    model.mixedIdealMiss ≤ alpha

#check @ProductBinomial.crossSectionalReturnMix :
  ∀ (model : CrossSectionalMixture) (alpha : Real),
    (∀ n1 n0 : Nat, 0 < n1 → 0 < n0 →
      model.conditionalReturnMiss n1 n0 ≤ alpha) →
    model.mixedReturnMiss ≤ alpha

-- #51: coercion-preserving comparator and checked sign certificates.
#check @BoschlooOrdering.rationalCoercion :
  ∀ (psi : ℚ), 0 < psi → ∀ (x y : Table),
    BoschlooOrdering.exactCompare psi x y =
      BoschlooOrdering.realCompare (psi : Real) x y

#check @BoschlooOrdering.signedBreakpointAnchor :
  BoschlooOrdering.breakpointNumerator =
    16 * Polynomial.X + 46 * Polynomial.X ^ 2 - 6 * Polynomial.X ^ 4

#check @BoschlooOrdering.eventualZeroGreaterMaskStratum :
  ∀ {n1 n0 : Nat} (observed : TableAt n1 n0),
    0 < observed.x → 0 < n0 - observed.y →
    ∃ delta : Real, 0 < delta ∧ delta ≤ 1 ∧
      ∀ (psi : Real), 0 < psi → psi ≤ delta →
        ∀ candidate : TableAt n1 n0,
          candidate ∈ BoschlooOrdering.finiteMask observed .greater psi →
            min candidate.x (n0 - candidate.y) ≥
              min observed.x (n0 - observed.y)

#check @BoschlooOrdering.eventualPositiveInfinityLessMaskStratum :
  ∀ {n1 n0 : Nat} (observed : TableAt n1 n0),
    0 < observed.y → 0 < n1 - observed.x →
    ∃ M : Real, 1 < M ∧
      ∀ (psi : Real), M ≤ psi →
        ∀ candidate : TableAt n1 n0,
          candidate ∈ BoschlooOrdering.finiteMask observed .less psi →
            min candidate.y (n1 - candidate.x) ≥
              min observed.y (n1 - observed.x)

#check @BoschlooOrdering.groupSwapFiniteMask :
  ∀ {n1 n0 : Nat} (observed candidate : TableAt n1 n0) (psi : Real),
    0 < psi →
    (candidate ∈ BoschlooOrdering.finiteMask observed .less psi ↔
      TableAt.groupSwap candidate ∈ BoschlooOrdering.finiteMask
        (TableAt.groupSwap observed) .greater psi⁻¹)

#check @BoschlooOrdering.groupSwapStructural :
  ∀ (table : Table), PositiveGroupTotals table →
    Structural.directionalP (Table.groupSwap table) .positiveInfinity =
      Direction.reversePair (Structural.directionalP table .zero) ∧
    Structural.directionalP (Table.groupSwap table) .zero =
      Direction.reversePair (Structural.directionalP table .positiveInfinity)

-- #48 endpoint continuation: these bounds explicitly consume the preceding
-- eventual finite-mask theorems plus U-OR-MASS-001; a tagged endpoint mask is
-- not an admissible replacement premise.
#check @BoschlooOrdering.finiteMaskMass_eq :
  ∀ {n1 n0 : Nat} (observed : TableAt n1 n0) (direction : Direction)
    (psi q : Real), 0 < psi → q ∈ Set.Icc (0 : Real) 1 →
    BoschlooOrdering.finiteMaskMass observed direction psi q =
      (ProductBinomial.mass n1 n0
        (psi * q / (1 - q + psi * q)) q).eventMass
        {candidate | candidate ∈
          BoschlooOrdering.finiteMask observed direction psi}

#check @BoschlooOrdering.finiteP_eq :
  ∀ {n1 n0 : Nat} (observed : TableAt n1 n0) (direction : Direction)
    (psi : Real), 0 < psi →
    BoschlooOrdering.finiteP observed direction psi =
      sSup (BoschlooOrdering.finiteMaskMass observed direction psi ''
        Set.Icc (0 : Real) 1)

#check @Structural.zeroUnsupportedFiniteMaskMassBound :
  ∀ {n1 n0 : Nat} (observed : TableAt n1 n0),
    0 < observed.x → 0 < n0 - observed.y →
    ∃ C delta : Real, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
      ∀ (psi q : Real), 0 < psi → psi ≤ delta → q ∈ Set.Icc (0 : Real) 1 →
        BoschlooOrdering.finiteMaskMass observed .greater psi q ≤
          C * psi ^ min observed.x (n0 - observed.y)

#check @Structural.zeroUnsupportedFinitePBound :
  ∀ {n1 n0 : Nat} (observed : TableAt n1 n0),
    0 < observed.x → 0 < n0 - observed.y →
    ∃ C delta : Real, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
      ∀ (psi : Real), 0 < psi → psi ≤ delta →
        BoschlooOrdering.finiteP observed .greater psi ≤
          C * psi ^ min observed.x (n0 - observed.y)

#check @Structural.positiveInfinityUnsupportedFiniteMaskMassBound :
  ∀ {n1 n0 : Nat} (observed : TableAt n1 n0),
    0 < observed.y → 0 < n1 - observed.x →
    ∃ C M : Real, 0 < C ∧ 1 < M ∧
      ∀ (psi q : Real), M ≤ psi → q ∈ Set.Icc (0 : Real) 1 →
        BoschlooOrdering.finiteMaskMass observed .less psi q ≤
          C / psi ^ min observed.y (n1 - observed.x)

#check @Structural.positiveInfinityUnsupportedFinitePBound :
  ∀ {n1 n0 : Nat} (observed : TableAt n1 n0),
    0 < observed.y → 0 < n1 - observed.x →
    ∃ C M : Real, 0 < C ∧ 1 < M ∧
      ∀ (psi : Real), M ≤ psi →
        BoschlooOrdering.finiteP observed .less psi ≤
          C / psi ^ min observed.y (n1 - observed.x)

#check @Structural.orEndpointUniformLimits :
  ∀ {n1 n0 : Nat} (observed : TableAt n1 n0),
    (0 < observed.x → 0 < n0 - observed.y →
      ∃ C delta : Real, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ (psi : Real), 0 < psi → psi ≤ delta →
          BoschlooOrdering.finiteP observed .greater psi ≤
            C * psi ^ min observed.x (n0 - observed.y)) ∧
    (0 < observed.y → 0 < n1 - observed.x →
      ∃ C M : Real, 0 < C ∧ 1 < M ∧
        ∀ (psi : Real), M ≤ psi →
          BoschlooOrdering.finiteP observed .less psi ≤
            C / psi ^ min observed.y (n1 - observed.x))

#check @RootSignCertificate.checkerSound :
  ∀ (certificate : RootSignCertificate) (polynomial : Polynomial ℚ)
    (interval : RationalInterval),
    checkRootSign certificate polynomial interval = true →
    CertifiedSignClaim certificate polynomial interval

#check @RootSignCertificate.existsComplete :
  ∀ (polynomial : Polynomial ℚ) (interval : RationalInterval),
    interval.IsValid →
    ∃ certificate : RootSignCertificate,
      checkRootSign certificate polynomial interval = true ∧
      certificate.CoversEveryRootAndSignCell polynomial interval

-- #52/#49: compact/beta bridge, cells, T1-min, and terminal branches.
#check @Structural.effectOrderIso : CompactEffect ≃o BetaEffect

#check @Structural.hullTransport :
  ∀ {S : Set CompactEffect}, S.Nonempty →
    Set.image Structural.effectOrderIso (compactHull S) =
      betaHull (Set.image Structural.effectOrderIso S)

#check @GlobalInversion.movingPUpperSemicontinuous :
  ∀ (model : MovingMaskModel) (direction : Direction),
    UpperSemicontinuousOn (model.directionalP direction) Set.univ

#check @GlobalInversion.acceptedSetClosed :
  ∀ (model : MovingMaskModel) (threshold : Real),
    IsClosed (model.twoSidedAcceptedSet threshold)

#check @GlobalInversion.cellDecision :
  ∀ (certificate : CellDecisionCertificate),
    checkCellDecision certificate = true →
    CellDecisionGuarantee certificate

#check @GlobalInversion.t1MinHull :
  ∀ {A I O : Set CompactEffect} {epsilon : ℚ},
    T1EndpointPremises A I O epsilon →
    HullGuarantee A O epsilon

#check @GlobalInversion.adaptiveCompletion :
  ∀ (replay : AdaptiveReplay),
    checkAdaptiveReplay replay = true → AdaptiveCompletionGuarantee replay

#check @GlobalInversion.certifiedEmpty :
  ∀ {A O : Set CompactEffect}, A ⊆ O → O = ∅ → A = ∅

#check @GlobalInversion.certifiedFull :
  ∀ {A I : Set CompactEffect}, I = Set.univ → I ⊆ A → A = Set.univ

#check @GlobalInversion.topologyCertified :
  ∀ (certificate : TopologyCertificate),
    checkTopology certificate = true → TopologyGuarantee certificate
```

Real-valued probability, continuity, supremum, ordering, and coverage theorems
remain over `Real`. Executable effects, alpha values, masks, coefficients, and
certificate witnesses use reduced rationals or integers and require explicit
coercion theorems. `CompactEffect` subtype encoding makes every accepted set a
subset of the effect domain; this is the missing domain premise in the full-set
argument. Binary64 appears only at the checked outward-conversion boundary. The
structural value `s=1` is never coerced through the finite formula `s/(1-s)`.

#### B.16.5 Theorem-to-runtime correspondence

| obligation | Python/runtime evidence | certificate or replay field | unchecked consequence |
|---|---|---|---|
| manifest and design | exact manifest guard; central count/design validation | schema, method, estimand, design | method absent or `DesignError` |
| decoded alpha domains | validate public float, then `as_integer_ratio()` | `alpha_exact`, `alpha_side` | validation failure or `NumericalError` |
| normalized null mass | exact integer/rational construction and mass digest | dimensions, basis, degree, coefficient digests | `NumericalError` |
| cross-sectional ideal/returned mixing | positive-total conditional bounds; zero-total no-return check; separate event accumulators | total-stratum weights and ideal/returned event tags | no cross-sectional claim |
| nuisance-independent inclusive ordering | exact comparator, mask construction, tie and q-independence mutation gates | construction ID, direction, exact tie rule, mask digests | no fixed-null decision |
| rational-to-real comparator agreement | theorem ID plus exact cross-product replay | operands, denominator signs, comparison relation | ordering unresolved; refine or refuse |
| maximum-attained threshold | checked witness or universal root/sign certificate on `[0,1]` | witness/isolating leaves, equality relation | `UNRESOLVED` |
| root/sign completeness | normalize every rational polynomial/interval; replay sound checker; require complete root/sign-cell coverage | normalization digest, roots, multiplicities, sign cells, checker result | exact fallback unresolved; refuse |
| mask sandwich | lower/upper mask digests and subset replay | unresolved comparison count and refinements | refine or refuse |
| structural OR endpoint pair and threshold | direct `or` support predicate, ordered `(p_greater,p_less)` pair, exact decoded side level, inclusive two-direction comparison, and Boschloo-OR-only dispatch | endpoint tag, support result, pair, `alpha_side`, per-direction comparisons, construction ID | no structural classification; never reuse for RR |
| structural-fibre validity and complete-domain coverage bridge | record `U-STRUCT-OR-VALID-001`, positive-group-total branch, endpoint tag, direct `or` support predicate, B.9 pair, and exact decoded side level; cross-sectional execution retains zero-total no-return | structural-fibre theorem ID, endpoint tag, support result, pair, `alpha_side`, positive-total/no-return branch | no complete-domain calibration claim |
| eventual finite endpoint mask and uniform limit | replay one `delta`/`M`, actual finite-mask digests for its certified region, the exact `finiteMaskMass` product-binomial event equation, the `finiteP` nuisance-supremum equation, the common exponent, and the theorem-linked nuisance-uniform bound; finite enumeration is supporting evidence only | finite-mask construction ID, mass-law digest, `delta` or `M`, exponent, constant/region certificate, direction, reciprocal finite-mask replay | no complete-domain USC or global result |
| compact/beta order isomorphism and hull transport | theorem IDs; exact structural tags; rational finite transform and nonempty-hull replay | compact and beta endpoints, membership source, both hulls | no global result |
| moving-mask upper semicontinuity and closedness | replay exact region cover, inclusive breakpoint ownership, interior continuity hypotheses, B.9 endpoint pairs, and `U-STRUCT-OR-MASK-001`/`U-STRUCT-OR-LIMIT-001` composition | region/root digests, endpoint-limit certificate, boundary owners, directional superlevel and two-sided set records | no complete-topology or hull result |
| cell quantifiers | cell-wide lower acceptance witnesses and one-direction upper rejection covers | effect cell, direction, witnesses/covers | leaf remains unresolved |
| adaptive completion | replay every transition; on either named stall require nuisance refinement, exact fallback, or terminal refusal | transition kind, progress measure, counters, stall reason, terminal state | no success state |
| complete inner/outer relation | replay every leaf, ownership edge, and domain cover | complete cell tree, `I`, `O`, unresolved count | no success state |
| T1-min endpoint extents | exact `I/O` extrema, finite beta transforms, `hull_endpoint_excess_tolerance`, structural branch checks | both global endpoint-excess checks and branch kind | refine or `NumericalError` |
| certified empty/full | complete replay plus respectively `O=empty` or `I=domain` | terminal state and complete partition digest | never infer from search failure |
| topology | stronger component/gap replay | topology state and component/gap records | no topology claim; hull may remain valid |
| outward binary64 | exact directed conversion and bit-pattern replay | rational bounds, hex bits, `as_integer_ratio()` witnesses | `NumericalError` |
| deterministic resources | preflight and increment exact counters before work | active limits, counters, exhausted flag | `RESOURCE_EXHAUSTED` |
| policy and internal surface | explicit `method="boschloo"` dispatch; default-Wald and no-public-certificate gates | method key and internal certificate schema | method absent or packaging gate fails |

For every returned interval, all applicable rows must name the contract and
theorem identifiers and replay the corresponding hypothesis. Any hypothesis
without a runtime check, exact construction, checked certificate field, or
replay obligation bars the associated result.

#### B.16.6 Claim ceiling and approval state

This document specifies the statistical identity, domains, quantifiers,
assurance states, proof targets, and runtime obligations. It is U0 authority
only when introduced to `main` by an explicitly owner-approved immutable-head
merge. It does not prove the target theorems, validate a Python implementation,
establish floating-point correctness, coverage in shipped code, performance, or
release readiness.
Private or records-only Lean results remain `formalised-only` until ported,
reviewed, and built in the public issue-owned package.

**Implementation status: blocked.** An approved U0 merge authorizes F0, U1,
U2, and the issue-owned proof work only. Production unconditional Python remains
blocked until #48, #51, #52, and #49 close their applicable Boschloo obligations
and Chey posts an explicit implementation-authority checkpoint.

### B.17 Source and oracle authority

| source class | role | authority ceiling |
|---|---|---|
| this specification and later reviewed amendments | method identity, domains, ties, structural and error contracts | normative statistical definition |
| exact finite-sum proofs and checked formal theorems | distribution, ordering, threshold, validity, partition and hull claims | mathematical authority for their stated hypotheses |
| independent standard-library integer/Fraction oracle | fixtures, counterexamples, exact replay, metamorphics | implementation-independent executable evidence |
| Boschloo (1970) | historical vocabulary and comparison | not production code and not proof of this extension's identity |
| external R, SciPy, or SAS outputs with pinned versions/options/orientation | compatibility records only | never a coverage or certification oracle |
| grids, quasi-random sampling, local/global floating optimizers | discovery and profiling only | never scientific truth |
| private or legacy implementations | failure-mode and candidate-fixture discovery | never ported or used as expected values |

No source under a copyleft implementation licence is translated. Exact
arithmetic is rederived from the mathematical definition.

Primary historical references, used only to identify vocabulary and provenance:

- R. D. Boschloo, ["Raised conditional level of significance for the 2 x 2
  table when testing the equality of two
  probabilities"](https://doi.org/10.1111/j.1467-9574.1970.tb00104.x), 1970.

### B.18 Downstream stage contracts

| stage | required work | stop condition / exit ceiling |
|---|---|---|
| U1 oracle | independent full product-binomial enumeration; exact Fisher comparisons, coefficients, root/sign fixtures, structural/metamorphic corpus, canonical hashes; exhaustive positive group sizes through 12 where feasible | no production import or shared helper; external software remains compatibility-only; measured infeasibility is reported rather than hidden |
| U2 adversaries | strict expected failures for equality tangency, multiple maxima, near ties, endpoint nuisance optima, ordering breakpoints, disconnected accepted sets, structural cases, imbalance, and resource cliffs | scouting grids locate cases but exact U1 evidence defines them; every expected failure names its repairing stage |
| fixed-null proofs | prove all manifest-applicable rows in B.16, including total-preorder validity and exact tangency completion | no admissions, floating equality, weakened quantifiers, or deferred-method work on the Boschloo critical path |
| global specification/proof | freeze and prove cell ownership, quantifiers, boundary enclosures, inner/outer relation, hull and empty/full behaviour | no production inversion before the complete contract is proved |
| U3 fixed-null implementation | exact standard-library masks, common-degree coefficients, threshold/root certificates, deterministic replay, evidence-sized refusal | no grid success path, global inversion, public export, guessed cap, or certificate nondeterminism |
| U4-A global implementation | implement the proved adaptive relation; retain components and valid boundary enclosures; outward float conversion | no transient unresolved leaf on success, point-witness acceptance, mixed-point rejection, first-root assumption, or structural sentinel |
| U4-B integration/release | add only manifest names, registry/docs/gates, implementation correspondence, immutable artifacts | defaults unchanged; existing 1.1.2 results/errors byte-identical; no release until every scientific and artifact gate passes |

#### Frozen U2 adversarial anchors

These exact values are mandatory U2 fixtures. Discovery approximations may find
similar cases but cannot replace their stated masks, roots, or classifications.

| anchor | exact fixture | required conclusion |
|---|---|---|
| multiple maxima | `n1=2`, `n0=4`, `psi=1/4`, observed `(1,0)`, `greater` | three isolated stationary cells of the fixed-null nuisance objective |
| equality tangency | `n1=2`, `n0=3`, `psi=1`, observed `(2,0)`, `greater`, `alpha_side=108/3125` | mask `{(2,0)}`, supremum `108/3125` at `q=2/5`, and `H(2/5)=0` |
| disconnected acceptance | `n1=n0=4`, observed `(0,2)`, `less`, `alpha_side=1/40` | `23/9` accept, `47/17` reject, `3` accept, `25/7` reject |
| ordering breakpoint | `n1=n0=4`, observed `(0,2)`, `less`, candidate `(1,3)` | signed tail difference is positive at `psi=2.9`, zero at the unique positive root near `2.9286857509700537`, and negative at `psi=2.95`; inclusive mask membership is respectively out, in, in |

The tangency anchor requires the exact root/sign completeness path. The
disconnected and breakpoint anchors require the #52/#49 general global path;
they rule out a connectedness or global-monotonicity baseline.

For the ordering-breakpoint anchor, put

```text
T13 = F_less(1,3;psi)
    = (1+16*psi)/(1+16*psi+36*psi^2+16*psi^3+psi^4),
T02 = F_less(0,2;psi)
    = 6/(6+16*psi+6*psi^2).
```

Over their positive common denominator, the **unreduced** cross-product
numerator in the fixed orientation `T13*den02 - T02*den13` is

```text
-2*psi*(3*psi^3 - 23*psi - 8),
```

with ascending coefficients `[0,16,46,0,-6]`. The fully reduced numerator is
`-psi*(3*psi^3-23*psi-8)`; the leading negative orientation is therefore not a
removable convention. The cubic has one positive root

```text
psi_star = 2.9286857509700537...,
29/10 < psi_star < 59/20.
```

Indeed, its derivative is `9*psi^2-23`: the cubic decreases from its negative
value at zero to its only positive critical point and then increases strictly
to positive infinity. The exact bracket signs are
`g(29/10)=-1533/1000` and `g(59/20)=9337/8000`, so this bracket isolates the
unique positive root.

At `psi=2.9`, `T13-T02>0`, so candidate `(1,3)` is not in the inclusive
`less` mask generated by observed `(0,2)`. At `psi=2.95`, the difference is
negative and the candidate is in the mask. At `psi=psi_star`, equality is
included, so the candidate is also in. U1 must independently reconstruct the
rational tails and U2 must freeze canonical bytes; this U0 record fixes the
mathematical orientation and the mutation target, not a production fixture.

<!-- exactcis-unconditional-breakpoint-contract:start -->
```json
{
  "schema": "exactcis.unconditional.breakpoint_contract.v1",
  "group_sizes": [4, 4],
  "observed": [0, 2],
  "direction": "less",
  "candidate": [1, 3],
  "cross_product_orientation": "T13*den02 - T02*den13",
  "unreduced_numerator_factorization": "-2*psi*(3*psi^3-23*psi-8)",
  "ascending_coefficients": [0, 16, 46, 0, -6],
  "unique_positive_root_decimal": "2.9286857509700537",
  "isolating_bracket": [[29, 10], [59, 20]],
  "membership": {
    "29/10": "out",
    "unique_positive_root": "in_by_equality",
    "59/20": "in"
  }
}
```
<!-- exactcis-unconditional-breakpoint-contract:end -->

## C) Assumptions (checkboxes)

Minimal assumptions (needed):

- [x] Counts are central-validated nonnegative integers and both group totals are
  positive.
- [x] The design is independent-binomial, directly or conditionally on positive
  cross-sectional group totals.
- [x] Generic validity uses its stated mathematical alpha domain, ordinary CIs
  use `0 < alpha < 1`, and the executable envelope is only a runtime-capability
  restriction.
- [x] `alpha_exact` and `alpha_side` are decoded exactly from the accepted
  public float's binary rational representation.
- [x] Statistical effects and nuisance coordinates range over their full real
  domains; rationals are certificate representations and witnesses, not grids.
- [x] At fixed effect and direction, the method supplies one common inclusive
  total preorder (or equivalent nested principal family) and its rejection sets
  are nuisance-independent.
- [x] Every successful fixed-null decision is exact or certificate-enclosed;
  equality with the side level is accepted, and real-continuum maximum
  attainment connects the supremum to the decision.
- [x] Every successful global result establishes `I subseteq A_s subseteq O`,
  has no transient unresolved leaf, and may retain `BOUNDARY_ENCLOSURE` rather
  than falsely classify it. A returned nonempty interval also satisfies both
  global T1-min endpoint-excess bounds.
- [x] Structural endpoints are tagged mathematical states, not finite sentinels.
- [x] Resource exhaustion refuses and supplies no coverage-bearing interval.

Safer/stronger assumptions (optional, never implicit):

- [ ] A direction-specific p-value is monotone in effect on a complete branch;
  use only with a named theorem and checked runtime hypotheses.
- [ ] The accepted set is connected; no baseline algorithm or claim assumes it.
- [ ] Finite component boundaries are rational or algebraic and exactly isolated;
  the baseline permits outward boundary enclosures instead.
- [ ] A performance bound ignores integer bit complexity; such a bound is never
  promoted to a wall-clock promise.

## D) What would falsify it (counterexample targets)

1. A table/effect pair for which the exact Boschloo mask changes with nuisance
   `q`, rather than only with the tested OR.
2. A fixed-effect mask family that is self-inclusive but is not the principal
   family of one total preorder and violates super-uniformity.
3. An exact equality/tangency case classified as rejected because the engine
   uses `<= alpha_side` rather than strict rejection.
4. Either OR structural face omitted at `0` or `+infinity`, causing a supported
   zero/infinite-MLE table to lose its endpoint.
5. A reciprocal group-swap case that exposes a transformed-group denominator
   exponent or direction error.
6. A disconnected accepted set or isolated accepted tangency lost by
   first-crossing inversion or by cell-boundary ownership.
7. A boundary cell called accepted from one effect-point witness, or rejected by
   combining different failing directions at different points.
8. A rational internal hull whose ordinary float conversion shrinks one side,
   overflows to a structural tag, or violates the beta-space width contract.
9. A proof or implementation that samples rational nuisance values and thereby
   mistakes the rational certificate representation for the real supremum.
10. A global certificate that calls every finite leaf accepted/rejected while
    silently discarding a necessary `BOUNDARY_ENCLOSURE`.
11. Failure to reproduce any frozen U2 anchor in B.18 with its stated exact
    mask, root, stationary-cell count, or accept/reject sequence.
12. Reversing the signed breakpoint numerator or dropping its negative factor,
    which swaps mask-entry direction while preserving the cubic root set.
13. Applying a full-square continuity argument across `(s,q)=(0,1)` or `(1,0)`.
14. Requiring component matching for hull soundness, or accepting an unmatched
    extreme sliver whose global beta-space endpoint excess exceeds tolerance.
15. Treating failure to find an accepted witness as certified emptiness, or an
    outer cover of the full domain as certified full acceptance.
16. Declaring adaptive completion after effect-only subdivision or degree
    elevation stalls without switching dimension, invoking an exact fallback,
    or refusing.
17. A moving-mask equality boundary where the inclusive directional p-value is
    not upper semicontinuous, or its two-sided superlevel set is not closed.
18. A rational polynomial and rational closed interval for which no complete
    checked root/sign certificate exists under the frozen certificate language.
19. A nonempty compact accepted set whose order-isomorphic image has a different
    smallest closed beta-domain interval from `hull_beta(A_s)`.

## E) Done criteria

This U0 candidate is ready for independent statistical, exact-arithmetic,
formal-target, and software-contract review when:

1. the machine-readable manifest, proposed signatures, exact Boschloo preorder,
   structural matrix, empty-set error, registry text, and policy defaults are
   accepted without ambiguity;
2. every normative identity has stable domains, quantifiers, contract IDs, and
   a formal target/runtime consumer;
3. the real-effect/real-nuisance domain, alpha layers, maximum-attainment
   bridge, equality-at-alpha, both structural OR faces, cross-sectional
   conditional model, and outward float conversion are explicitly reviewed;
4. the Boschloo-only scope lock is non-widenable for 1.2.0 and all deferred
   research remains nonblocking and absent from the public surface;
5. the four frozen U2 anchors, owner packet, documentation, focused authority
   and mutation guards, strict docs build, hygiene gates, and unchanged 1.1.2
   suite pass; and
6. the diff contains no production implementation, export, registry row,
   default, version, capability value, or release-workflow change.

U0 merge authorizes exact U1/U2 attack work and the named proof obligations. It
does **not** authorize production unconditional code. Production begins only
after the complete fixed-null and global mathematics chain has merged.

## F) Handoff bundle (pasteable)

- Statement: Implement the release-manifest Boschloo OR confidence-set hull on
  the full extended real effect domain by inverting two exact directional
  Fisher-tail ordered tests at decoded binary-rational `alpha/2`; use rational
  effects only as coercion-preserving certificate representations; certify every
  real-continuum fixed-null threshold and the global inner/outer accepted set;
  fail closed.
- Assumptions: Positive group totals; stated mathematical/executable alpha
  layers; fixed effect/direction inclusive total preorder or nested family;
  nuisance-independent mask; real-continuum maximum attainment; exact
  arithmetic; tagged structural endpoints; complete certified partition with no
  unresolved successful leaf.
- Definitions: B.3 effect/structural domain, OR-MASS, B.5 Fisher-tail masks,
  B.6 strict threshold decision, B.9 structural matrix, B.11 inner/outer global
  semantics, B.14 canonical certificates.
- Counterexample targets: D.1-D.19 plus the U1/U2 rows in B.18.
- Requested deliverable: First independent exact oracle/adversarial artifacts
  and the proof obligations in B.16; no production module until the programme's
  complete mathematics gate has merged.
