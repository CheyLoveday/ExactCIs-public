# Certified unconditional exact intervals: U0 statistical specification

Status: **review candidate; specified but unshipped**. This document is the
U0-A/U0-B contract for programme issue #41. It changes no runtime behaviour,
does not add a registry row, and does not represent an unconditional method as
available in ExactCIs 1.1.2.

The release manifest is deliberately narrower than the research programme.
Boschloo odds-ratio inversion is specified for the 1.2.0 train. The two
score-ordered candidates remain deferred because their candidate-specific
algebraic comparison and endpoint orderings have not yet passed independent
proof review. Downstream work must consume this manifest rather than treating
the deferred candidates as hidden blockers or placeholders.

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

The ideal mathematical target is

```text
H_star = the smallest closed interval containing A[m,x].
```

A successful computation may enclose finite transition boundaries, but it must
produce a complete certified partition with no `UNRESOLVED` leaves and retain
an inner and outer accepted-set representation satisfying

```text
A_inner subseteq A[m,x] subseteq A_outer
H_star subseteq H_return = hull(A_outer).
```

`BOUNDARY_ENCLOSURE` leaves are neither accepted nor rejected: they contribute
to `A_outer`, not `A_inner`. The implementation may not infer connectedness,
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

The following block is the machine-readable U0 release decision.

<!-- exactcis-unconditional-release-manifest:start -->
```json
{
  "schema": "exactcis.unconditional.release_manifest.v1",
  "status": "specified-unshipped",
  "target_release": "1.2.0",
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
  "deferred_candidates": [
    {
      "construction_id": "barnard_efficient_score_or",
      "entrypoint": "exact_ci_barnard",
      "method_key": "barnard",
      "reason": "candidate-specific exact algebraic comparator and endpoint ordering require separate approval",
      "signature": "exact_ci_barnard(a: int, b: int, c: int, d: int, alpha: float, *, design: Design) -> tuple[float, float]"
    },
    {
      "construction_id": "exact_efficient_score_rr",
      "entrypoint": "exact_ci_score_rr",
      "method_key": "exact_score_rr",
      "reason": "candidate-specific exact algebraic comparator and endpoint ordering require separate approval",
      "signature": "exact_ci_score_rr(a: int, b: int, c: int, d: int, alpha: float, *, design: Design) -> tuple[float, float]"
    }
  ]
}
```
<!-- exactcis-unconditional-release-manifest:end -->

The manifest can be widened only by a reviewed U0 amendment that closes the
exact-comparison and structural contracts in B.8. A deferred method has no root
export, registry row, compatibility alias, expected-failure blocker, or public
placeholder.

U0 freezes these exact proposed raw-function signatures:

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

exact_ci_barnard(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float,
    *,
    design: Design,
) -> tuple[float, float]

exact_ci_score_rr(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float,
    *,
    design: Design,
) -> tuple[float, float]
```

Each raw function returns only `(lower, upper)`. Each requires an explicit
design, uses no continuity correction, and never substitutes another method.
Only `exact_ci_boschloo` belongs to the release manifest above; the other two
signatures are frozen names and validation surfaces for deferred candidates,
not exports, placeholders, or implementation commitments.

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

For either ratio `beta` in its extended real statistical domain, global
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

Its two structural fibres are unions of boundary faces, not tagged values of
the finite-psi nuisance formula:

```text
psi = 0:         p1 = 0  or p0 = 1,
psi = +infinity: p0 = 0  or p1 = 1.
```

The closure corners `(0,0)` and `(1,1)` are retained. This distinction is
necessary for both kinds of zero or infinite sample-odds-ratio table.

For a future risk-ratio method,

```text
rho = p1/p0,
rho = 0:         p1 = 0,
rho = +infinity: p0 = 0,
```

again with closure corners handled structurally.

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

### B.7 Exact-p validity and two-sided coverage

At fixed real `psi` and direction, let `T` be the exact Fisher-tail ordering value
with smaller values more extreme, and let

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
corollary uses `0 < alpha < 1`. Hence the
strict rejection event `p(X)<alpha_side` has probability at most
`alpha_side`. The two directional rejection events each satisfy that bound;
their union has probability at most `alpha`, so the ideal total procedure has
coverage at least `1-alpha`. If the implementation returns only certified
outward enclosures of that ideal accepted-set hull, then
`{return and miss}` is a subset of the ideal noncoverage event and has
probability at most `alpha`. No conditional-on-return coverage follows without
an additional theorem about the refusal mechanism.

The hypotheses are: a finite sample space, normalized point-null masses, one
common inclusive total preorder (equivalently, a nested family of inclusive
principal rejection sets) for each fixed effect and direction,
nuisance-independent masks, an exact real-continuum nuisance supremum, and
successful completion. A grid, sampler, local optimizer, non-nested family of
ad-hoc self-containing masks, or resource-exhausted call does not satisfy the
theorem.

### B.8 Deferred score candidates and the amendment gate

The following formulas identify the candidate constructions but do not place
them in the release manifest.

#### B.8.1 Candidate Barnard-family efficient-score OR ordering

For every candidate `(x,y)`, not just the observed table, set `m=x+y`. Its
candidate-specific constrained nuisance estimate is the unique maximizer on
`[0,1]`. For `0<m<N` it is the unique interior root of

```text
n0*(psi-1)*q^2
  + [n1*psi+n0-m*(psi-1)]*q
  - m = 0.                                      (OR-QHAT)
```

Use `q_hat=0` for `m=0` and `q_hat=1` for `m=N`. Put

```text
p0_hat = q_hat,
p1_hat = psi*q_hat/[1+(psi-1)q_hat],
w1 = n1*p1_hat*(1-p1_hat),
w0 = n0*p0_hat*(1-p0_hat),
U = x-n1*p1_hat,
I_eff = w1*w0/(w1+w0) when w1+w0>0.
```

The proposed statistic is `Z_OR=U/sqrt(I_eff)`. If `I_eff=0`, its exact
extended value is `0` when `U=0` and the signed infinity of `U` otherwise.
Greater ordering uses `Z_OR(candidate) >= Z_OR(observed)`; less uses `<=`.
There is no continuity correction and no observed-table-only nuisance fit.

An exact comparator may encode the algebraic `q_hat` by a square-free defining
polynomial plus rational isolating interval, compare sign first, and compare
`U^2/I_eff` with direction reversal for two negative scores. Overlapping
isolations require an exact algebraic equality/order certificate; rounding is
not a tie rule. Resource-bounded uncertainty must produce `R_minus/R_plus`.

This is a qualified Barnard-family score construction. Barnard tests are a
family, and neither the public name nor prose may imply equivalence to every
procedure carrying that surname.

#### B.8.2 Candidate exact efficient-score RR ordering

For rational `rho>0`, use `p1=rho*p0` and the feasible interval
`0<=p0<=min(1,1/rho)`. For each candidate `(x,y)`, the constrained MLE
`p0_hat` is the likelihood-maximizing feasible root of

```text
rho*N*p0^2
  - [rho*(n1+y)+n0+x]*p0
  + (x+y) = 0.                                  (RR-QHAT)
```

Set `p1_hat=rho*p0_hat` and

```text
D = x/n1-rho*y/n0,
V = p1_hat*(1-p1_hat)/n1
    + rho^2*p0_hat*(1-p0_hat)/n0,
Z_RR = D/sqrt(V).
```

This is algebraically the standardized efficient score for `log(rho)` at the
constrained nuisance maximum. No finite-sample variance multiplier is applied.
When `V=0`, use `0` if `D=0` and the signed infinity of `D` otherwise. Direction,
algebraic comparison, ties, and ambiguity follow the OR score rules.

The neutral candidate names are `exact_ci_score_rr` and `exact_score_rr`. No
historical identity is claimed until a formula-level comparison is reviewed.

#### B.8.3 Compact RR nuisance theorem target

For later exact RR work, use one compact `t in [0,1]`:

```text
rho <= 1: a0=1,     a1=rho,
rho >= 1: a1=1,     a0=1/rho,
p_g = a_g*t.
```

With `K_g~Bin(n_g,t)` and `X_g|K_g~Bin(K_g,a_g)`, one has
`X_g~Bin(n_g,a_g*t)`. For a fixed rejection mask,

```text
P((X1,X0) in R)
  = sum[m=0..N] b_m*C(N,m)*t^m*(1-t)^(N-m),
b_m = P((X1,X0) in R | K1+K0=m),
0 <= b_m <= 1.
```

A straightforward exact transform may cost `O(M*N)` before bit complexity.
No `O(M)` production claim is approved without a proved recurrence.

#### B.8.4 Score-manifest amendment criteria

One score candidate may enter the release manifest only after independent
review confirms all of the following:

1. candidate-specific constrained-MLE existence, uniqueness, and every boundary
   case;
2. exact expected efficient-information formula and direction convention;
3. a decidable exact algebraic comparison/equality certificate or sound
   `R_minus/R_plus` ambiguity protocol;
4. a common total preorder and nuisance-independent inclusive principal masks;
5. structural `0/+infinity` endpoint decisions and zero-information behaviour;
6. group-swap metamorphics and method-specific validity corollaries;
7. exact oracle and adversarial fixtures, including distinct quadratic fields.

Failure of any item keeps the method absent without delaying Boschloo OR.

### B.9 Structural decisions and observed point estimates

Structural effect values use direct support tests, not finite search limits.
For the manifest-approved Boschloo construction, an observed table outside
every distribution in its null fibre is rejected with p-value `0`; a supported
observation is accepted in both directions with the conservative structural
p-value `1`. Under a true structural null, generated observations are supported
almost surely and therefore receive p-value `1`; unsupported observations have
null probability zero. The structural rejection probability is consequently
zero. This endpoint rule is a specified conservative Boschloo extension, not a
limit of the finite-psi preorder. A deferred score construction must adopt or
replace it through the B.8.4 amendment gate and prove its own endpoint validity.

For positive group totals the OR cases are exhaustive:

| observed condition | uncorrected OR point | structural membership | raw interval consequence | policy point |
|---|---:|---|---|---|
| `a=c=0` (both groups all failures) | non-unique | `0` and `+infinity` accepted; every finite null has p-value `1` | exactly `(0.0, inf)` | raise `NonIdentifiableError` |
| `b=d=0` (both groups all successes) | non-unique | `0` and `+infinity` accepted; every finite null has p-value `1` | exactly `(0.0, inf)` | raise `NonIdentifiableError` |
| `a*d=0`, `b*c>0` | `0` | `0` accepted, `+infinity` rejected | lower endpoint exactly `0.0` | point `0.0` |
| `b*c=0`, `a*d>0` | `+infinity` | `0` rejected, `+infinity` accepted | upper endpoint exactly `inf` | point `inf` |
| `a*d>0`, `b*c>0` | finite positive | both structural endpoints rejected | global inversion determines boundedness; endpoint rejection alone does not exclude accepted finite sequences converging to an endpoint | finite sample OR |

For the deferred RR candidate the exhaustive cases are:

| observed condition | uncorrected RR point | structural membership | raw interval consequence | policy point |
|---|---:|---|---|---|
| `a=c=0` | non-unique | `0` and `+infinity` accepted; every finite null has p-value `1` | exactly `(0.0, inf)` | raise `NonIdentifiableError` |
| `a=0`, `c>0` | `0` | `0` accepted, `+infinity` rejected | lower endpoint exactly `0.0` | point `0.0` |
| `a>0`, `c=0` | `+infinity` | `0` rejected, `+infinity` accepted | upper endpoint exactly `inf` | point `inf` |
| `a>0`, `c>0` | finite positive | both structural endpoints rejected | a future global proof must determine boundedness; endpoint rejection alone is insufficient | finite sample risk/prevalence ratio |

RR all-success data are not the OR all-success non-identifiable case.

If the exact accepted set is empty, a future raw function raises a dedicated
`EmptyConfidenceSetError(ExactCIsError, RuntimeError)`; it must not return
`(0.0, inf)`. The trigger is a completed exact/certified partition proving
`A_outer` empty, not resource exhaustion or a failure to find an accepted
point. That proposed error is unshipped in U0 and requires API review before
integration. A full set returns exactly `(0.0, inf)`. Resource exhaustion
instead raises `NumericalError` with method, direction, null value or cell,
bounds, counters, active limits, and a machine-readable failure kind.

### B.10 Metamorphic transformations

Freeze the following transformations:

```text
group swap (a,b,c,d) -> (c,d,a,b):
    OR and RR map to their reciprocal; direction reverses.

outcome complement (a,b,c,d) -> (b,a,d,c):
    OR maps to its reciprocal; direction reverses.
    RR maps to the complementary-risk ratio, not generally to 1/RR.
```

No RR outcome-complement reciprocity test is valid. The exact OR group-swap
map must transform the nuisance parameterization as well as the effect value.

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

`UNRESOLVED` is transient or failed. A successful result has a **complete
certified partition**, not necessarily a complete exact accepted/rejected
partition: a boundary enclosure is neither accepted nor rejected and
contributes to `A_outer`, not `A_inner`. `A_inner` contains only certified
accepted material; `A_outer` contains it together with every
`BOUNDARY_ENCLOSURE` needed to enclose the ideal set. Disconnected accepted
components and isolated tangencies are retained before the hull is taken.

The returned interval is `H_return=hull(A_outer)`, with
`H_star subseteq H_return`. A successful certificate records the partition,
the `A_inner/A_outer` relation, and no `UNRESOLVED` leaf; it does not claim
that a boundary enclosure has been classified accepted or rejected.

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
not add a planned or experimental row. The OR policy default remains `wald`;
the RR policy default remains `score_rr`. Existing 1.1.2 results and errors must
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
| objective | OR/RR basis, exact degree, numerator/denominator or polynomial coefficient digests, arithmetic representation |
| decision | accepted/rejected/indeterminate, strict/equality relation to alpha, exact witness or root/sign leaves |
| bounds | optional p-value lower/upper rationals and argmax enclosure, always labelled diagnostic |
| proof map | contract IDs, theorem IDs, runtime hypotheses and checks |
| resources | states, coefficient bits/storage, subdivision nodes/depth, root-sign work, comparison refinements, active limits, exhausted flag |
| provenance | implementation revision, deterministic replay inputs, source classification, parent/child digests |

Every global certificate additionally contains the canonical effect-cell tree,
leaf ownership and state, the assertion that each cell covers its full real
effect image, direction-specific mask digests, witnesses, boundary widths on
both `s` and beta scales, `A_inner`, `A_outer`, accepted-component records,
boundary-enclosure records, structural points, returned outward hull,
transient-unresolved count which must be zero on success, and the determinism
digest. Its return-conversion record also contains the exact pre-conversion
rational bounds or structural tags, each returned binary64 bit pattern as 16
lowercase hexadecimal digits, the finite `as_integer_ratio()` witnesses, the
exact directional-comparison results, the post-rounding beta-space error check,
and any underflow/overflow or finite-tag refusal reason.

Replay rebuilds all derived masks, coefficients, decisions, partitions, and
digests from primitive inputs. A verifier checks local certificate conditions
without trusting the producer's scheduling choices. Certificate bytes must be
identical across repeated runs with the same implementation and inputs.

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
targets; issue #12 owns the formal package substrate. A renamed theorem must
retain the contract ID.

| contract ID | mathematical statement | formal target module/theorem | hypotheses | manifest applicability | future runtime consumer |
|---|---|---|---|---|---|
| `U-DESIGN-001` | product-binomial finite sample space and normalization | `ExactCIs.Unconditional.ProductBinomial.mass_sum` | positive group totals, probabilities in `[0,1]` | Boschloo | fixed-null mass builder |
| `U-XSEC-001` | fixed-positive-total return-and-miss bounds mix to the cross-sectional event bound; zero totals produce no return | `ExactCIs.Unconditional.ProductBinomial.crossSectionalMix` | conditional model and certified returned enclosure | Boschloo | design validation/docs |
| `U-EFFECT-001` | `s=beta/(1+beta)` maps the finite nonnegative real beta domain to `[0,1)` and tags both structural endpoints | `ExactCIs.Unconditional.Structural.effectEquiv` | finite real beta | Boschloo | global effect cells |
| `U-OR-NULL-001` | finite real OR null parameterization satisfies the cross-product equation; rational coefficients are a coercion-preserving specialization | `ExactCIs.Unconditional.ORNull.parameterization` | real `psi>0`, real `q in [0,1]` | Boschloo | OR mass builder |
| `U-OR-MASS-001` | equation OR-MASS with transformed-group exponent | `ExactCIs.Unconditional.ORNull.massIdentity` | `U-OR-NULL-001` | Boschloo | OR objective builder |
| `U-OR-BERN-001` | fixed-mask OR probability has a continuous real common-degree Bernstein ratio with positive denominator; rational specialization has rational coefficients | `ExactCIs.Unconditional.ORNull.bernsteinRatio` | exact fixed mask, real `psi>0` | Boschloo | OR coefficients |
| `U-OR-CONTROL-001` | ratio of common-degree control coefficients is the conditional rejection probability | `ExactCIs.Unconditional.ORNull.controlRatio` | fixed mask, total index | Boschloo | coefficient oracle |
| `U-NUISANCE-CONT-001` | every fixed-mask null objective is continuous on the full real compact nuisance interval | `ExactCIs.Unconditional.ORNull.continuous` | real finite effect, fixed mask | Boschloo | threshold bridge |
| `U-ATTAIN-001` | the nuisance supremum is attained and equals the `exists q`/`forall q` exact threshold decisions, including equality | `ExactCIs.Unconditional.ThresholdDecision.maximumAttained` | `U-NUISANCE-CONT-001`, compact interval | Boschloo | fixed-null decision |
| `U-RR-THIN-001` | compact RR thinning produces the degree-`N` Bernstein identity and coefficients in `[0,1]` | `ExactCIs.Unconditional.RRNull.thinningIdentity` | finite real `rho>0`, fixed mask; rational specialization | deferred score RR | future RR coefficients |
| `U-BOSCH-ORDER-001` | Fisher tails define inclusive total preorders independent of `q` at each finite real OR | `ExactCIs.Unconditional.BoschlooOrdering.totalPreorder` | real `psi>0` | Boschloo | mask builder |
| `U-BOSCH-REP-001` | the rational exact comparator agrees after coercion with the corresponding real Boschloo ordering | `ExactCIs.Unconditional.BoschlooOrdering.rationalCoercion` | reduced rational `psi>0` | Boschloo | executable comparator |
| `U-BOSCH-SWAP-001` | group swap maps `psi` to `1/psi` and reverses direction | `ExactCIs.Unconditional.BoschlooOrdering.groupSwap` | positive finite real `psi` | Boschloo | metamorphic checks |
| `U-MASK-001` | mask inclusion implies pointwise and supremum probability bounds | `ExactCIs.Unconditional.MaskBounds.sandwich` | normalized finite masses | Boschloo | ambiguity protocol |
| `U-THRESH-001` | positive-denominator threshold comparison equals the sign of `H` on the full real nuisance interval | `ExactCIs.Unconditional.ThresholdDecision.orEquiv` | decoded rational side level, real `q` | Boschloo | fixed-null decision |
| `U-BERN-CERT-001` | coefficient hulls and de Casteljau leaves give sound local signs | `ExactCIs.Unconditional.BernsteinSubdivision.signSound` | exact coefficients | Boschloo | fast certificate path |
| `U-ROOT-CERT-001` | normalized root/sign certificates decide the closed-interval sign problem including tangency | `ExactCIs.Unconditional.RootSignCertificate.soundComplete` | checked certificate | Boschloo | completeness path/verifier |
| `U-EXACT-P-001` | nuisance supremum of inclusive principal ordered p-values is super-uniform | `ExactCIs.Unconditional.ExactPValueValidity.superUniform` | one total preorder or nested inclusive principal family; q-independent masks | Boschloo | coverage claim |
| `U-COVER-001` | the ideal procedure has coverage at least `1-alpha`; certified outward returns satisfy `P(return and miss)<=alpha` | `ExactCIs.Unconditional.ExactPValueValidity.centralCoverage` | generic/ordinary alpha domains, `U-EXACT-P-001` twice, returned-hull containment | Boschloo | public calibration |
| `U-STRUCT-OR-001` | structural OR fibres and support decisions match B.3/B.9 | `ExactCIs.Unconditional.Structural.orEndpoints` | positive group totals | Boschloo | endpoint dispatch |
| `U-STRUCT-RR-001` | structural RR fibres and support decisions match B.3/B.9 | `ExactCIs.Unconditional.Structural.rrEndpoints` | positive group totals | deferred score RR | future endpoint dispatch |
| `U-SCORE-OR-001` | OR-QHAT and efficient-score formula define a candidate-specific extended algebraic order | `ExactCIs.Unconditional.BarnardOrdering.candidateScore` | rational `psi>0` | deferred Barnard | future score mask |
| `U-SCORE-RR-001` | RR-QHAT and variance formula define a candidate-specific extended algebraic order | `ExactCIs.Unconditional.ScoreRROrdering.candidateScore` | rational `rho>0` | deferred score RR | future score mask |
| `U-EFFECT-MASK-001` | cell lower/upper masks enclose every point mask over every real effect in the cell | `ExactCIs.Unconditional.GlobalInversion.maskCell` | canonical real-effect cell | Boschloo | global classifier |
| `U-EFFECT-QUANT-001` | whole-cell accept/reject certificates have the quantifiers in B.11 | `ExactCIs.Unconditional.GlobalInversion.cellDecision` | sound mask cells/objective bounds over real effects | Boschloo | global classifier |
| `U-INNER-OUTER-001` | a complete certified partition with no transient unresolved leaf implies `A_inner subseteq A subseteq A_outer` | `ExactCIs.Unconditional.GlobalInversion.innerOuter` | allowed leaf states, no transient unresolved leaves | Boschloo | partition/verifier |
| `U-HULL-001` | outward hull of `A_outer` contains the ideal hull and preserves structural tags | `ExactCIs.Unconditional.GlobalInversion.hullContains` | `U-INNER-OUTER-001` | Boschloo | public tuple conversion |

Theorems do not by themselves verify Python scheduling, serialization, resource
limits, memory use, or binary64 behaviour. Runtime consumers must check every
hypothesis and record the mapping in the certificate.

`U-FLOAT-001` is a software-only correspondence obligation, not a theorem
claim: tests and replay must reconstruct the B.12 directed conversion from the
recorded exact bounds, verify the returned IEEE-754 bit patterns and rational
witnesses, and force each underflow, overflow, wrong-direction, and error-budget
mutation to fail.

### B.17 Source and oracle authority

| source class | role | authority ceiling |
|---|---|---|
| this specification and later reviewed amendments | method identity, domains, ties, structural and error contracts | normative statistical definition |
| exact finite-sum proofs and checked formal theorems | distribution, ordering, threshold, validity, partition and hull claims | mathematical authority for their stated hypotheses |
| independent standard-library integer/Fraction oracle | fixtures, counterexamples, exact replay, metamorphics | implementation-independent executable evidence |
| Boschloo (1970), Barnard (1947), Suissa-Shuster (1985), Koopman (1984) | historical vocabulary and comparison | not production code and not proof of this extension's identity |
| external R, SciPy, or SAS outputs with pinned versions/options/orientation | compatibility records only | never a coverage or certification oracle |
| grids, quasi-random sampling, local/global floating optimizers | discovery and profiling only | never scientific truth |
| private or legacy implementations | failure-mode and candidate-fixture discovery | never ported or used as expected values |

No source under a copyleft implementation licence is translated. Exact
arithmetic is rederived from the mathematical definition.

Primary historical references, used only to identify vocabulary and provenance:

- R. D. Boschloo, ["Raised conditional level of significance for the 2 x 2
  table when testing the equality of two
  probabilities"](https://doi.org/10.1111/j.1467-9574.1970.tb00104.x), 1970.
- G. A. Barnard, ["Significance tests for 2 x 2
  tables"](https://doi.org/10.1093/biomet/34.1-2.123), 1947.
- S. Suissa and J. J. Shuster, ["Exact unconditional sample sizes for the 2 x
  2 binomial trial"](https://doi.org/10.2307/2981892), 1985.
- P. A. R. Koopman, ["Confidence intervals for the ratio of two binomial
  proportions"](https://doi.org/10.2307/2531405), 1984.

### B.18 Downstream stage contracts

| stage | required work | stop condition / exit ceiling |
|---|---|---|
| U1 oracle | independent full product-binomial enumeration; exact Fisher comparisons, coefficients, root/sign fixtures, structural/metamorphic corpus, canonical hashes; exhaustive positive group sizes through 12 where feasible | no production import or shared helper; external software remains compatibility-only; measured infeasibility is reported rather than hidden |
| U2 adversaries | strict expected failures for equality tangency, multiple maxima, near ties, endpoint nuisance optima, ordering breakpoints, disconnected accepted sets, structural cases, imbalance, and resource cliffs | scouting grids locate cases but exact U1 evidence defines them; every expected failure names its repairing stage |
| fixed-null proofs | prove all manifest-applicable rows in B.16, including total-preorder validity and exact tangency completion | no admissions, floating equality, or method-specific corollary for a deferred method |
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
| ordering breakpoint | candidate `(1,3)` | tail-difference numerator has breakpoint `3*psi^3 - 23*psi - 8 = 0` |

The tangency anchor requires the exact root/sign completeness path. The
disconnected and breakpoint anchors require the #52/#49 general global path;
they rule out a connectedness or global-monotonicity baseline.

The ordering-breakpoint row is a verified factor-level anchor, not yet a
standalone strict-fixture record: U2 must bank its group sizes, observed table,
direction, compared ordering values, exact algebraic isolation or rational
brackets, and masks immediately on both sides of the breakpoint. It is only
then independently replayable as required by the U2 issue.

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
- [x] Every successful global result establishes
  `A_inner subseteq A subseteq A_outer`, has no transient unresolved leaf, and
  may retain `BOUNDARY_ENCLOSURE` rather than falsely classify it.
- [x] Structural endpoints are tagged mathematical states, not finite sentinels.
- [x] Resource exhaustion refuses and supplies no coverage-bearing interval.

Safer/stronger assumptions (optional, never implicit):

- [ ] A direction-specific p-value is monotone in effect on a complete branch;
  use only with a named theorem and checked runtime hypotheses.
- [ ] The accepted set is connected; no baseline algorithm or claim assumes it.
- [ ] Finite component boundaries are rational or algebraic and exactly isolated;
  the baseline permits outward boundary enclosures instead.
- [ ] A score candidate has a decidable exact comparator for every pair of
  candidate tables; until proved, that candidate remains outside the manifest.
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
4. score candidates are either approved by a later manifest amendment after all
   B.8.4 gates, or remain nonblocking and absent;
5. the four frozen U2 anchors, documentation, manifest-guard tests, strict docs
   build, hygiene gates, and the unchanged 1.1.2 suite pass; and
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
- Counterexample targets: D.1-D.8 plus the U1/U2 rows in B.18.
- Requested deliverable: First independent exact oracle/adversarial artifacts
  and the proof obligations in B.16; no production module until the programme's
  complete mathematics gate has merged.
