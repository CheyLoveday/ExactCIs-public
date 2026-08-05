# Ordered confidence-set hull: specification

Specification for the interval returned by `exact_ci_minlike` and
`exact_ci_blaker` (programme issue #15). The implementation (issue #16) is
written against this document; the formal package states and proves the
real-valued obligations; the Python test suite discharges the floating-point
obligations. Nothing in this file describes the current implementation. It
describes what any implementation must satisfy.

## 1. Objects

Fix a table `(a, b, c, d)` with margins `n1 = a + b`, `n0 = c + d`,
`m = a + c`, a significance level `alpha` in the certified domain, and an
ordering (minimum-likelihood or Blaker). Let `p(eta)` be the inclusive ordered
conditional p-value at log odds ratio `eta`, computed with the frozen tie
policy: a support point is included when its rank is no greater than

```
threshold(eta) = nextafter(rank_eta(a) * (1.0 + 1e-10), inf)
```

Three objects are distinct and must never be conflated.

1. **Accepted set.** `A = { eta : p(eta) >= alpha }`, a subset of the extended
   real line. It may be disconnected.
2. **Ideal hull.** `H = [inf A, sup A]`, the smallest closed order interval
   containing `A`, with infima and suprema taken in the extended reals.
3. **Returned interval.** A pair of binary64 values `(L, U)` on the odds-ratio
   scale, an outward-certified numerical enclosure of `H`.

## 2. Contract for the returned interval

R1. **Containment.** Every element of `A` lies in `[L, U]` after mapping to the
    odds-ratio scale. Equivalently `L <= exp(inf A)` and `exp(sup A) <= U`.

R2. **Structural endpoints are exact.** If the observed count sits at the lower
    support bound, `L == 0.0` exactly. If at the upper support bound,
    `U == inf` exactly. If the conditional support is a single point, the
    returned interval is `(0.0, inf)` exactly.

R3. **Bounded excess.** Finite endpoints lie outside the ideal endpoints.
    Define the near-accepted set `A_kappa = { eta : p(eta) >= alpha - kappa }`,
    where `kappa` is the certification floor: the smallest p-difference the
    conservative bounds can resolve, set by the documented inflation constant
    and of order `1e-9 * p`. The log-scale excess of each finite endpoint
    beyond the closure of `A_kappa` is bounded by
    `TOL = _ROOT_TOL * max(1.0, |log endpoint|)`, the same parameter-error
    contract used by the root solvers. Excess relative to the ideal endpoint of
    `A` itself is additionally bounded by the width of the band on which
    `|p - alpha| < kappa`, which is `kappa` divided by the local slope of `p`;
    measured on an exhaustive small-table sweep this totals below `3e-8` on the
    log scale. A tolerance stated against `A` alone would be unachievable by
    any finite-precision implementation, which is precisely the ideal-versus-
    floating distinction this specification exists to keep.

R4. **No search sentinel.** A finite configured search-domain limit is never
    reported as an inferential endpoint. If acceptance persists at the domain
    limit, the returned endpoint is the exact structural `0.0` or `inf`.

R5. **Fail closed.** If the enclosure cannot be certified within the
    computation budget, the routine raises `NumericalError`. It never returns a
    best-effort interval and never substitutes another method.

R6. **Tie policy frozen.** Point evaluations of `p` use exactly the threshold
    above. No bound construction may narrow it.

## 3. Why first-transition search is insufficient

The previous construction walked outward from the conditional MLE and bisected
the first sign change of `p - alpha`. Two measured facts break it.

- The accepted set can be disconnected. On `(4, 300, 150, 4)` at
  `alpha = 0.01` under minimum-likelihood ordering, `eta = log(0.00229)` is
  accepted while the first transition sits below it. The returned interval
  violated R1.
- Within a maximal segment on which the ordering membership set is constant,
  `p` need not be monotone. On margins `(35, 12, 36)` with observed 31, fixed
  membership segments exhibit interior direction changes. Any construction
  that evaluates `p` only at membership breakpoints therefore has no
  correctness argument.

## 4. Sound enclosure obligations

Any implementation must derive its endpoint from certified rejection, not from
point evaluations alone.

E1. **Rejection certificates.** A region may be excluded from the search only
    when a certified upper bound of `p` over the entire region is below
    `alpha`.

E2. **Conservative floating bounds.** A real-valued bound argument is not
    automatically a floating bound. Certified upper bounds must be computed
    with outward-rounded operations or an explicit, documented roundoff
    inflation whose margin dominates the accumulated evaluation error by
    several orders of magnitude, validated against dense sampling.

E3. **Acceptance extends, never excludes.** Direct evaluations of `p` may be
    used to certify that a point is accepted, extending the hull outward.
    A floating error at the alpha boundary then widens the interval, which is
    the conservative direction. Point evaluations must never shrink it.

E4. **Membership-agnostic bounds.** For Blaker ordering the membership set
    cannot be partitioned by probability-mass tie intercepts alone: ranks are
    cumulative tails, and a complete intercept enumeration must additionally
    cover tail-branch switches of every support point, the observed point's
    branch switch, and threshold crossings. An implementation may avoid the
    enumeration entirely by using bounds that remain sound when membership
    changes inside the region: a point whose membership over the region is
    uncertain contributes its full upper mass bound to the region's `p` upper
    bound and nothing to any lower bound.

E5. **Convergence without a stated rate.** The region bounds must converge to
    `p` as the region shrinks. First-order convergence is expected and
    sufficient; no faster rate may be claimed without a separate proof.

## 5. Division of assurance

A formal-assurance layer, tracked separately in the post-1.0.0 programme and
**not present in this repository**, is the intended home for the real-valued
obligations: the accepted-set and hull definitions, soundness of the envelope
bounds under exact arithmetic, that outward-certified rejection plus
accepted-point extension yields an interval satisfying R1, and refinement
convergence (E5). Until that layer exists, those obligations are stated here as
specification, not as discharged proof. Python certifies today: binary64 evaluation, the `nextafter` tie
policy, the inflation margin against dense sampling (E2), structural endpoint
exactness (R2), sentinel behaviour (R4), budget behaviour (R5), and agreement
with external references within the declared compatibility tolerance, which for
finite `exact2x2` endpoints is approximately `1e-6` combined absolute and
relative, reflecting the known tie-policy difference.

## 6. Registry wording

The registry `interval_type` for both orderings becomes:

> numerically certified interval hull of the inverted ordered conditional
> exact confidence set

with documentation explaining that the returned interval is an outward-certified
approximation to the smallest interval containing the possibly disconnected
inverted confidence set.
