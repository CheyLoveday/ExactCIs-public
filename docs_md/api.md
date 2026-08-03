# API contract

All functions use the package table orientation:

```text
             outcome +   outcome -
exposed +        a           b
exposed -        c           d
```

Counts are finite non-negative integers. `alpha` is the two-sided significance
level and must satisfy the certified numerical contract
`1e-12 < alpha < 1 - 1e-12`. Values outside this open interval raise
`ValidationError` before quantile evaluation or inversion. Extended endpoints
are Python `0.0` and `math.inf`. Incoherent designs raise `DesignError`;
unidentified point estimates raise
`NonIdentifiableError`; unsupported method keys raise
`UnsupportedMethodError`; and failed numerical certification raises
`NumericalError`.

## Design-aware policy functions

### `compute_or_with_policy`

Accepts one table, keyword-only `design`, optional registry `method`, and
`alpha`. Fixed-margin case-control sampling estimates a conditional odds ratio;
cohort and cross-sectional rows use product-binomial Wald constructions. It
returns `InferenceResult(point, lower, upper, confidence_level, design,
estimand, method, construction, status)`. Singleton conditional support has a
full confidence set but no unique point, so the policy refuses it.

```python
from exactcis import Design, compute_or_with_policy

result = compute_or_with_policy(12, 5, 8, 10, design=Design.CASE_CONTROL_FIXED_MARGIN)
assert result.lower <= result.point <= result.upper
```

### `compute_rr_with_policy`

Accepts one independent-group table under `COHORT_BINOMIAL` (risk ratio) or
`CROSS_SECTIONAL` (prevalence ratio). It defaults to `score_rr` and returns
`InferenceResult`. Fixed-margin retrospective case-control sampling is refused.
Empty groups and two observed zero risks do not produce a policy point.

```python
from exactcis import Design, compute_rr_with_policy

result = compute_rr_with_policy(12, 5, 8, 10, design=Design.COHORT_BINOMIAL)
assert result.lower <= result.point <= result.upper
```

### `compute_pooled_or`

Accepts an iterable of prespecified independent `(a, b, c, d)` strata, a
stratified design, and `alpha`. It returns `PooledORResult` from the
Mantel-Haenszel estimator and Robins-Breslow-Greenland variance. Empty strata,
zero pooled cross-products, and unsupported designs fail explicitly.
The private source profile-likelihood inverter is not shipped or reachable;
this public route is the registry-declared Mantel-Haenszel replacement.

```python
from exactcis import Design, compute_pooled_or

result = compute_pooled_or(
    [(12, 5, 8, 10), (8, 2, 15, 20)],
    design=Design.STRATIFIED_CASE_CONTROL,
)
assert result.lower <= result.point <= result.upper
```

## Fixed-margin odds-ratio intervals

These functions require `design=Design.CASE_CONTROL_FIXED_MARGIN`, return a
`(lower, upper)` tuple, and condition on both margins. Support-boundary
observations produce `0` or `+∞`; singleton support produces `(0, +∞)`.
Nonconvergence raises `NumericalError` without fallback.

```python
from exactcis import (
    Design,
    exact_ci_blaker,
    exact_ci_conditional,
    exact_ci_midp,
    exact_ci_minlike,
)

table = (12, 5, 8, 10)
design = Design.CASE_CONTROL_FIXED_MARGIN
for method in (
    exact_ci_conditional,
    exact_ci_midp,
    exact_ci_minlike,
    exact_ci_blaker,
):
    lower, upper = method(*table, design=design)
    assert 0 <= lower <= upper
```

`exact_ci_conditional` inverts inclusive equal tails. `exact_ci_midp` includes
half the observed mass in each tail and does not claim exact nominal coverage.
`exact_ci_minlike` and `exact_ci_blaker` invert distinct inclusive outcome
orderings; they are not aliases.

## Product-binomial odds-ratio intervals

`ci_wald` and `ci_wald_haldane` require `COHORT_BINOMIAL` or
`CROSS_SECTIONAL` and return `(lower, upper)`. The former applies a 0.5
correction only when a zero cell occurs; the latter always applies it. Empty
groups or outcome columns are non-estimable. These are asymptotic intervals.

```python
from exactcis import Design, ci_wald, ci_wald_haldane

for method in (ci_wald, ci_wald_haldane):
    lower, upper = method(12, 5, 8, 10, design=Design.COHORT_BINOMIAL)
    assert 0 < lower <= upper
```

## Risk/prevalence-ratio intervals

`ci_score_rr` and `ci_wald_rr` require `COHORT_BINOMIAL` (risk ratio) or
`CROSS_SECTIONAL` (prevalence ratio) and return `(lower, upper)`. Empty groups
are invalid. Zero events in the numerator row give lower endpoint zero; zero
events in the denominator row give upper endpoint infinity; both zero-event
rows give the full set. Score inversion raises on failed bracketing and never
substitutes Wald.

```python
from exactcis import Design, ci_score_rr, ci_wald_rr

for method in (ci_score_rr, ci_wald_rr):
    lower, upper = method(12, 5, 8, 10, design=Design.COHORT_BINOMIAL)
    assert 0 < lower <= upper
```

## Result types and version

`InferenceResult` and `PooledORResult` are frozen typed dataclasses.
`exactcis.__version__` is read only from `exactcis.__about__`. The root exports
the documented exceptions above and no compatibility aliases.
