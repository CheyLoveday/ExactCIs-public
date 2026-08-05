# Supported methods

This table is derived from `exactcis.estimands.method_registry()` and verified
by `tools/check_method_docs.py`. The registry—not this rendered page—is the
machine-readable source of truth.

<!-- exactcis-method-table:start -->
| design | effect measure | method key | construction | status | point estimator | interval/test type | coverage/calibration statement | principal limitations |
|---|---|---|---|---|---|---|---|---|
| case_control_fixed_margin | odds ratio | `conditional` | Equal-tail inversion of the Fisher noncentral hypergeometric law | stable | conditional maximum-likelihood estimate | conditional exact confidence interval | Tail probabilities are computed under fixed margins; discreteness can make coverage conservative. | Conditions on both margins and does not claim unconditional coverage. |
| case_control_fixed_margin | odds ratio | `midp` | Mid-P equal-tail inversion of the Fisher noncentral hypergeometric law | stable | conditional maximum-likelihood estimate | conditional mid-P confidence interval | Mid-P reduces discreteness but is not guaranteed to attain nominal coverage for every parameter value. | Conditions on both margins; mid-P is not a fully exact coverage guarantee. |
| case_control_fixed_margin | odds ratio | `minlike` | Fisher-Irwin minimum-likelihood ordering under the conditional law | stable | conditional maximum-likelihood estimate | numerically certified interval hull of the inverted ordered conditional exact confidence set | Inverts an inclusive probability-mass ordering at fixed margins. | Discrete ordering can yield non-smooth endpoints and conservative coverage. |
| case_control_fixed_margin | odds ratio | `blaker` | Blaker acceptability ordering under the conditional law | stable | conditional maximum-likelihood estimate | numerically certified interval hull of the inverted ordered conditional exact confidence set | Inverts inclusive Blaker acceptability ordering at fixed margins. | Discrete ordering can yield non-smooth endpoints and conservative coverage. |
| cohort_binomial | odds ratio | `wald` | Log-Wald interval with a 0.5 correction only when any cell is zero | stable | sample odds ratio, corrected on zero-cell tables | asymptotic confidence interval | First-order normal approximation on the log-odds-ratio scale. | Can be inaccurate for sparse data; the zero-cell correction changes the target estimator. |
| cohort_binomial | odds ratio | `wald_haldane` | Log-Wald interval after adding 0.5 to every cell | stable | Haldane-Anscombe corrected odds ratio | asymptotic confidence interval | First-order normal approximation after a fixed continuity correction. | The correction is applied even without zero cells and can matter in small samples. |
| cohort_binomial | risk ratio | `score_rr` | Koopman-Nam inversion of the independent-binomial score statistic | stable | sample risk ratio | score confidence interval | Score-test inversion for two independent binomial groups. | Requires non-empty groups; discreteness is not modelled as an exact conditional law. |
| cohort_binomial | risk ratio | `wald_rr` | Log-Wald interval for two independent binomial risks | stable | sample risk ratio with zero-triggered correction for finite-side calculation | asymptotic confidence interval | First-order normal approximation on the log-ratio scale. | Can be inaccurate for sparse data; structural zero and infinity endpoints are retained. |
| cross_sectional | prevalence odds ratio | `wald` | Log-Wald interval with a 0.5 correction only when any cell is zero | stable | sample odds ratio, corrected on zero-cell tables | asymptotic confidence interval | First-order normal approximation on the log-odds-ratio scale. | Can be inaccurate for sparse data; the zero-cell correction changes the target estimator. |
| cross_sectional | prevalence odds ratio | `wald_haldane` | Log-Wald interval after adding 0.5 to every cell | stable | Haldane-Anscombe corrected odds ratio | asymptotic confidence interval | First-order normal approximation after a fixed continuity correction. | The correction is applied even without zero cells and can matter in small samples. |
| cross_sectional | prevalence ratio | `score_rr` | Koopman-Nam inversion of the independent-binomial score statistic | stable | sample prevalence ratio | score confidence interval | Score-test inversion for two independent binomial groups. | Requires non-empty groups; discreteness is not modelled as an exact conditional law. |
| cross_sectional | prevalence ratio | `wald_rr` | Log-Wald interval for two independent binomial risks | stable | sample prevalence ratio with zero-triggered correction for finite-side calculation | asymptotic confidence interval | First-order normal approximation on the log-ratio scale. | Can be inaccurate for sparse data; structural zero and infinity endpoints are retained. |
| stratified_case_control | common odds ratio | `mantel_haenszel` | Mantel-Haenszel common odds ratio with Robins-Breslow-Greenland variance | stable | Mantel-Haenszel common odds ratio | asymptotic stratified confidence interval | Large-sample normal approximation for prespecified independent strata. | Requires positive pooled cross-products and a defensible common-effect model. |
| stratified_cohort | common odds ratio | `mantel_haenszel` | Mantel-Haenszel common odds ratio with Robins-Breslow-Greenland variance | stable | Mantel-Haenszel common odds ratio | asymptotic stratified confidence interval | Large-sample normal approximation for prespecified independent strata. | Requires positive pooled cross-products and a defensible common-effect model. |
<!-- exactcis-method-table:end -->

## Selection rules

The high-level policy selects only stable methods. Fixed-margin OR defaults to
`conditional`; cohort/cross-sectional OR defaults to `wald`; and
risk/prevalence ratio defaults to `score_rr`. Stratified pooling requires an
explicit `compute_pooled_or` call. Experimental, compatibility, planned, and
unsupported methods do not participate in selection.

## Sparse cohort Wald coverage (illustration)

Log-Wald odds-ratio intervals are **first-order asymptotic**. On sparse cohort
tables they often look “fine” (finite endpoints, `status='stable'`) while
**empirical coverage drifts away from the nominal 95%**, and empty outcome
columns make the OR non-identifiable (the interval is not produced).

The table below is a Monte Carlo check of unconditional coverage for the true
odds ratio under independent binomial sampling
(`Design.COHORT_BINOMIAL`, `alpha=0.05`). Each row draws 1 000 tables with
`seed=42` using pure-Python Bernoulli sampling; coverage is the fraction of
**successful** intervals that contain the true OR. Failures are empty-column
or other validation/numerical refusals (not counted in the coverage rate).

| n₁ | n₂ | p₁ | p₂ | true OR | `wald` coverage | `wald_haldane` coverage | `wald` fails / 1000 | `wald_haldane` fails / 1000 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 20 | 20 | 0.50 | 0.50 | 1 | 94.9% | 95.0% | 0 | 0 |
| 20 | 20 | 0.10 | 0.10 | 1 | 99.7% | 99.7% | 10 | 10 |
| 20 | 20 | 0.05 | 0.20 | 0.211 | 96.9% | 96.9% | 3 | 3 |
| 10 | 10 | 0.10 | 0.10 | 1 | 100% | 100% | 145 | 145 |
| 10 | 40 | 0.05 | 0.05 | 1 | 97.6% | 97.6% | 76 | 76 |
| 15 | 15 | 0.05 | 0.05 | 1 | 100% | 100% | 235 | 235 |
| 50 | 50 | 0.02 | 0.02 | 1 | 100% | 100% | 133 | 133 |
| 30 | 30 | 0.80 | 0.20 | 16 | 97.5% | 96.0% | 0 | 0 |
| 100 | 100 | 0.05 | 0.05 | 1 | 97.6% | 98.2% | 0 | 0 |

**How to read this.** Nominal 95% is approached on balanced moderate cells
(e.g. n=20, p=0.5). Sparse or rare-event designs show **conservative** coverage
when an interval is produced **and** a high rate of **non-identifiable**
tables when a column is empty. Very high “coverage” with many failures is not
a free lunch: the procedure often refuses rather than undercovering.

**What to use instead when cells are sparse**

| Situation | Prefer |
|---|---|
| Fixed-margin case-control OR | `conditional` / `midp` / `blaker` / `minlike` (not Wald) |
| Independent-binomial OR with rare events | Treat Wald as exploratory; prefer larger samples or a design that identifies a conditional exact OR if appropriate |
| Independent-binomial risk / prevalence ratio | Prefer `score_rr` over `wald_rr` for sparse counts |
| Empty outcome column | No OR interval is identified; fix the sampling design or collect more data |

## Conditional exact runtime (illustration)

The fixed-margin evaluator traverses outward from the mode and stops only when
a term's relative log mass underflows exactly to zero in binary64. Returned
probabilities are bit-identical to the full recurrence, but need not evaluate
every point in the conditional support.

## Fixed-margin certification limits

This block is generated from `exactcis._capability`; the tool verifies it in
CI. The ordered-hull width cap is a certification ceiling, not a performance
promise: its evaluation budget can refuse a narrower call when it cannot prove
the endpoint.

<!-- exactcis-capability-table:start -->
| documented capability | value | applicability / failure contract |
|---|---:|---|
| Cell-count bound | `1,000,000,000,000` per cell | `ValidationError` before numerical work |
| Certified alpha domain | `1e-12 < alpha < 1 - 1e-12` | `ValidationError` outside the open domain |
| Preparation support-width cap | `10,000,000` | `conditional`, `midp`; `NumericalError` before support preparation |
| Ordered-hull support-width cap | `1,000,000` | `minlike`, `blaker`; `NumericalError` before ordered-hull preparation |
| Ordered-hull evaluation budget | `50,000` | certification can refuse below the width cap |
| Ordered-hull recursion-depth cap | `64` | one rejection certificate |
<!-- exactcis-capability-table:end -->

The version-stamped timing block below is generated from a committed clean-wheel
measurement record. It is illustrative evidence, not a competitive benchmark.

<!-- exactcis-timing-table:start -->
Measured on `exactcis==1.1.0` at `18673bb` with Python 3.12.3 on macOS-26.5.1-arm64-arm-64bit (2026-08-05). Each measured row is one public API call from a clean wheel-installed virtual environment; time.perf_counter starts after imports and no profiler is attached. The cap-width row records the existing unoptimised cap-scale evidence rather than rerunning it.

| Table / support width | method | seconds | outcome |
|---|---|---:|---|
| `(20, 10, 15, 25); W=31` | `conditional` | 0.00148958 | returns |
| `(100, 50, 80, 120); W=151` | `conditional` | 0.00706092 | returns |
| `(500, 250, 250, 1000); W=751` | `conditional` | 0.0494918 | returns |
| `(1500, 1500, 1500, 1500); W=3,001` | `conditional` | 0.16038 | returns |
| `(50000, 50000, 50000, 50000); W=100,001` | `minlike` | 36.8814 | returns |
| `(500000, 500000, 500000, 500000); W=1,000,001` | `minlike` | 2.825e-05 | raises NumericalError before allocation |
| `(499999, 500000, 500000, 500000); W=1,000,000` | `minlike` | not rerun | tens of minutes, unoptimised; see #27 |
<!-- exactcis-timing-table:end -->

**Soft guidance.** If conditional support is large enough that a single call is
taking many seconds and an asymptotic comparison is scientifically acceptable
for the design, prefer the design-appropriate asymptotic route (`wald` /
`wald_haldane` for independent-binomial OR; `score_rr` for RR/PR). Do **not**
swap methods silently after a timeout: ExactCIs fails closed; the caller must
choose the construction.

Counts above `10**12` per cell are rejected by validation so that float /
log-space arithmetic stays inside the package’s numerical certification
envelope.
