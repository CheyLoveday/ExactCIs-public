# Supported methods

This table is derived from `exactcis.estimands.method_registry()` and verified
by `tools/check_method_docs.py`. The registry—not this rendered page—is the
machine-readable source of truth.

<!-- exactcis-method-table:start -->
| design | effect measure | method key | construction | status | point estimator | interval/test type | coverage/calibration statement | principal limitations |
|---|---|---|---|---|---|---|---|---|
| case_control_fixed_margin | odds ratio | `conditional` | Equal-tail inversion of the Fisher noncentral hypergeometric law | stable | conditional maximum-likelihood estimate | conditional exact confidence interval | Tail probabilities are computed under fixed margins; discreteness can make coverage conservative. | Conditions on both margins and does not claim unconditional coverage. |
| case_control_fixed_margin | odds ratio | `midp` | Mid-P equal-tail inversion of the Fisher noncentral hypergeometric law | stable | conditional maximum-likelihood estimate | conditional mid-P confidence interval | Mid-P reduces discreteness but is not guaranteed to attain nominal coverage for every parameter value. | Conditions on both margins; mid-P is not a fully exact coverage guarantee. |
| case_control_fixed_margin | odds ratio | `minlike` | Fisher-Irwin minimum-likelihood ordering under the conditional law | stable | conditional maximum-likelihood estimate | ordered conditional exact confidence set | Inverts an inclusive probability-mass ordering at fixed margins. | Discrete ordering can yield non-smooth endpoints and conservative coverage. |
| case_control_fixed_margin | odds ratio | `blaker` | Blaker acceptability ordering under the conditional law | stable | conditional maximum-likelihood estimate | ordered conditional exact confidence set | Inverts inclusive Blaker acceptability ordering at fixed margins. | Discrete ordering can yield non-smooth endpoints and conservative coverage. |
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
