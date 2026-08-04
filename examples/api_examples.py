"""Executable examples for every stable root-level operation."""

from exactcis import (
    Design,
    ci_score_rr,
    ci_wald,
    ci_wald_haldane,
    ci_wald_rr,
    compute_or_with_policy,
    compute_pooled_or,
    compute_rr_with_policy,
    exact_ci_blaker,
    exact_ci_conditional,
    exact_ci_midp,
    exact_ci_minlike,
)

table = (12, 5, 8, 10)
fixed = Design.CASE_CONTROL_FIXED_MARGIN
cohort = Design.COHORT_BINOMIAL

or_result = compute_or_with_policy(*table, design=fixed)
rr_result = compute_rr_with_policy(*table, design=cohort)
pooled_result = compute_pooled_or(
    [table, (8, 2, 15, 20)],
    design=Design.STRATIFIED_CASE_CONTROL,
)

for result in (or_result, rr_result, pooled_result):
    assert result.lower <= result.point <= result.upper
    print(
        f"{result.method}: point={result.point:.6g} "
        f"({result.lower:.6g}, {result.upper:.6g})"
    )

for method in (
    exact_ci_conditional,
    exact_ci_midp,
    exact_ci_minlike,
    exact_ci_blaker,
):
    lower, upper = method(*table, design=fixed)
    assert 0.0 <= lower <= upper
    print(f"{method.__name__}: ({lower:.6g}, {upper:.6g})")

for method in (ci_wald, ci_wald_haldane):
    lower, upper = method(*table, design=cohort)
    assert 0.0 < lower <= upper
    print(f"{method.__name__}: ({lower:.6g}, {upper:.6g})")

for method in (ci_score_rr, ci_wald_rr):
    lower, upper = method(*table, design=cohort)
    assert 0.0 < lower <= upper
    print(f"{method.__name__}: ({lower:.6g}, {upper:.6g})")
