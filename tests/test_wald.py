"""Direct tests for asymptotic odds- and risk-ratio intervals."""

from __future__ import annotations

import math
from statistics import NormalDist

import pytest

from exactcis.estimands import Design
from exactcis.exceptions import DesignError, NonIdentifiableError, ValidationError
from exactcis.inference.odds_ratio import ci_wald, ci_wald_haldane
from exactcis.inference.relative_risk import ci_wald_rr

COHORT = Design.COHORT_BINOMIAL
CROSS_SECTIONAL = Design.CROSS_SECTIONAL


def _analytic_or_interval(table, *, correction: float) -> tuple[float, float]:
    a, b, c, d = (value + correction for value in table)
    point = a * d / (b * c)
    standard_error = math.sqrt(1 / a + 1 / b + 1 / c + 1 / d)
    critical = NormalDist().inv_cdf(0.975)
    return (
        math.exp(math.log(point) - critical * standard_error),
        math.exp(math.log(point) + critical * standard_error),
    )


def test_wald_matches_analytic_log_or_formula() -> None:
    table = (12, 5, 8, 10)
    assert ci_wald(*table, design=COHORT) == pytest.approx(
        _analytic_or_interval(table, correction=0.0), rel=2e-14
    )
    assert ci_wald_haldane(*table, design=COHORT) == pytest.approx(
        _analytic_or_interval(table, correction=0.5), rel=2e-14
    )


def test_zero_trigger_and_always_haldane_contracts_are_distinct() -> None:
    zero_table = (0, 5, 5, 10)
    regular_table = (1, 5, 5, 10)
    assert ci_wald(*zero_table, design=COHORT) == pytest.approx(
        ci_wald_haldane(*zero_table, design=COHORT)
    )
    assert ci_wald(*regular_table, design=COHORT) != pytest.approx(
        ci_wald_haldane(*regular_table, design=COHORT)
    )


@pytest.mark.parametrize("method", (ci_wald, ci_wald_haldane))
@pytest.mark.parametrize("design", (COHORT, CROSS_SECTIONAL))
def test_wald_or_row_and_column_swap_reciprocity(method, design) -> None:
    lower, upper = method(12, 5, 8, 10, design=design)
    for swapped in ((8, 10, 12, 5), (5, 12, 10, 8)):
        swapped_lower, swapped_upper = method(*swapped, design=design)
        assert lower == pytest.approx(1 / swapped_upper, rel=2e-14)
        assert upper == pytest.approx(1 / swapped_lower, rel=2e-14)


@pytest.mark.parametrize("method", (ci_wald, ci_wald_haldane))
def test_wald_or_confidence_interval_nests(method) -> None:
    ci_90 = method(12, 5, 8, 10, alpha=0.10, design=COHORT)
    ci_95 = method(12, 5, 8, 10, alpha=0.05, design=COHORT)
    ci_99 = method(12, 5, 8, 10, alpha=0.01, design=COHORT)
    assert ci_99[0] < ci_95[0] < ci_90[0]
    assert ci_90[1] < ci_95[1] < ci_99[1]


@pytest.mark.parametrize("method", (ci_wald, ci_wald_haldane))
def test_wald_or_nonidentifiable_and_wrong_design_fail(method) -> None:
    with pytest.raises(NonIdentifiableError, match="outcome column"):
        method(0, 5, 0, 5, design=COHORT)
    with pytest.raises(ValidationError, match="comparison group"):
        method(0, 0, 5, 5, design=COHORT)
    with pytest.raises(DesignError, match="requires"):
        method(12, 5, 8, 10, design=Design.CASE_CONTROL_FIXED_MARGIN)


def test_wald_rr_analytic_interior_and_structural_endpoints() -> None:
    a, b, c, d = 12, 5, 8, 10
    ratio = (a / (a + b)) / (c / (c + d))
    se = math.sqrt(b / (a * (a + b)) + d / (c * (c + d)))
    critical = NormalDist().inv_cdf(0.975)
    expected = (
        math.exp(math.log(ratio) - critical * se),
        math.exp(math.log(ratio) + critical * se),
    )
    assert ci_wald_rr(a, b, c, d, design=COHORT) == pytest.approx(expected, rel=2e-14)
    assert ci_wald_rr(0, 10, 5, 15, design=COHORT)[0] == 0.0
    assert math.isinf(ci_wald_rr(5, 15, 0, 10, design=COHORT)[1])
    assert ci_wald_rr(0, 10, 0, 10, design=COHORT) == (0.0, math.inf)


def test_wald_rr_reciprocity_nesting_validation_and_design() -> None:
    lower, upper = ci_wald_rr(12, 5, 8, 10, design=COHORT)
    swapped_lower, swapped_upper = ci_wald_rr(8, 10, 12, 5, design=COHORT)
    assert lower == pytest.approx(1 / swapped_upper, rel=2e-14)
    assert upper == pytest.approx(1 / swapped_lower, rel=2e-14)
    ci_90 = ci_wald_rr(12, 5, 8, 10, alpha=0.10, design=COHORT)
    ci_99 = ci_wald_rr(12, 5, 8, 10, alpha=0.01, design=COHORT)
    assert ci_99[0] < ci_90[0] and ci_90[1] < ci_99[1]
    with pytest.raises(ValidationError, match="alpha"):
        ci_wald_rr(12, 5, 8, 10, alpha=math.nan, design=COHORT)
    with pytest.raises(ValidationError, match="comparison group"):
        ci_wald_rr(0, 0, 8, 10, design=COHORT)
    with pytest.raises(DesignError, match="requires"):
        ci_wald_rr(12, 5, 8, 10, design=Design.CASE_CONTROL_FIXED_MARGIN)
