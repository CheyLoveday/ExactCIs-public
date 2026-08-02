"""Release-critical Koopman-Nam risk-ratio checks."""

from __future__ import annotations

import itertools
import math

import pytest

import exactcis.inference.relative_risk.score as score_module
from exactcis.estimands import Design
from exactcis.exceptions import DesignError, NumericalError, ValidationError
from exactcis.inference.relative_risk import ci_score_rr
from tests.conftest import endpoint, load_reference

COHORT = Design.COHORT_BINOMIAL


@pytest.mark.parametrize("case", load_reference("propcis_rr.json")["cases"])
def test_score_interval_matches_r_propcis_oracle(case) -> None:
    expected = tuple(endpoint(value) for value in case["interval"])
    observed = ci_score_rr(*case["table"], design=COHORT)
    tolerance = 1e-4 if case["boundary"] else 3e-8
    assert observed == pytest.approx(expected, rel=tolerance, abs=5e-10)


def test_score_statistic_matches_defining_equation() -> None:
    a, b, c, d = 12, 5, 8, 10
    ratio = 2.0
    p0 = score_module._constrained_control_risk(a, b, c, d, ratio)
    p1 = ratio * p0
    contrast = a / (a + b) - ratio * c / (c + d)
    variance = p1 * (1 - p1) / (a + b) + ratio**2 * p0 * (1 - p0) / (c + d)
    expected = contrast / math.sqrt(variance)
    assert score_module._score_statistic(a, b, c, d, ratio) == pytest.approx(
        expected, rel=2e-14
    )
    assert expected == pytest.approx(-0.7284411605251533, rel=2e-14)


@pytest.mark.parametrize("a,c", tuple(itertools.product((0, 1, 4, 5), (0, 1, 6, 7))))
def test_score_boundary_cartesian_product(a, c) -> None:
    table = (a, 5 - a, c, 7 - c)
    lower, upper = ci_score_rr(*table, design=COHORT)
    assert 0.0 <= lower <= upper
    if a == 0:
        assert lower == 0.0
    if c == 0:
        assert math.isinf(upper)
    elif a == 0:
        assert math.isfinite(upper)


def test_score_reciprocity_and_confidence_level_nesting() -> None:
    lower, upper = ci_score_rr(12, 5, 8, 10, design=COHORT)
    swapped_lower, swapped_upper = ci_score_rr(8, 10, 12, 5, design=COHORT)
    assert lower == pytest.approx(1 / swapped_upper, rel=2e-9)
    assert upper == pytest.approx(1 / swapped_lower, rel=2e-9)
    ci_90 = ci_score_rr(12, 5, 8, 10, alpha=0.10, design=COHORT)
    ci_95 = ci_score_rr(12, 5, 8, 10, alpha=0.05, design=COHORT)
    ci_99 = ci_score_rr(12, 5, 8, 10, alpha=0.01, design=COHORT)
    assert ci_99[0] < ci_95[0] < ci_90[0]
    assert ci_90[1] < ci_95[1] < ci_99[1]


@pytest.mark.parametrize("design", (Design.COHORT_BINOMIAL, Design.CROSS_SECTIONAL))
def test_score_supports_only_identified_independent_group_designs(design) -> None:
    lower, upper = ci_score_rr(12, 5, 8, 10, design=design)
    assert lower < (12 / 17) / (8 / 18) < upper
    with pytest.raises(DesignError, match="requires"):
        ci_score_rr(12, 5, 8, 10, design=Design.CASE_CONTROL_FIXED_MARGIN)


@pytest.mark.parametrize("table", ((0, 0, 1, 4), (1, 4, 0, 0), (0, 0, 0, 0)))
def test_score_rejects_empty_groups(table) -> None:
    with pytest.raises(ValidationError, match="comparison group"):
        ci_score_rr(*table, design=COHORT)


@pytest.mark.parametrize("alpha", (0.0, 1.0, -0.1, math.nan))
def test_score_rejects_invalid_alpha(alpha) -> None:
    with pytest.raises(ValidationError, match="alpha"):
        ci_score_rr(12, 5, 8, 10, alpha=alpha, design=COHORT)


def test_score_inversion_failure_does_not_substitute_wald(monkeypatch) -> None:
    def fail(*args, **kwargs):
        raise NumericalError("forced score failure")

    monkeypatch.setattr(score_module, "_invert_score", fail)
    with pytest.raises(NumericalError, match="forced score failure"):
        ci_score_rr(12, 5, 8, 10, design=COHORT)
