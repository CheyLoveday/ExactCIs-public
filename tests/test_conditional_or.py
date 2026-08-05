"""Release gates for fixed-margin odds-ratio inference."""

from __future__ import annotations

import math

import pytest

import exactcis._numerics as numerics
from exactcis._numerics import ordered_p_value
from exactcis.estimands import Design
from exactcis.exceptions import DesignError, NumericalError, ValidationError
from exactcis.inference.odds_ratio import (
    exact_ci_blaker,
    exact_ci_conditional,
    exact_ci_midp,
    exact_ci_minlike,
)
from tests.conftest import endpoint, load_reference

FIXED = Design.CASE_CONTROL_FIXED_MARGIN
EXACT_METHODS = (
    exact_ci_conditional,
    exact_ci_midp,
    exact_ci_minlike,
    exact_ci_blaker,
)


@pytest.mark.parametrize("case", load_reference("conditional_mpmath.json")["cases"])
@pytest.mark.parametrize(
    ("key", "method"),
    (("conditional", exact_ci_conditional), ("midp", exact_ci_midp)),
)
def test_equal_tail_methods_match_80_digit_mpmath_reference(case, key, method) -> None:
    expected = tuple(endpoint(value) for value in case[key])
    observed = method(*case["table"], design=FIXED)
    assert observed == pytest.approx(expected, rel=2e-9, abs=2e-9)


@pytest.mark.parametrize("case", load_reference("exact2x2.json")["cases"])
@pytest.mark.parametrize(
    ("key", "method"),
    (("minlike", exact_ci_minlike), ("blaker", exact_ci_blaker)),
)
def test_ordered_methods_match_r_exact2x2_reference(case, key, method) -> None:
    expected = tuple(case[key]["interval"])
    observed = method(*case["table"], design=FIXED)
    assert observed == pytest.approx(expected, rel=2e-7, abs=2e-7)
    a, b, c, d = case["table"]
    p_value = ordered_p_value(
        a + b,
        c + d,
        a + c,
        a,
        math.log(case["theta"]),
        ordering=key,
    )
    assert p_value == pytest.approx(case[key]["p_value"], abs=2e-12)


CANONICAL_TABLES = (
    (10, 10, 10, 10),  # balanced and OR = 1
    (1, 99, 2, 198),  # rare event
    (0, 5, 5, 5),  # one zero cell
    (10, 0, 0, 10),  # two zero cells
    (0, 0, 5, 5),  # empty row and singleton support
    (0, 5, 0, 5),  # empty column and singleton support
    (5, 0, 0, 0),  # one nonzero cell and singleton support
    (0, 10, 10, 10),  # lower support boundary
    (99, 1, 50, 50),  # extreme imbalance
    (50, 950, 25, 975),  # large counts
    (1, 9, 11, 3),  # OR below one
    (12, 5, 8, 10),  # OR above one
)


@pytest.mark.parametrize("method", EXACT_METHODS)
@pytest.mark.parametrize("table", CANONICAL_TABLES)
def test_canonical_families_have_certified_endpoint_domains(method, table) -> None:
    lower, upper = method(*table, design=FIXED)
    assert 0.0 <= lower <= upper
    assert math.isfinite(lower)
    assert upper >= 0.0 and not math.isnan(upper)


@pytest.mark.parametrize("method", EXACT_METHODS)
def test_singleton_support_is_full_parameter_space(method) -> None:
    assert method(0, 0, 5, 5, design=FIXED) == (0.0, math.inf)
    assert method(0, 5, 0, 5, design=FIXED) == (0.0, math.inf)


@pytest.mark.parametrize("method", EXACT_METHODS)
def test_support_boundaries_have_structural_extended_endpoints(method) -> None:
    lower_min, upper_min = method(0, 10, 10, 10, design=FIXED)
    lower_max, upper_max = method(10, 0, 0, 10, design=FIXED)
    assert lower_min == 0.0 and math.isfinite(upper_min)
    assert lower_max > 0.0 and math.isinf(upper_max)


@pytest.mark.parametrize("method", EXACT_METHODS)
def test_row_and_column_swaps_reciprocate_interval(method) -> None:
    lower, upper = method(12, 5, 8, 10, design=FIXED)
    for swapped in ((8, 10, 12, 5), (5, 12, 10, 8)):
        swapped_lower, swapped_upper = method(*swapped, design=FIXED)
        assert lower == pytest.approx(1.0 / swapped_upper, rel=3e-10)
        assert upper == pytest.approx(1.0 / swapped_lower, rel=3e-10)


@pytest.mark.parametrize("method", EXACT_METHODS)
def test_confidence_sets_weakly_widen_with_confidence_level(method) -> None:
    lower_90, upper_90 = method(12, 5, 8, 10, alpha=0.10, design=FIXED)
    lower_95, upper_95 = method(12, 5, 8, 10, alpha=0.05, design=FIXED)
    lower_99, upper_99 = method(12, 5, 8, 10, alpha=0.01, design=FIXED)
    assert lower_99 <= lower_95 <= lower_90
    assert upper_90 <= upper_95 <= upper_99


@pytest.mark.parametrize("method", EXACT_METHODS)
def test_direct_exact_methods_require_declared_fixed_margin_design(method) -> None:
    with pytest.raises(TypeError, match="design"):
        method(12, 5, 8, 10)
    with pytest.raises(DesignError, match="CASE_CONTROL_FIXED_MARGIN"):
        method(12, 5, 8, 10, design=Design.COHORT_BINOMIAL)


@pytest.mark.parametrize("method", EXACT_METHODS)
@pytest.mark.parametrize("alpha", (0.0, 1.0, -0.1, math.nan))
def test_exact_methods_reject_invalid_alpha(method, alpha) -> None:
    with pytest.raises(ValidationError, match="alpha"):
        method(12, 5, 8, 10, alpha=alpha, design=FIXED)


@pytest.mark.parametrize("method", EXACT_METHODS)
@pytest.mark.parametrize("table", ((-1, 2, 3, 4), (1.5, 2, 3, 4), (True, 2, 3, 4)))
def test_exact_methods_reject_invalid_counts(method, table) -> None:
    with pytest.raises(ValidationError, match="counts"):
        method(*table, design=FIXED)


def test_equal_tail_callback_failure_is_not_a_vacuous_interval(monkeypatch) -> None:
    # The distribution-evaluation seam is PreparedMargins.probabilities: both the
    # equal-tail and the ordered inversions reach the FNCH vector through it.
    def fail(self, log_odds):
        raise NumericalError("forced FNCH failure")

    monkeypatch.setattr(numerics.PreparedMargins, "probabilities", fail)
    with pytest.raises(NumericalError, match="forced FNCH failure"):
        exact_ci_conditional(12, 5, 8, 10, design=FIXED)


def test_ordered_callback_failure_is_not_a_different_method(monkeypatch) -> None:
    def fail(self, log_odds):
        raise NumericalError("forced ordered failure")

    monkeypatch.setattr(numerics.PreparedMargins, "probabilities", fail)
    with pytest.raises(NumericalError, match="forced ordered failure"):
        exact_ci_blaker(12, 5, 8, 10, design=FIXED)


def test_unallocatable_support_is_a_numerical_error() -> None:
    """Preparation runs before the solver's guarded region, so it guards itself.

    This table passes count validation (both counts are below the 1e12 bound) but
    its support cannot be allocated. Without a guard inside preparation the
    failure escapes as a bare MemoryError instead of the documented
    NumericalError.
    """
    with pytest.raises(NumericalError):
        exact_ci_conditional(10**11, 1, 1, 10**11, design=FIXED)
