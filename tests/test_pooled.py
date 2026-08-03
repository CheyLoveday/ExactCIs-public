"""Prespecified independent-strata Mantel-Haenszel checks."""

from __future__ import annotations

import math

import pytest

from exactcis.estimands import Design
from exactcis.estimation import compute_pooled_or
from exactcis.exceptions import DesignError, NonIdentifiableError, ValidationError
from exactcis.results import PooledORResult
from tests.conftest import load_reference


@pytest.mark.parametrize("case", load_reference("statsmodels_pooled.json")["cases"])
@pytest.mark.parametrize(
    "design", (Design.STRATIFIED_CASE_CONTROL, Design.STRATIFIED_COHORT)
)
def test_pooled_result_matches_statsmodels_reference(case, design) -> None:
    result = compute_pooled_or(case["strata"], design=design)
    assert isinstance(result, PooledORResult)
    assert result.point == pytest.approx(case["point"], rel=2e-12)
    assert (result.lower, result.upper) == pytest.approx(case["interval"], rel=2e-12)
    assert result.lower <= result.point <= result.upper
    assert result.strata == len(case["strata"])


def test_pooled_high_alpha_interval_nests_without_profile_search_sentinels() -> None:
    strata = [(10, 20, 5, 25), (8, 22, 4, 26)]
    results = [
        compute_pooled_or(
            strata,
            design=Design.STRATIFIED_CASE_CONTROL,
            alpha=alpha,
        )
        for alpha in (0.05, 0.50, 0.90)
    ]

    point = results[0].point
    assert all(result.point == pytest.approx(point) for result in results[1:])
    for result in results:
        assert 0.0 < result.lower < point < result.upper < math.inf
        assert not math.isclose(result.lower, math.exp(-30.0), abs_tol=1e-15)
        assert not math.isclose(result.upper, math.exp(30.0), rel_tol=1e-15)

    widest, middle, narrowest = results
    assert widest.lower < middle.lower < narrowest.lower < point
    assert point < narrowest.upper < middle.upper < widest.upper
    assert all(result.method == "mantel_haenszel" for result in results)
    assert all("Mantel-Haenszel" in result.construction for result in results)


def test_pooled_row_or_column_swap_reciprocates_result() -> None:
    strata = [(12, 5, 8, 10), (8, 2, 15, 20)]
    result = compute_pooled_or(strata, design=Design.STRATIFIED_CASE_CONTROL)
    for swapped in (
        [(c, d, a, b) for a, b, c, d in strata],
        [(b, a, d, c) for a, b, c, d in strata],
    ):
        transformed = compute_pooled_or(swapped, design=Design.STRATIFIED_CASE_CONTROL)
        assert result.point == pytest.approx(1 / transformed.point, rel=2e-14)
        assert result.lower == pytest.approx(1 / transformed.upper, rel=2e-14)
        assert result.upper == pytest.approx(1 / transformed.lower, rel=2e-14)


def test_pooled_boundary_and_input_failures_are_explicit() -> None:
    with pytest.raises(NonIdentifiableError, match="cross-products"):
        compute_pooled_or([(0, 5, 5, 10)], design=Design.STRATIFIED_CASE_CONTROL)
    with pytest.raises(ValidationError, match="no observations"):
        compute_pooled_or([(0, 0, 0, 0)], design=Design.STRATIFIED_CASE_CONTROL)
    with pytest.raises(ValidationError, match="at least one stratum"):
        compute_pooled_or([], design=Design.STRATIFIED_CASE_CONTROL)
    with pytest.raises(DesignError, match="requires"):
        compute_pooled_or([(12, 5, 8, 10)], design=Design.COHORT_BINOMIAL)
    with pytest.raises(ValidationError, match="alpha"):
        compute_pooled_or(
            [(12, 5, 8, 10)],
            design=Design.STRATIFIED_CASE_CONTROL,
            alpha=math.nan,
        )


def test_generator_of_strata_is_materialized_once() -> None:
    strata = ((value, 5, 8, 10) for value in (12, 13))
    result = compute_pooled_or(strata, design=Design.STRATIFIED_CASE_CONTROL)
    assert result.strata == 2
