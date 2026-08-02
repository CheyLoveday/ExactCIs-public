"""Prespecified independent-strata Mantel-Haenszel checks."""

from __future__ import annotations

import math

import pytest
from exactcis.results import PooledORResult

from exactcis.estimands import Design
from exactcis.estimation import compute_pooled_or
from exactcis.exceptions import DesignError, NonIdentifiableError, ValidationError
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


def test_pooled_confidence_interval_nests() -> None:
    strata = [(12, 5, 8, 10), (8, 2, 15, 20)]
    ci_90 = compute_pooled_or(strata, design=Design.STRATIFIED_CASE_CONTROL, alpha=0.10)
    ci_99 = compute_pooled_or(strata, design=Design.STRATIFIED_CASE_CONTROL, alpha=0.01)
    assert ci_99.lower < ci_90.lower and ci_90.upper < ci_99.upper


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
