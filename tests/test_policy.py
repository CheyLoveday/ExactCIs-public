"""Design-aware policy and public result contracts."""

from __future__ import annotations

import math

import pytest
from exactcis.results import InferenceResult

from exactcis.estimands import Design, Estimand
from exactcis.estimation import compute_or_with_policy, compute_rr_with_policy
from exactcis.exceptions import (
    DesignError,
    NonIdentifiableError,
    UnsupportedMethodError,
)


@pytest.mark.parametrize("method", ("conditional", "midp", "minlike", "blaker"))
def test_fixed_margin_policy_routes_only_named_exact_method(method) -> None:
    result = compute_or_with_policy(
        12,
        5,
        8,
        10,
        design=Design.CASE_CONTROL_FIXED_MARGIN,
        method=method,
    )
    assert isinstance(result, InferenceResult)
    assert result.method == method
    assert result.estimand is Estimand.OR
    assert result.lower <= result.point <= result.upper
    assert result.status == "stable"


@pytest.mark.parametrize("method", ("wald", "wald_haldane"))
@pytest.mark.parametrize("design", (Design.COHORT_BINOMIAL, Design.CROSS_SECTIONAL))
def test_product_binomial_or_policy(method, design) -> None:
    result = compute_or_with_policy(12, 5, 8, 10, design=design, method=method)
    assert result.design is design
    assert result.method == method
    assert result.lower <= result.point <= result.upper


@pytest.mark.parametrize("method", ("score_rr", "wald_rr"))
@pytest.mark.parametrize("design", (Design.COHORT_BINOMIAL, Design.CROSS_SECTIONAL))
def test_ratio_policy_names_risk_or_prevalence_design(method, design) -> None:
    result = compute_rr_with_policy(12, 5, 8, 10, design=design, method=method)
    assert result.design is design
    assert result.estimand is Estimand.RR
    assert result.method == method
    assert result.lower <= result.point <= result.upper


def test_policy_defaults_are_stable_registry_methods() -> None:
    assert (
        compute_or_with_policy(
            12, 5, 8, 10, design=Design.CASE_CONTROL_FIXED_MARGIN
        ).method
        == "conditional"
    )
    assert (
        compute_or_with_policy(12, 5, 8, 10, design=Design.COHORT_BINOMIAL).method
        == "wald"
    )
    assert (
        compute_rr_with_policy(12, 5, 8, 10, design=Design.COHORT_BINOMIAL).method
        == "score_rr"
    )


def test_policy_refuses_unknown_wrong_design_and_nonidentifiable_routes() -> None:
    with pytest.raises(UnsupportedMethodError, match="available methods"):
        compute_or_with_policy(
            12,
            5,
            8,
            10,
            design=Design.CASE_CONTROL_FIXED_MARGIN,
            method="wald",
        )
    with pytest.raises(DesignError, match="not shipped"):
        compute_rr_with_policy(12, 5, 8, 10, design=Design.CASE_CONTROL_FIXED_MARGIN)
    with pytest.raises(DesignError, match="stratified data"):
        compute_or_with_policy(12, 5, 8, 10, design=Design.STRATIFIED_CASE_CONTROL)
    with pytest.raises(NonIdentifiableError, match="singleton support"):
        compute_or_with_policy(0, 0, 5, 5, design=Design.CASE_CONTROL_FIXED_MARGIN)
    with pytest.raises(NonIdentifiableError, match="both observed risks"):
        compute_rr_with_policy(0, 10, 0, 10, design=Design.COHORT_BINOMIAL)


def test_policy_preserves_structural_infinite_point_and_interval() -> None:
    result = compute_rr_with_policy(5, 15, 0, 10, design=Design.COHORT_BINOMIAL)
    assert math.isinf(result.point)
    assert math.isinf(result.upper)
