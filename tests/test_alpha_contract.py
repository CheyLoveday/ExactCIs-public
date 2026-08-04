"""Release-wide tests for the certified significance-level contract."""

from __future__ import annotations

import math
from collections.abc import Callable

import pytest

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
from exactcis._validation import validate_alpha
from exactcis.exceptions import ValidationError

AlphaRoute = Callable[[float], object]
TABLE = (10, 20, 5, 25)
STRATA = (TABLE, (8, 22, 4, 26))


def _fixed(method: Callable[..., object]) -> AlphaRoute:
    return lambda alpha: method(
        *TABLE,
        alpha=alpha,
        design=Design.CASE_CONTROL_FIXED_MARGIN,
    )


def _cohort(method: Callable[..., object]) -> AlphaRoute:
    return lambda alpha: method(
        *TABLE,
        alpha=alpha,
        design=Design.COHORT_BINOMIAL,
    )


def _or_policy(alpha: float) -> object:
    return compute_or_with_policy(
        *TABLE,
        alpha=alpha,
        design=Design.COHORT_BINOMIAL,
        method="wald",
    )


def _rr_policy(alpha: float) -> object:
    return compute_rr_with_policy(
        *TABLE,
        alpha=alpha,
        design=Design.COHORT_BINOMIAL,
        method="wald_rr",
    )


def _pooled_policy(alpha: float) -> object:
    return compute_pooled_or(
        STRATA,
        alpha=alpha,
        design=Design.STRATIFIED_CASE_CONTROL,
    )


ALPHA_ROUTES: tuple[tuple[str, AlphaRoute], ...] = (
    ("ci_wald", _cohort(ci_wald)),
    ("ci_wald_haldane", _cohort(ci_wald_haldane)),
    ("ci_score_rr", _cohort(ci_score_rr)),
    ("ci_wald_rr", _cohort(ci_wald_rr)),
    ("exact_ci_conditional", _fixed(exact_ci_conditional)),
    ("exact_ci_midp", _fixed(exact_ci_midp)),
    ("exact_ci_minlike", _fixed(exact_ci_minlike)),
    ("exact_ci_blaker", _fixed(exact_ci_blaker)),
    ("compute_or_with_policy", _or_policy),
    ("compute_rr_with_policy", _rr_policy),
    ("compute_pooled_or", _pooled_policy),
)


@pytest.mark.parametrize(
    ("route_name", "route"),
    ALPHA_ROUTES,
    ids=[name for name, _route in ALPHA_ROUTES],
)
@pytest.mark.parametrize(
    "alpha",
    (
        1e-20,
        math.nextafter(0.0, 1.0),
        1.0 - 1e-13,
        math.nextafter(1.0, 0.0),
    ),
    ids=(
        "rounds-normal-tail-to-one",
        "smallest-positive-float",
        "near-upper-stability-boundary",
        "largest-float-below-one",
    ),
)
def test_extreme_alpha_is_rejected_before_numerical_dispatch(
    route_name: str,
    route: AlphaRoute,
    alpha: float,
) -> None:
    """No stable route may leak a backend error or a search sentinel."""
    del route_name
    with pytest.raises(ValidationError, match="numerical stability"):
        route(alpha)


@pytest.mark.parametrize("alpha", (1e-12, 1.0 - 1e-12))
def test_certified_alpha_boundary_is_open(alpha: float) -> None:
    with pytest.raises(ValidationError, match="numerical stability"):
        validate_alpha(alpha)


@pytest.mark.parametrize(
    "alpha",
    (
        math.nextafter(1e-12, math.inf),
        math.nextafter(1.0 - 1e-12, 0.0),
    ),
)
def test_values_immediately_inside_certified_alpha_domain_are_accepted(
    alpha: float,
) -> None:
    assert validate_alpha(alpha) == alpha
