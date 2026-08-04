"""Ordered fixed-margin exact confidence intervals."""

from __future__ import annotations

from exactcis._numerics import ordered_interval
from exactcis.estimands import Design
from exactcis.inference.odds_ratio._common import (
    require_fixed_margin_design,
    validated_conditional_inputs,
)


def exact_ci_minlike(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float = 0.05,
    *,
    design: Design,
) -> tuple[float, float]:
    """Invert the inclusive Fisher-Irwin minimum-likelihood ordering."""
    require_fixed_margin_design(design)
    a, b, c, d, alpha = validated_conditional_inputs(a, b, c, d, alpha)
    return ordered_interval(a, b, c, d, alpha, ordering="minlike")


def exact_ci_blaker(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float = 0.05,
    *,
    design: Design,
) -> tuple[float, float]:
    """Invert Blaker's inclusive acceptability ordering.

    Acceptability for support value ``x`` is the smaller inclusive lower or
    upper tail probability. Discrete crossings are bracketed and certified;
    a failed crossing raises rather than returning a different interval.
    """
    require_fixed_margin_design(design)
    a, b, c, d, alpha = validated_conditional_inputs(a, b, c, d, alpha)
    return ordered_interval(a, b, c, d, alpha, ordering="blaker")


__all__ = ["exact_ci_blaker", "exact_ci_minlike"]
