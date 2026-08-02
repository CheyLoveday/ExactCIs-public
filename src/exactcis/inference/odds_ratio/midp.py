"""Mid-P conditional odds-ratio confidence intervals."""

from __future__ import annotations

from exactcis.estimands import Design
from exactcis.inference.odds_ratio._common import (
    equal_tail_interval,
    require_fixed_margin_design,
    validated_conditional_inputs,
)


def exact_ci_midp(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float = 0.05,
    *,
    design: Design | None = None,
) -> tuple[float, float]:
    """Return a fixed-margin Mid-P confidence interval for an odds ratio.

    Each one-sided tail includes half the observed probability mass. Mid-P
    reduces discreteness but is not advertised as guaranteeing nominal
    coverage at every parameter value. Endpoint and failure semantics match
    :func:`exact_ci_conditional`.
    """
    require_fixed_margin_design(design)
    a, b, c, d, alpha = validated_conditional_inputs(a, b, c, d, alpha)
    return equal_tail_interval(a, b, c, d, alpha, midp=True)


__all__ = ["exact_ci_midp"]
