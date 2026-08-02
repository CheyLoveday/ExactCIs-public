"""Equal-tail conditional odds-ratio confidence intervals."""

from __future__ import annotations

from exactcis.estimands import Design
from exactcis.inference.odds_ratio._common import (
    equal_tail_interval,
    require_fixed_margin_design,
    validated_conditional_inputs,
)


def exact_ci_conditional(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float = 0.05,
    *,
    design: Design | None = None,
) -> tuple[float, float]:
    """Return a central conditional confidence interval for an odds ratio.

    ``a, b, c, d`` follow the package table orientation. The construction
    conditions on both margins and inverts inclusive equal tails of Fisher's
    noncentral-hypergeometric law. Extended endpoints are represented by
    ``0.0`` and ``math.inf``. A singleton conditional support returns the full
    parameter space. Any failed numerical certification raises
    :class:`exactcis.NumericalError`; no alternate method is substituted.
    """
    require_fixed_margin_design(design)
    a, b, c, d, alpha = validated_conditional_inputs(a, b, c, d, alpha)
    return equal_tail_interval(a, b, c, d, alpha, midp=False)


__all__ = ["exact_ci_conditional"]
