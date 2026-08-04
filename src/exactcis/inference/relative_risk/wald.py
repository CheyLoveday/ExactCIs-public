"""Log-Wald intervals for independent-binomial ratios."""

from __future__ import annotations

import math

from exactcis._numerics import normal_quantile
from exactcis._validation import validate_alpha, validate_independent_groups
from exactcis.estimands import Design, Estimand, get_method_spec
from exactcis.exceptions import DesignError


def ci_wald_rr(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float = 0.05,
    *,
    design: Design,
) -> tuple[float, float]:
    """Return an asymptotic log-Wald risk/prevalence-ratio interval.

    A 0.5 correction is used only to calculate finite sides when a zero cell
    is present. The mathematical endpoint remains zero when ``a == 0`` and
    infinity when ``c == 0``. If both event counts are zero, the returned set
    is the full non-negative extended parameter space.
    """
    if design not in {Design.COHORT_BINOMIAL, Design.CROSS_SECTIONAL}:
        raise DesignError(
            "risk/prevalence-ratio inference requires Design.COHORT_BINOMIAL "
            "or Design.CROSS_SECTIONAL"
        )
    get_method_spec(design, Estimand.RR, "wald_rr")
    a, b, c, d = validate_independent_groups(a, b, c, d)
    alpha = validate_alpha(alpha)
    if a == 0 and c == 0:
        return 0.0, math.inf
    correction = 0.5 if 0 in (a, b, c, d) else 0.0
    a_f, b_f, c_f, d_f = (value + correction for value in (a, b, c, d))
    n1, n0 = a_f + b_f, c_f + d_f
    ratio = (a_f / n1) / (c_f / n0)
    standard_error = math.sqrt(b_f / (a_f * n1) + d_f / (c_f * n0))
    critical = normal_quantile(1.0 - alpha / 2.0)
    lower = math.exp(math.log(ratio) - critical * standard_error)
    upper = math.exp(math.log(ratio) + critical * standard_error)
    if a == 0:
        lower = 0.0
    if c == 0:
        upper = math.inf
    return lower, upper


__all__ = ["ci_wald_rr"]
