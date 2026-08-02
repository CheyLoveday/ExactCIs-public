"""Asymptotic log-Wald odds-ratio intervals."""

from __future__ import annotations

import math

from exactcis._numerics import normal_quantile
from exactcis._validation import validate_alpha, validate_independent_groups
from exactcis.estimands import Design, Estimand, get_method_spec
from exactcis.exceptions import NonIdentifiableError


def _wald_interval(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float,
    *,
    always_correct: bool,
) -> tuple[float, float]:
    table = validate_independent_groups(a, b, c, d)
    alpha = validate_alpha(alpha)
    if table[0] + table[2] == 0 or table[1] + table[3] == 0:
        raise NonIdentifiableError(
            "the odds ratio is not estimable when an outcome column is empty"
        )
    correction = 0.5 if always_correct or 0 in table else 0.0
    a_f, b_f, c_f, d_f = (value + correction for value in table)
    log_point = math.log((a_f * d_f) / (b_f * c_f))
    standard_error = math.sqrt(1.0 / a_f + 1.0 / b_f + 1.0 / c_f + 1.0 / d_f)
    critical = normal_quantile(1.0 - alpha / 2.0)
    return (
        math.exp(log_point - critical * standard_error),
        math.exp(log_point + critical * standard_error),
    )


def _require_product_binomial_or(design: Design | None, method: str) -> Design:
    if design not in {Design.COHORT_BINOMIAL, Design.CROSS_SECTIONAL}:
        from exactcis.exceptions import DesignError

        raise DesignError(
            "Wald odds-ratio inference requires Design.COHORT_BINOMIAL or "
            "Design.CROSS_SECTIONAL"
        )
    get_method_spec(design, Estimand.OR, method)
    return design


def ci_wald(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float = 0.05,
    *,
    design: Design | None = None,
) -> tuple[float, float]:
    """Return a log-Wald OR interval, correcting only zero-cell tables.

    The table is interpreted as two independent observed groups. If any cell
    is zero, 0.5 is added to all four cells before calculating both the point
    estimator and interval. Empty groups and empty outcome columns fail
    explicitly. This construction is asymptotic and can be unreliable for
    sparse data.
    """
    _require_product_binomial_or(design, "wald")
    return _wald_interval(a, b, c, d, alpha, always_correct=False)


def ci_wald_haldane(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float = 0.05,
    *,
    design: Design | None = None,
) -> tuple[float, float]:
    """Return a log-Wald OR interval after adding 0.5 to every cell."""
    _require_product_binomial_or(design, "wald_haldane")
    return _wald_interval(a, b, c, d, alpha, always_correct=True)


__all__ = ["ci_wald", "ci_wald_haldane"]
