"""Shared fixed-margin interval calculations."""

from __future__ import annotations

import math

from exactcis._numerics import (
    exp_parameter,
    fnch_probabilities,
    solve_monotone_log_parameter,
    support_bounds,
)
from exactcis._validation import validate_alpha, validate_table
from exactcis.estimands import Design
from exactcis.exceptions import DesignError, NumericalError


def require_fixed_margin_design(design: Design | None) -> Design:
    """Require the single-table conditional sampling design."""
    if design is not Design.CASE_CONTROL_FIXED_MARGIN:
        raise DesignError(
            "conditional odds-ratio inference requires "
            "Design.CASE_CONTROL_FIXED_MARGIN"
        )
    return design


def validated_conditional_inputs(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float,
) -> tuple[int, int, int, int, float]:
    """Validate one integer table and significance level."""
    table = validate_table(a, b, c, d)
    return (*table, validate_alpha(alpha))


def equal_tail_interval(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float,
    *,
    midp: bool,
) -> tuple[float, float]:
    """Invert inclusive or mid-P one-sided FNCH tails."""
    n1, n0, events = a + b, c + d, a + c
    lower_support, upper_support = support_bounds(n1, n0, events)
    if lower_support == upper_support:
        return 0.0, math.inf

    target = alpha / 2.0

    def tail(log_odds: float, *, upper: bool) -> float:
        support, probabilities = fnch_probabilities(n1, n0, events, log_odds)
        index = support.index(a)
        observed_mass = probabilities[index]
        if upper:
            strict = math.fsum(probabilities[index + 1 :])
        else:
            strict = math.fsum(probabilities[:index])
        value = strict + (0.5 if midp else 1.0) * observed_mass
        if not math.isfinite(value) or not -1e-15 <= value <= 1.0 + 1e-12:
            raise NumericalError("conditional tail probability failed certification")
        return min(1.0, max(0.0, value))

    method = "midp" if midp else "conditional"
    if a == lower_support:
        lower = 0.0
    else:
        lower_log = solve_monotone_log_parameter(
            lambda value: tail(value, upper=True),
            target,
            increasing=True,
            method=method,
            side="lower",
        )
        lower = exp_parameter(lower_log)

    if a == upper_support:
        upper = math.inf
    else:
        upper_log = solve_monotone_log_parameter(
            lambda value: tail(value, upper=False),
            target,
            increasing=False,
            method=method,
            side="upper",
        )
        upper = exp_parameter(upper_log)

    if lower < 0.0 or lower > upper:
        raise NumericalError(
            "conditional inversion returned invalid bounds",
            method=method,
        )
    return lower, upper


__all__ = [
    "equal_tail_interval",
    "require_fixed_margin_design",
    "validated_conditional_inputs",
]
