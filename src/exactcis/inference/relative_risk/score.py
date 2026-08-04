"""Koopman-Nam score intervals for independent-binomial ratios."""

from __future__ import annotations

import math

from exactcis._numerics import normal_quantile
from exactcis._validation import validate_alpha, validate_independent_groups
from exactcis.estimands import Design, Estimand, get_method_spec
from exactcis.exceptions import NumericalError

_MAX_LOG_RATIO = 709.0


def _require_independent_ratio_design(design: Design, method: str) -> Design:
    if design not in {Design.COHORT_BINOMIAL, Design.CROSS_SECTIONAL}:
        from exactcis.exceptions import DesignError

        raise DesignError(
            "risk/prevalence-ratio inference requires Design.COHORT_BINOMIAL "
            "or Design.CROSS_SECTIONAL"
        )
    get_method_spec(design, Estimand.RR, method)
    return design


def _constrained_control_risk(
    a: int,
    b: int,
    c: int,
    d: int,
    ratio: float,
) -> float:
    """Return the restricted second-group risk under p1 = ratio * p0."""
    n1 = float(a + b)
    n0 = float(c + d)
    events = float(a + c)
    if events == 0.0:
        return 0.0
    total = n1 + n0
    if ratio >= 1.0:
        coef_a = total
        coef_b = n1 + c + (a + n0) / ratio
        coef_c = events / ratio
    else:
        coef_a = ratio * total
        coef_b = ratio * (n1 + c) + a + n0
        coef_c = events
    discriminant = coef_b * coef_b - 4.0 * coef_a * coef_c
    scale = max(coef_b * coef_b, 1.0)
    if discriminant < 0.0 and abs(discriminant) <= 64.0 * math.ulp(scale):
        discriminant = 0.0
    if discriminant < 0.0:
        raise NumericalError(
            "constrained risk-ratio likelihood has a negative discriminant",
            method="score_rr",
        )
    denominator = coef_b + math.sqrt(discriminant)
    if denominator <= 0.0 or not math.isfinite(denominator):
        raise NumericalError(
            "constrained risk-ratio MLE could not be evaluated", method="score_rr"
        )
    risk = 2.0 * coef_c / denominator
    return min(1.0, 1.0 / ratio, max(0.0, risk))


def _score_statistic(a: int, b: int, c: int, d: int, ratio: float) -> float:
    """Return the signed Koopman-Nam score statistic."""
    if not math.isfinite(ratio) or ratio <= 0.0:
        raise ValueError("the null ratio must be finite and positive")
    n1 = float(a + b)
    n0 = float(c + d)
    p0 = _constrained_control_risk(a, b, c, d, ratio)
    p1 = min(1.0, max(0.0, ratio * p0))
    contrast = a / n1 - ratio * (c / n0)
    # Algebraically equivalent to ratio**2 * p0*(1-p0)/n0, but avoids
    # overflow when ratio is close to the largest finite float.
    variance = p1 * (1.0 - p1) / n1 + ratio * p1 * (1.0 - p0) / n0
    if variance <= 0.0:
        if contrast == 0.0:
            return 0.0
        return math.copysign(math.inf, contrast)
    return contrast / math.sqrt(variance)


def _invert_score(
    a: int,
    b: int,
    c: int,
    d: int,
    target_score: float,
    *,
    side: str,
) -> float:
    if a > 0 and c > 0:
        center = math.log((a / (a + b)) / (c / (c + d)))
    else:
        center = 0.0

    def target(log_ratio: float) -> float:
        value = _score_statistic(a, b, c, d, math.exp(log_ratio)) - target_score
        if math.isnan(value):
            raise NumericalError(
                "score inversion produced NaN", method="score_rr", side=side
            )
        return value

    left = right = min(_MAX_LOG_RATIO, max(-_MAX_LOG_RATIO, center))
    f_left = f_right = target(center)
    if f_left == 0.0:
        return math.exp(center)
    span = 1.0
    while left > -_MAX_LOG_RATIO or right < _MAX_LOG_RATIO:
        if left > -_MAX_LOG_RATIO:
            left = max(-_MAX_LOG_RATIO, center - span)
            f_left = target(left)
        if right < _MAX_LOG_RATIO:
            right = min(_MAX_LOG_RATIO, center + span)
            f_right = target(right)
        if f_left == 0.0:
            return math.exp(left)
        if f_right == 0.0:
            return math.exp(right)
        if (f_left < 0.0 < f_right) or (f_right < 0.0 < f_left):
            break
        if left == -_MAX_LOG_RATIO and right == _MAX_LOG_RATIO:
            raise NumericalError(
                "unable to bracket the requested score bound",
                method="score_rr",
                side=side,
            )
        span *= 2.0

    for _ in range(220):
        middle = (left + right) / 2.0
        f_middle = target(middle)
        if f_middle == 0.0:
            left = right = middle
            break
        if (f_left < 0.0 < f_middle) or (f_middle < 0.0 < f_left):
            right, f_right = middle, f_middle
        else:
            left, f_left = middle, f_middle
        if right - left <= 2e-12 * max(1.0, abs(middle)):
            break
    root = (left + right) / 2.0
    residual = abs(target(root))
    scale = max(1.0, abs(f_left), abs(f_right), abs(residual))
    if not math.isfinite(residual) or residual > 1e-8 * scale:
        raise NumericalError(
            "score inversion failed its residual criterion",
            method="score_rr",
            side=side,
            diagnostics={"residual": residual, "scale": scale},
        )
    return math.exp(root)


def ci_score_rr(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float = 0.05,
    *,
    design: Design,
) -> tuple[float, float]:
    """Return a Koopman-Nam score interval for a risk/prevalence ratio.

    The rows are treated as two independent binomial groups. Under
    ``Design.CROSS_SECTIONAL`` the same row-proportion ratio is interpreted as
    a prevalence ratio. Empty groups are invalid. If both observed event
    counts are zero, the confidence set is ``(0, inf)``; otherwise structural
    zero and infinity endpoints are retained. Failed score inversion raises
    :class:`exactcis.NumericalError` and never falls back to Wald.
    """
    _require_independent_ratio_design(design, "score_rr")
    a, b, c, d = validate_independent_groups(a, b, c, d)
    alpha = validate_alpha(alpha)
    if a == 0 and c == 0:
        return 0.0, math.inf
    critical = normal_quantile(1.0 - alpha / 2.0)
    lower = 0.0 if a == 0 else _invert_score(a, b, c, d, critical, side="lower")
    upper = math.inf if c == 0 else _invert_score(a, b, c, d, -critical, side="upper")
    if lower < 0.0 or lower > upper:
        raise NumericalError(
            "score inversion returned invalid bounds", method="score_rr"
        )
    return lower, upper


__all__ = ["ci_score_rr"]
