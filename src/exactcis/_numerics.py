"""Dependency-free numerical primitives used by the public methods."""

from __future__ import annotations

import math
from collections.abc import Callable
from statistics import NormalDist

from exactcis.exceptions import NumericalError

_LOG_LIMIT = 740.0
_ROOT_TOL = 2e-12


def normal_quantile(probability: float) -> float:
    """Return the standard-normal quantile using the Python standard library."""
    if not 0.0 < probability < 1.0 or not math.isfinite(probability):
        raise ValueError("normal probability must be finite and in (0, 1)")
    return NormalDist().inv_cdf(probability)


def support_bounds(n1: int, n0: int, events: int) -> tuple[int, int]:
    """Return the support of the first-row event count at fixed margins."""
    return max(0, events - n0), min(events, n1)


def _log_choose(n: int, k: int) -> float:
    """Return log(C(n, k)) without catastrophic cancellation.

    Small supports use exact ``math.comb``; large supports use an iterative
    product in log space. The previous three-term ``lgamma`` form can lose
    precision for large, unbalanced arguments.
    """
    if k < 0 or k > n:
        return -math.inf
    if k == 0 or k == n:
        return 0.0
    k = min(k, n - k)
    if n <= 10_000:
        return math.log(math.comb(n, k))
    result = 0.0
    for i in range(k):
        result += math.log(n - i) - math.log(i + 1)
    return result


def fnch_probabilities(
    n1: int,
    n0: int,
    events: int,
    log_odds: float,
) -> tuple[tuple[int, ...], tuple[float, ...]]:
    """Evaluate a Fisher noncentral-hypergeometric probability vector.

    The implementation uses a log-sum-exp normalization over the complete
    finite support. It raises :class:`NumericalError` instead of returning a
    synthetic distribution when normalization cannot be certified.
    """
    lower, upper = support_bounds(n1, n0, events)
    support = tuple(range(lower, upper + 1))
    if not support:
        raise NumericalError("conditional support is empty", method="FNCH")
    if lower == upper:
        return support, (1.0,)
    if log_odds == -math.inf:
        return support, tuple(1.0 if value == lower else 0.0 for value in support)
    if log_odds == math.inf:
        return support, tuple(1.0 if value == upper else 0.0 for value in support)
    if not math.isfinite(log_odds):
        raise NumericalError(
            "log odds must be finite or an extended endpoint", method="FNCH"
        )

    log_masses = tuple(
        _log_choose(n1, value) + _log_choose(n0, events - value) + value * log_odds
        for value in support
    )
    anchor = max(log_masses)
    if not math.isfinite(anchor):
        raise NumericalError("conditional mass anchor is not finite", method="FNCH")
    scaled = tuple(math.exp(value - anchor) for value in log_masses)
    total = math.fsum(scaled)
    if not math.isfinite(total) or total <= 0.0:
        raise NumericalError("conditional mass normalization failed", method="FNCH")
    probabilities = tuple(value / total for value in scaled)
    probability_sum = math.fsum(probabilities)
    if (
        any(value < 0.0 or not math.isfinite(value) for value in probabilities)
        or abs(probability_sum - 1.0) > 2e-13
    ):
        raise NumericalError(
            "conditional probabilities failed certification",
            method="FNCH",
            diagnostics={"sum": probability_sum, "support_size": len(support)},
        )
    return support, probabilities


def conditional_mean(n1: int, n0: int, events: int, log_odds: float) -> float:
    """Return the first-row conditional mean under one log odds ratio."""
    support, probabilities = fnch_probabilities(n1, n0, events, log_odds)
    return math.fsum(
        value * probability for value, probability in zip(support, probabilities)
    )


def solve_monotone_log_parameter(
    function: Callable[[float], float],
    target: float,
    *,
    increasing: bool,
    method: str,
    side: str,
) -> float:
    """Solve a certified monotone equation on the extended log-OR domain."""
    left = -_LOG_LIMIT
    right = _LOG_LIMIT
    try:
        f_left = function(left)
        f_right = function(right)
    except NumericalError:
        raise
    except (OverflowError, ValueError, ZeroDivisionError, MemoryError) as exc:
        raise NumericalError(
            "endpoint evaluation failed during inversion",
            method=method,
            side=side,
        ) from exc
    values = (f_left, f_right, target)
    if any(not math.isfinite(value) for value in values):
        raise NumericalError(
            "non-finite value encountered during inversion",
            method=method,
            side=side,
        )
    bracketed = (
        f_left <= target <= f_right if increasing else f_right <= target <= f_left
    )
    if not bracketed:
        raise NumericalError(
            "monotone confidence-limit equation was not bracketed",
            method=method,
            side=side,
            diagnostics={"left": f_left, "right": f_right, "target": target},
        )

    for _ in range(220):
        middle = (left + right) / 2.0
        value = function(middle)
        if not math.isfinite(value):
            raise NumericalError(
                "non-finite value encountered during inversion",
                method=method,
                side=side,
            )
        if (value < target) == increasing:
            left = middle
        else:
            right = middle
        if right - left <= _ROOT_TOL * max(1.0, abs(middle)):
            break
    else:
        raise NumericalError(
            "confidence-limit inversion exceeded its iteration budget",
            method=method,
            side=side,
        )

    root = (left + right) / 2.0
    residual = abs(function(root) - target)
    scale = max(1.0, abs(target))
    if residual > 2e-10 * scale:
        raise NumericalError(
            "confidence-limit inversion failed its residual criterion",
            method=method,
            side=side,
            diagnostics={"residual": residual, "scale": scale},
        )
    return root


def exp_parameter(log_value: float) -> float:
    """Map a finite/extended log parameter to the non-negative OR scale."""
    if log_value == -math.inf:
        return 0.0
    if log_value == math.inf or log_value > math.log(
        float.fromhex("0x1.fffffffffffffp+1023")
    ):
        return math.inf
    value = math.exp(log_value)
    return 0.0 if value < float.fromhex("0x0.0000000000001p-1022") else value


def conditional_mle(
    a: int,
    b: int,
    c: int,
    d: int,
) -> float:
    """Return the conditional MLE under the fixed-margin FNCH model."""
    n1, n0, events = a + b, c + d, a + c
    lower, upper = support_bounds(n1, n0, events)
    if lower == upper:
        return math.nan
    if a == lower:
        return 0.0
    if a == upper:
        return math.inf
    log_value = solve_monotone_log_parameter(
        lambda value: conditional_mean(n1, n0, events, value),
        float(a),
        increasing=True,
        method="conditional_mle",
        side="point",
    )
    return exp_parameter(log_value)


def ordered_p_value(
    n1: int,
    n0: int,
    events: int,
    observed: int,
    log_odds: float,
    *,
    ordering: str,
) -> float:
    """Return an inclusive minimum-likelihood or Blaker ordered p-value."""
    support, probabilities = fnch_probabilities(n1, n0, events, log_odds)
    try:
        index = support.index(observed)
    except ValueError as exc:
        raise NumericalError("observed count is outside conditional support") from exc
    if ordering == "minlike":
        order = probabilities
    elif ordering == "blaker":
        lower_tail: list[float] = []
        running = 0.0
        for probability in probabilities:
            running += probability
            lower_tail.append(running)
        upper_tail = [0.0] * len(probabilities)
        running = 0.0
        for position in range(len(probabilities) - 1, -1, -1):
            running += probabilities[position]
            upper_tail[position] = running
        order = tuple(min(low, high) for low, high in zip(lower_tail, upper_tail))
    else:
        raise ValueError(f"unknown conditional ordering {ordering!r}")

    threshold = math.nextafter(order[index] * (1.0 + 1e-10), math.inf)
    p_value = math.fsum(
        probability
        for probability, rank in zip(probabilities, order)
        if rank <= threshold
    )
    if not math.isfinite(p_value) or p_value < -1e-15 or p_value > 1.0 + 1e-12:
        raise NumericalError("ordered conditional p-value failed certification")
    return min(1.0, max(0.0, p_value))


def ordered_interval(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float,
    *,
    ordering: str,
) -> tuple[float, float]:
    """Invert one ordered conditional p-value without method substitution."""
    n1, n0, events = a + b, c + d, a + c
    support_lower, support_upper = support_bounds(n1, n0, events)
    if support_lower == support_upper:
        return 0.0, math.inf

    point = conditional_mle(a, b, c, d)
    if point == 0.0:
        center = -36.0
    elif math.isinf(point):
        center = 36.0
    else:
        center = math.log(point)

    def accepted(log_odds: float) -> bool:
        try:
            return (
                ordered_p_value(
                    n1,
                    n0,
                    events,
                    a,
                    log_odds,
                    ordering=ordering,
                )
                >= alpha
            )
        except (OverflowError, ValueError, ZeroDivisionError, MemoryError) as exc:
            raise NumericalError(
                "ordered conditional p-value evaluation failed",
                method=ordering,
            ) from exc

    try:
        center_ok = accepted(center)
    except NumericalError:
        raise
    except (OverflowError, ValueError, ZeroDivisionError, MemoryError) as exc:
        raise NumericalError(
            "ordered conditional p-value evaluation failed at the MLE",
            method=ordering,
        ) from exc
    if not center_ok:
        raise NumericalError(
            "ordered conditional p-value is below alpha at its likelihood maximum",
            method=ordering,
        )

    def transition(direction: int) -> float:
        inside = center
        step = 1.0
        outside = center + direction * step
        while -_LOG_LIMIT < outside < _LOG_LIMIT and accepted(outside):
            inside = outside
            step *= 2.0
            outside = center + direction * step
        outside = min(_LOG_LIMIT, max(-_LOG_LIMIT, outside))
        if accepted(outside):
            return -math.inf if direction < 0 else math.inf

        if direction < 0:
            left, right = outside, inside
            for _ in range(220):
                middle = (left + right) / 2.0
                if accepted(middle):
                    right = middle
                else:
                    left = middle
                if right - left <= _ROOT_TOL * max(1.0, abs(middle)):
                    break
            if not accepted(right) or accepted(left):
                raise NumericalError(
                    "lower ordered-exact transition failed certification",
                    method=ordering,
                    side="lower",
                )
            return right

        left, right = inside, outside
        for _ in range(220):
            middle = (left + right) / 2.0
            if accepted(middle):
                left = middle
            else:
                right = middle
            if right - left <= _ROOT_TOL * max(1.0, abs(middle)):
                break
        if not accepted(left) or accepted(right):
            raise NumericalError(
                "upper ordered-exact transition failed certification",
                method=ordering,
                side="upper",
            )
        return left

    lower_log = -math.inf if a == support_lower else transition(-1)
    upper_log = math.inf if a == support_upper else transition(1)
    lower, upper = exp_parameter(lower_log), exp_parameter(upper_log)
    if lower < 0.0 or lower > upper:
        raise NumericalError(
            "ordered conditional inversion returned invalid bounds",
            method=ordering,
        )
    return lower, upper


__all__ = [
    "conditional_mean",
    "conditional_mle",
    "exp_parameter",
    "fnch_probabilities",
    "normal_quantile",
    "ordered_interval",
    "ordered_p_value",
    "solve_monotone_log_parameter",
    "support_bounds",
]
