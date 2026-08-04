"""Independent high-precision oracles.

These are deliberately written from the mathematical definitions rather than by
reusing any production helper, so that agreement is evidence rather than
tautology. ``mpmath`` is an optional ``validation`` extra; every consumer skips
when it is absent.
"""

from __future__ import annotations

import math

try:  # pragma: no cover - exercised by the skip path in CI matrices without the extra
    import mpmath as mp

    HAVE_MPMATH = True
except ImportError:  # pragma: no cover
    mp = None
    HAVE_MPMATH = False

DPS = 60


def _bounds(n1: int, n0: int, events: int) -> tuple[int, int]:
    return max(0, events - n0), min(events, n1)


def fnch_probabilities(n1: int, n0: int, events: int, log_odds: float):
    """Fisher noncentral hypergeometric probabilities at ``DPS`` digits."""
    if not HAVE_MPMATH:  # pragma: no cover
        raise RuntimeError("mpmath is required for the high-precision oracle")
    with mp.workdps(DPS):
        lower, upper = _bounds(n1, n0, events)
        points = list(range(lower, upper + 1))
        weights = [
            mp.binomial(n1, k)
            * mp.binomial(n0, events - k)
            * mp.e ** (mp.mpf(k) * mp.mpf(log_odds))
            for k in points
        ]
        total = mp.fsum(weights)
        return points, [w / total for w in weights]


def moments(n1: int, n0: int, events: int, log_odds: float):
    """Exact conditional mean and variance at ``DPS`` digits."""
    points, probabilities = fnch_probabilities(n1, n0, events, log_odds)
    with mp.workdps(DPS):
        mean = mp.fsum(mp.mpf(k) * p for k, p in zip(points, probabilities))
        var = mp.fsum(
            (mp.mpf(k) - mean) ** 2 * p for k, p in zip(points, probabilities)
        )
    return mean, var


def _bisect(fn, lo, hi, iterations: int = 400):
    with mp.workdps(DPS):
        flo = fn(lo)
        fhi = fn(hi)
        if flo * fhi > 0:
            return None
        for _ in range(iterations):
            mid = (lo + hi) / 2
            if flo * fn(mid) <= 0:
                hi = mid
            else:
                lo = mid
        return (lo + hi) / 2


def conditional_interval(a: int, b: int, c: int, d: int, alpha: float = 0.05):
    """Equal-tail conditional interval, inverted independently at ``DPS`` digits."""
    if not HAVE_MPMATH:  # pragma: no cover
        raise RuntimeError("mpmath is required for the high-precision oracle")
    n1, n0, events = a + b, c + d, a + c
    lower_k, upper_k = _bounds(n1, n0, events)
    with mp.workdps(DPS):
        points = list(range(lower_k, upper_k + 1))
        coeffs = [mp.binomial(n1, k) * mp.binomial(n0, events - k) for k in points]
        half = mp.mpf(alpha) / 2

        def tail(t, upper_side: bool):
            weights = [ci * mp.e ** (mp.mpf(k) * t) for ci, k in zip(coeffs, points)]
            total = mp.fsum(weights)
            keep = [
                w for k, w in zip(points, weights) if (k <= a if upper_side else k >= a)
            ]
            return mp.fsum(keep) / total

        lower = (
            mp.mpf(0)
            if a == lower_k
            else mp.e
            ** _bisect(lambda t: tail(t, False) - half, mp.mpf(-900), mp.mpf(900))
        )
        upper = (
            mp.inf
            if a == upper_k
            else mp.e
            ** _bisect(lambda t: tail(t, True) - half, mp.mpf(-900), mp.mpf(900))
        )
    return lower, upper


def relative_error(observed: float, reference) -> float:
    """Relative deviation, treating matching infinities and zeros as exact."""
    if not HAVE_MPMATH:  # pragma: no cover
        raise RuntimeError("mpmath is required for the high-precision oracle")
    with mp.workdps(DPS):
        ref = mp.mpf(reference) if not mp.isinf(mp.mpf(reference)) else mp.inf
        if mp.isinf(ref) and math.isinf(observed):
            return 0.0
        if ref == 0 and observed == 0:
            return 0.0
        if mp.isinf(ref) != math.isinf(observed):
            return float("inf")
        return float(abs(mp.mpf(observed) - ref) / max(abs(ref), mp.mpf("1e-300")))
