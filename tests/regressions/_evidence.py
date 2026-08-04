"""Shared evidence helpers: operation counting and ordering-set introspection.

These helpers deliberately avoid touching production code paths. They observe
the existing implementation rather than replacing any part of it.
"""

from __future__ import annotations

import math
from contextlib import contextmanager
from dataclasses import dataclass, field

from exactcis import Design
from exactcis import _numerics as numerics

CASE_CONTROL = Design.CASE_CONTROL_FIXED_MARGIN
COHORT = Design.COHORT_BINOMIAL


@dataclass
class WorkCounter:
    """Deterministic combinatorial work units consumed by one measurement.

    ``comb_work`` counts ``min(k, n - k)`` per ``math.comb`` call, which is the
    number of multiply/divide steps CPython performs, and ``log_calls`` counts
    ``math.log`` invocations. Both are exactly reproducible across runs and
    machines, unlike wall-clock time, which is why the complexity gate is
    expressed in these units.
    """

    log_calls: int = 0
    comb_calls: int = 0
    comb_work: int = 0
    fnch_calls: int = 0
    prepared: int = 0
    detail: dict = field(default_factory=dict)

    def total_work(self) -> int:
        return self.comb_work + self.log_calls


class _CountingMath:
    """Proxy around the ``math`` module recording combinatorial work."""

    def __init__(self, real, counter: WorkCounter) -> None:
        object.__setattr__(self, "_real", real)
        object.__setattr__(self, "_counter", counter)

    def log(self, *args):
        self._counter.log_calls += 1
        return self._real.log(*args)

    def comb(self, n, k):
        self._counter.comb_calls += 1
        self._counter.comb_work += min(k, n - k)
        return self._real.comb(n, k)

    def lgamma(self, x):
        self._counter.log_calls += 1
        return self._real.lgamma(x)

    def __getattr__(self, name):
        return getattr(object.__getattribute__(self, "_real"), name)


@contextmanager
def count_work():
    """Count combinatorial work performed inside ``exactcis._numerics``.

    Also counts calls to ``fnch_probabilities`` and, when the module exposes a
    prepared-margins entry point, how many times preparation occurred. The
    latter is zero on 1.0.0 and becomes the one-preparation-per-inversion
    assertion once the replacement kernel lands.
    """
    counter = WorkCounter()
    real_math = numerics.math
    real_fnch = numerics.fnch_probabilities
    prepare_name = "prepare_margins"
    real_prepare = getattr(numerics, prepare_name, None)

    def counting_fnch(*args, **kwargs):
        counter.fnch_calls += 1
        return real_fnch(*args, **kwargs)

    def counting_prepare(*args, **kwargs):
        counter.prepared += 1
        return real_prepare(*args, **kwargs)

    numerics.math = _CountingMath(real_math, counter)
    numerics.fnch_probabilities = counting_fnch
    if real_prepare is not None:
        setattr(numerics, prepare_name, counting_prepare)
    try:
        yield counter
    finally:
        numerics.math = real_math
        numerics.fnch_probabilities = real_fnch
        if real_prepare is not None:
            setattr(numerics, prepare_name, real_prepare)


def support(n1: int, n0: int, events: int) -> list[int]:
    lower, upper = numerics.support_bounds(n1, n0, events)
    return list(range(lower, upper + 1))


def support_width(n1: int, n0: int, events: int) -> int:
    lower, upper = numerics.support_bounds(n1, n0, events)
    return upper - lower + 1


def log_coefficients(n1: int, n0: int, events: int) -> dict[int, float]:
    """Exact-integer log binomial coefficients, used only by tests."""
    out = {}
    for k in support(n1, n0, events):
        out[k] = math.log(math.comb(n1, k)) + math.log(math.comb(n0, events - k))
    return out


def membership_breakpoints(n1: int, n0: int, events: int, observed: int) -> list[float]:
    """Log-parameter values where minimum-likelihood membership can change.

    ``x`` enters or leaves ``{x : P(x) <= P(observed)}`` exactly when the two
    log masses coincide, which is a closed form independent of the parameter.
    """
    coeffs = log_coefficients(n1, n0, events)
    values = []
    for x in support(n1, n0, events):
        if x == observed:
            continue
        values.append((coeffs[observed] - coeffs[x]) / (x - observed))
    return sorted(t for t in values if math.isfinite(t))


def ordering_membership(
    n1: int, n0: int, events: int, observed: int, log_odds: float
) -> frozenset[int]:
    """The inclusion set used by the minimum-likelihood ordered p-value."""
    points, probabilities = numerics.fnch_probabilities(n1, n0, events, log_odds)
    index = points.index(observed)
    threshold = math.nextafter(probabilities[index] * (1.0 + 1e-10), math.inf)
    return frozenset(k for k, p in zip(points, probabilities) if p <= threshold)
