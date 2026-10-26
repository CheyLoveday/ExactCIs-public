"""Independent normalized Fisher sums and per-margin cutoff/witness lane."""

from __future__ import annotations

from fractions import Fraction as F
from math import comb

Point = tuple[int, int]


def _fisher(n1: int, n0: int, point: Point, psi: F, greater: bool) -> F:
    x, y = point
    margin = x + y
    weights = tuple(
        (k, F(comb(n1, k) * comb(n0, margin - k)) * psi**k)
        for k in range(max(0, margin - n0), min(n1, margin) + 1)
    )
    numerator = (
        sum((w for k, w in weights if k >= x), F(0))
        if greater
        else sum((w for k, w in weights if k <= x), F(0))
    )
    return numerator / sum((w for _, w in weights), F(0))


def mask(
    n1: int, n0: int, observed: Point, psi: F, direction: str
) -> tuple[Point, ...]:
    if min(n1, n0) <= 0 or psi <= 0 or direction not in ("greater", "less"):
        raise ValueError("invalid reference input")
    greater = direction == "greater"
    target = _fisher(n1, n0, observed, psi, greater)
    cutoffs = []
    for margin in range(n1 + n0 + 1):
        lo, hi = max(0, margin - n0), min(n1, margin)
        included = [
            k
            for k in range(lo, hi + 1)
            if _fisher(n1, n0, (k, margin - k), psi, greater) <= target
        ]
        cutoffs.append(
            min(included, default=hi + 1) if greater else max(included, default=lo - 1)
        )
    return tuple(
        (x, y)
        for x in range(n1 + 1)
        for y in range(n0 + 1)
        if (x >= cutoffs[x + y] if greater else x <= cutoffs[x + y])
    )


def probability(n1: int, n0: int, selected: tuple[Point, ...], psi: F, q: F) -> F:
    if psi <= 0 or not 0 <= q <= 1:
        raise ValueError("invalid effect or nuisance")
    p1 = psi * q / (1 - q + psi * q)
    return sum(
        (
            F(comb(n1, x) * comb(n0, y))
            * p1**x
            * (1 - p1) ** (n1 - x)
            * q**y
            * (1 - q) ** (n0 - y)
            for x, y in selected
        ),
        F(0),
    )


def decide(
    n1: int, n0: int, observed: Point, psi: F, direction: str, level: F
) -> bool | None:
    """Finite nuisance witnesses, then the exact conditional Fisher envelope."""
    selected = mask(n1, n0, observed, psi, direction)
    for q in (F(0), F(1, 4), F(1, 2), F(3, 4), F(1)):
        if probability(n1, n0, selected, psi, q) >= level:
            return True
    if _fisher(n1, n0, observed, psi, direction == "greater") < level:
        return False
    return None
