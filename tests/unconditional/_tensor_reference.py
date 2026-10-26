"""Independent exact tensor Bernstein lane; test/reference infrastructure only.

The product-binomial numerator is built directly in compact effect and nuisance
coordinates. It reuses none of the projected-event polynomial machinery.
"""

from __future__ import annotations

from fractions import Fraction as F
from math import comb

Power = dict[tuple[int, int], F]
Tensor = tuple[tuple[F, ...], ...]


def _add(a: Power, b: Power) -> Power:
    out = dict(a)
    for key, value in b.items():
        out[key] = out.get(key, F(0)) + value
    return {key: value for key, value in out.items() if value}


def _scale(a: Power, value: F) -> Power:
    return {
        key: coefficient * value
        for key, coefficient in a.items()
        if coefficient * value
    }


def _multiply(a: Power, b: Power) -> Power:
    out: Power = {}
    for (i, j), x in sorted(a.items()):
        for (k, m), y in sorted(b.items()):
            key = i + k, j + m
            out[key] = out.get(key, F(0)) + x * y
    return {key: value for key, value in out.items() if value}


def _power(a: Power, n: int) -> Power:
    out = {(0, 0): F(1)}
    for _ in range(n):
        out = _multiply(out, a)
    return out


def objective(n1: int, n0: int, mask: tuple[tuple[int, int], ...], level: F) -> Power:
    if min(n1, n0) <= 0 or n1 + n0 > 16:
        raise ValueError(
            "tensor reference supports positive groups with total at most 16"
        )
    if len(set(mask)) != len(mask) or any(
        not (0 <= x <= n1 and 0 <= y <= n0) for x, y in mask
    ):
        raise ValueError("invalid outcome mask")
    out: Power = {}
    # (1-s)^a and (1-q)^b are expanded independently from binomial identities.
    for x, y in sorted(mask):
        weight = comb(n1, x) * comb(n0, y)
        for i in range(n1 - x + 1):
            for j in range(n1 + n0 - x - y + 1):
                key = x + i, x + y + j
                value = F(
                    weight
                    * comb(n1 - x, i)
                    * comb(n1 + n0 - x - y, j)
                    * (-1) ** (i + j)
                )
                out[key] = out.get(key, F(0)) + value
    denominator = _power({(0, 0): F(1), (1, 0): F(-1), (0, 1): F(-1), (1, 1): F(2)}, n1)
    return _add(out, _scale(denominator, -level))


def controls(power: Power, degree: tuple[int, int], box: tuple[F, F, F, F]) -> Tensor:
    ns, nq = degree
    a, b, c, d = box
    if not (a < b and c < d) or any(i > ns or j > nq for i, j in power):
        raise ValueError("invalid box or declared degree")
    local: Power = {}
    for (i, j), value in sorted(power.items()):
        for k in range(i + 1):
            for m in range(j + 1):
                key = k, m
                term = value * comb(i, k) * a ** (i - k) * (b - a) ** k
                term *= comb(j, m) * c ** (j - m) * (d - c) ** m
                local[key] = local.get(key, F(0)) + term
    return tuple(
        tuple(
            sum(
                (
                    value * F(comb(k, i), comb(ns, i)) * F(comb(m, j), comb(nq, j))
                    for (i, j), value in local.items()
                    if i <= k and j <= m
                ),
                F(0),
            )
            for m in range(nq + 1)
        )
        for k in range(ns + 1)
    )


def _casteljau(values: tuple[F, ...], t: F) -> F:
    if not values or not 0 <= t <= 1:
        raise ValueError("invalid Bernstein evaluation")
    row = values
    while len(row) > 1:
        row = tuple((1 - t) * x + t * y for x, y in zip(row, row[1:]))
    return row[0]


def evaluate(tensor: Tensor, u: F, v: F) -> F:
    return _casteljau(tuple(_casteljau(row, v) for row in tensor), u)


def hull(tensor: Tensor) -> tuple[F, F]:
    values = tuple(value for row in tensor for value in row)
    return min(values), max(values)


def constant_witness(tensor: Tensor, nuisance: F) -> bool:
    """Sufficient whole-effect-cell certificate, allowing inclusive equality."""
    return all(_casteljau(row, nuisance) >= 0 for row in tensor)


def slice_effect(tensor: Tensor, s: F) -> tuple[F, ...]:
    return tuple(
        _casteljau(tuple(row[j] for row in tensor), s) for j in range(len(tensor[0]))
    )


def _halve(values: tuple[F, ...]) -> tuple[tuple[F, ...], tuple[F, ...]]:
    row = values
    left, right = [row[0]], [row[-1]]
    while len(row) > 1:
        row = tuple((x + y) / 2 for x, y in zip(row, row[1:]))
        left.append(row[0])
        right.append(row[-1])
    return tuple(left), tuple(reversed(right))


def decide_nuisance(values: tuple[F, ...], depth: int = 4) -> tuple[bool | None, int]:
    """Sound finite witness/strict-rejection lane; None is a named inconclusion.

    A surviving equality ridge or a root requiring deeper subdivision does not
    become rejection. No root solver is shared with the projected-event lane.
    """
    if not values or not 0 <= depth <= 12:
        raise ValueError("invalid bounded Bernstein search")
    queue = [(values, 0)]
    visits = 0
    unresolved = False
    while queue:
        row, level = queue.pop()
        visits += 1
        if row[0] >= 0 or row[-1] >= 0:
            return True, visits
        if max(row) < 0:
            continue
        if level == depth:
            unresolved = True
            continue
        left, right = _halve(row)
        queue.extend(((right, level + 1), (left, level + 1)))
    return (None if unresolved else False), visits
