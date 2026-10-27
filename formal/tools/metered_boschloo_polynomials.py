"""Exact frozen-v1 Boschloo comparison/objective reconstruction for generation.

Raw list lengths are retained while selecting the compactification degree.
Only the final signed polynomials are trimmed. This matters because v1 uses
the executable list length, rather than a guessed generic algebraic degree.
"""

from __future__ import annotations

from fractions import Fraction as Q
from math import comb
from typing import Literal

import metered_parametric as f
import metered_polynomial as p
import metered_root as r
import resource_model as v

Direction = Literal["greater", "less"]
Outcome = tuple[int, int]


def _pad(poly: p.P, count: int, m: r.Meter) -> p.P:
    m.size(count, operation="frozen raw coefficient length")
    if len(poly) > count:
        raise r.InvalidWitness("raw list bound contradicted polynomial degree")
    m.reserve(count, operation="frozen raw coefficient tuple")
    return poly + (Q(0),) * (count - len(poly))


def add(a: p.P, b: p.P, m: r.Meter) -> p.P:
    return _pad(p.add(a, b, m), max(len(a), len(b)), m)


def scale(c: Q, a: p.P, m: r.Meter) -> p.P:
    return _pad(p.scale(c, a, m), len(a), m)


def mul(a: p.P, b: p.P, m: r.Meter) -> p.P:
    count = max(0, len(a) + len(b) - 1) if a else 0
    return _pad(p.mul(a, b, m), count, m)


def power(a: p.P, n: int, m: r.Meter) -> p.P:
    m.resources.shape("exponent", n, phase="frozen_reconstruction")
    result = p.ONE
    for _ in range(n):
        m.structural()
        result = mul(a, result, m)
    return result


def badd(a: f.B, b: f.B, m: r.Meter) -> f.B:
    count = max(len(a), len(b))
    m.size(count, operation="frozen bivariate sum")
    m.structural(count)
    return tuple(
        add(a[i] if i < len(a) else (), b[i] if i < len(b) else (), m)
        for i in range(count)
    )


def bscale(c: p.P, a: f.B, m: r.Meter) -> f.B:
    m.structural(len(a))
    return tuple(mul(c, row, m) for row in a)


def bmul(a: f.B, b: f.B, m: r.Meter) -> f.B:
    m.structural()
    if not a:
        return ()
    head = bscale(a[0], b, m)
    rest = bmul(a[1:], b, m)
    m.structural()
    return badd(head, ((), *rest), m)


def bpower(a: f.B, n: int, m: r.Meter) -> f.B:
    m.resources.shape("exponent", n, phase="frozen_reconstruction")
    result: f.B = (p.ONE,)
    for _ in range(n):
        m.structural()
        result = bmul(a, result, m)
    return result


def transform(poly: p.P, degree: int, m: r.Meter) -> p.P:
    if len(poly) > degree + 1:
        raise r.InvalidWitness(
            "compactification degree did not cover every coefficient"
        )
    result: p.P = ()
    for i, coefficient in enumerate(poly):
        m.structural()
        monomial = p.mul(
            p.power((Q(0), Q(1)), i, m), p.power((Q(1), Q(-1)), degree - i, m), m
        )
        result = p.add(result, p.scale(coefficient, monomial, m), m)
    return result


class Model:
    def __init__(self, table: tuple[int, int, int, int], alpha_side: Q, m: r.Meter):
        if (
            type(table) is not tuple
            or len(table) != 4
            or any(type(x) is not int or x < 0 for x in table)
        ):
            raise r.InvalidWitness("a four-count exact table is required")
        if (
            type(alpha_side) is not Q
            or m.compare(alpha_side, Q(0)) < 0
            or m.compare(alpha_side, Q(1, 2)) > 0
        ):
            raise r.InvalidWitness("alpha_side must be an exact rational in [0,1/2]")
        a, b, c, d = table
        self.n1, self.n0 = a + b, c + d
        if not self.n1 or not self.n0:
            raise r.InvalidWitness("both group totals must be positive")
        m.resources.shape(
            "group_total", max(self.n1, self.n0), phase="frozen_reconstruction"
        )
        states = (self.n1 + 1) * (self.n0 + 1)
        m.resources.shape("sample_grid", states, phase="frozen_reconstruction")
        if self.n1 + self.n0 + 1 > m.limits.max_bits:
            m.refuse(
                "bits",
                operation="binomial coefficient preflight",
                requested=self.n1 + self.n0 + 1,
            )
        self.observed = (a, c)
        self.table = table
        self.level, self.meter = alpha_side, m
        m.structural(states)
        self.outcomes = tuple(
            (x, y) for x in range(self.n1 + 1) for y in range(self.n0 + 1)
        )
        self._events: dict[tuple[int, int, Direction | None], p.P] = {}
        self._outcomes: dict[Outcome, f.B] = {}
        self._objective: dict[tuple[bool, ...], f.B] = {}

    def _choose(self, n: int, k: int) -> Q:
        self.meter.integer_step(n + 1)
        return self.meter.integer(comb(n, k))

    def event(self, margin: int, success: int, direction: Direction | None) -> p.P:
        m = self.meter
        key = (margin, success, direction)
        m.structural()
        if key in self._events:
            return self._events[key]
        result: p.P = ()
        for k in range(max(0, margin - self.n0), min(self.n1, margin) + 1):
            m.resources.charge(
                v.Event.SAMPLE_STATE,
                v.CostVector(sample_states=1),
                phase="fisher_polynomials",
            )
            if (
                direction == "greater"
                and k < success
                or direction == "less"
                and k > success
            ):
                continue
            weight = m.mul(self._choose(self.n1, k), self._choose(self.n0, margin - k))
            result = add(result, scale(weight, power((Q(0), Q(1)), k, m), m), m)
        m.structural()
        self._events[key] = result
        return result

    def comparison(self, candidate: Outcome, direction: Direction) -> p.P:
        m = self.meter
        margin, observed = sum(candidate), sum(self.observed)
        raw = add(
            mul(
                self.event(margin, candidate[0], direction),
                self.event(observed, self.observed[0], None),
                m,
            ),
            scale(
                Q(-1),
                mul(
                    self.event(observed, self.observed[0], direction),
                    self.event(margin, candidate[0], None),
                    m,
                ),
                m,
            ),
            m,
        )
        return transform(raw, len(raw), m)

    def comparisons(self, direction: Direction) -> tuple[p.P, ...]:
        self.meter.structural(len(self.outcomes))
        return tuple(
            self.comparison(candidate, direction) for candidate in self.outcomes
        )

    def outcome(self, value: Outcome) -> f.B:
        m = self.meter
        m.structural()
        if value in self._outcomes:
            return self._outcomes[value]
        x, y = value
        weight = m.mul(self._choose(self.n1, x), self._choose(self.n0, y))
        monomial = scale(weight, power((Q(0), Q(1)), x, m), m)
        polynomial = bscale(
            monomial,
            bmul(
                bpower(((), p.ONE), x + y, m),
                bpower((p.ONE, (Q(-1),)), self.n1 + self.n0 - x - y, m),
                m,
            ),
            m,
        )
        m.structural()
        self._outcomes[value] = polynomial
        return polynomial

    def objective(self, mask: tuple[bool, ...]) -> f.B:
        m = self.meter
        if len(mask) != len(self.outcomes) or any(
            type(value) is not bool for value in mask
        ):
            raise r.InvalidWitness("a complete row-major Boolean mask is required")
        m.structural(len(mask))
        if mask in self._objective:
            return self._objective[mask]
        selected: f.B = ()
        total: f.B = ()
        for included, value in zip(mask, self.outcomes):
            m.structural()
            polynomial = self.outcome(value)
            total = badd(total, polynomial, m)
            if included:
                selected = badd(selected, polynomial, m)
        raw = badd(selected, bscale((m.sub(Q(0), self.level),), total, m), m)
        degree = 0
        for row in raw:
            m.structural()
            degree = max(degree, len(row))
        m.structural(len(raw))
        result = tuple(transform(row, degree, m) for row in raw)
        self._objective[mask] = result
        return result
