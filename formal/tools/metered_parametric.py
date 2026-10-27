"""Native metered Q(s)[q] root-data construction for the frozen v1 grammar.

Elements use exact numerator/denominator polynomial pairs, reduced by the
native metered rational-polynomial gcd.  There is no CAS call or irreducible
factorization oracle.
The q-Euclidean algorithm strictly lowers the q-degree; every generated
identity is independently replayed with integral bivariate list arithmetic.
This component constructs a cell-independent skeleton.  Whole-cell sign
guards and exceptional selected-embedding packets are separate work.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Protocol

import metered_polynomial as p
import metered_root as r

B = tuple[p.P, ...]


class Embedding(Protocol):
    def normalize(
        self, numerator: p.P, denominator: p.P, m: r.Meter
    ) -> tuple[p.P, p.P]: ...


@dataclass(frozen=True)
class Element:
    numerator: p.P
    denominator: p.P
    embedding: Embedding | None = None


ZERO = Element((), p.ONE)
ONE = Element(p.ONE, p.ONE)
F = tuple[Element, ...]


def _element(
    numerator: p.P, denominator: p.P, m: r.Meter, embedding: Embedding | None = None
) -> Element:
    numerator = m.poly(numerator)
    denominator = m.poly(denominator)
    if not denominator:
        raise r.InvalidWitness("zero Q(s) denominator")
    if embedding is not None:
        numerator, denominator = embedding.normalize(numerator, denominator, m)
        m.structural()
        return Element(numerator, denominator, embedding)
    if not numerator:
        m.structural()
        return ZERO
    common, _, _ = p.xgcd(numerator, denominator, m)
    numerator = p.exact_divide(numerator, common, m)
    denominator = p.exact_divide(denominator, common, m)
    leading_inverse = m.div(Q(1), denominator[-1])
    numerator = p.scale(leading_inverse, numerator, m)
    denominator = p.scale(leading_inverse, denominator, m)
    m.structural()
    return Element(numerator, denominator)


def _embedding(a: Element, b: Element) -> Embedding | None:
    if (
        a.embedding is not None
        and b.embedding is not None
        and a.embedding is not b.embedding
    ):
        raise r.InvalidWitness("field operation mixed two selected embeddings")
    return a.embedding if a.embedding is not None else b.embedding


def _add(a: Element, b: Element, m: r.Meter) -> Element:
    m.structural()
    return _element(
        p.add(
            p.mul(a.numerator, b.denominator, m),
            p.mul(b.numerator, a.denominator, m),
            m,
        ),
        p.mul(a.denominator, b.denominator, m),
        m,
        _embedding(a, b),
    )


def _neg(a: Element, m: r.Meter) -> Element:
    m.structural()
    return _element(p.scale(Q(-1), a.numerator, m), a.denominator, m, a.embedding)


def _mul(a: Element, b: Element, m: r.Meter) -> Element:
    m.structural()
    return _element(
        p.mul(a.numerator, b.numerator, m),
        p.mul(a.denominator, b.denominator, m),
        m,
        _embedding(a, b),
    )


def _inverse(a: Element, m: r.Meter) -> Element:
    m.structural()
    if not a.numerator:
        raise r.InvalidWitness("inverse of zero Q(s) element")
    return _element(a.denominator, a.numerator, m, a.embedding)


def _trim(values: F, m: r.Meter) -> F:
    m.structural()
    stop = len(values)
    while stop:
        m.structural()
        if values[stop - 1].numerator:
            break
        stop -= 1
    m.size(stop, operation="Q(s)[q] output degree")
    m.structural(stop)
    return values[:stop]


def _fadd(a: F, b: F, m: r.Meter) -> F:
    count = max(len(a), len(b))
    m.size(count, operation="Q(s)[q] sum degree")
    m.structural(count)
    return _trim(
        tuple(
            _add(a[i] if i < len(a) else ZERO, b[i] if i < len(b) else ZERO, m)
            for i in range(count)
        ),
        m,
    )


def _fneg(a: F, m: r.Meter) -> F:
    m.structural(len(a))
    return tuple(_neg(x, m) for x in a)


def _fmul(a: F, b: F, m: r.Meter) -> F:
    m.structural()
    if not a or not b:
        return ()
    count = len(a) + len(b) - 1
    m.size(count, operation="Q(s)[q] product degree")
    m.structural(count)
    values = [ZERO for _ in range(count)]
    for i, x in enumerate(a):
        m.structural()
        for j, y in enumerate(b):
            m.structural()
            values[i + j] = _add(values[i + j], _mul(x, y, m), m)
    m.structural(count)
    return _trim(tuple(values), m)


def _derivative(a: F, m: r.Meter) -> F:
    m.structural(len(a))
    values = []
    for i in range(1, len(a)):
        m.structural()
        values.append(_mul(_element((m.integer(i),), p.ONE, m), a[i], m))
    m.structural(len(values))
    return _trim(tuple(values), m)


def _divide(a: F, b: F, m: r.Meter) -> tuple[F, F]:
    a, b = _trim(a, m), _trim(b, m)
    if not b:
        raise r.InvalidWitness("division by zero Q(s)[q] polynomial")
    count = max(0, len(a) - len(b) + 1)
    m.size(count, operation="Q(s)[q] quotient degree")
    m.structural(count)
    quotient = [ZERO for _ in range(count)]
    leading_inverse = _inverse(b[-1], m)
    while a and len(a) >= len(b):
        m.structural()
        previous_degree = len(a)
        shift = len(a) - len(b)
        factor = _mul(a[-1], leading_inverse, m)
        quotient[shift] = _add(quotient[shift], factor, m)
        m.structural(len(a))
        remainder = list(a)
        for i, c in enumerate(b):
            m.structural()
            remainder[shift + i] = _add(
                remainder[shift + i], _neg(_mul(factor, c, m), m), m
            )
        m.structural(len(remainder))
        a = _trim(tuple(remainder), m)
        if len(a) >= previous_degree:
            raise r.InvalidWitness("Q(s)[q] division failed strict degree descent")
    m.structural(len(quotient))
    return _trim(tuple(quotient), m), a


def _exact_divide(a: F, b: F, m: r.Meter) -> F:
    quotient, remainder = _divide(a, b, m)
    if remainder:
        raise r.InvalidWitness("Q(s)[q] exact division left a remainder")
    return quotient


def _xgcd(a: F, b: F, m: r.Meter) -> tuple[F, F, F]:
    old_r, next_r = a, b
    old_s: F = (ONE,)
    next_s: F = ()
    old_t: F = ()
    next_t: F = (ONE,)
    while next_r:
        m.structural()
        quotient, remainder = _divide(old_r, next_r, m)
        old_r, next_r = next_r, remainder
        old_s, next_s = next_s, _fadd(old_s, _fneg(_fmul(quotient, next_s, m), m), m)
        old_t, next_t = next_t, _fadd(old_t, _fneg(_fmul(quotient, next_t, m), m), m)
    if not old_r:
        return (), (), ()
    inverse = _inverse(old_r[-1], m)
    scale = (inverse,)
    return _fmul(old_r, scale, m), _fmul(old_s, scale, m), _fmul(old_t, scale, m)


def _bequal(a: B, b: B, m: r.Meter) -> bool:
    m.structural(max(len(a), len(b)))
    return all(
        p.equal(a[i] if i < len(a) else (), b[i] if i < len(b) else (), m)
        for i in range(max(len(a), len(b)))
    )


def _bscale(c: p.P, a: B, m: r.Meter) -> B:
    m.structural(len(a))
    return tuple(p.mul(c, x, m) for x in a)


def _badd(a: B, b: B, m: r.Meter) -> B:
    count = max(len(a), len(b))
    m.size(count, operation="integral bivariate sum degree")
    m.structural(count)
    return tuple(
        p.add(a[i] if i < len(a) else (), b[i] if i < len(b) else (), m)
        for i in range(count)
    )


def _bmul(a: B, b: B, m: r.Meter) -> B:
    m.structural()
    if not a:
        return ()
    count = len(a) + len(b) - 1
    m.size(count, operation="integral bivariate product degree")
    m.structural(count)
    values: list[p.P] = [() for _ in range(count)]
    for i, x in enumerate(a):
        m.structural()
        for j, y in enumerate(b):
            m.structural()
            values[i + j] = p.add(values[i + j], p.mul(x, y, m), m)
    m.structural(count)
    return tuple(values)


def _bpower(a: B, exponent: int, m: r.Meter) -> B:
    result: B = (p.ONE,)
    for _ in range(exponent):
        m.structural()
        result = _bmul(a, result, m)
    return result


def _bderivative(a: B, m: r.Meter) -> B:
    m.structural(len(a))
    if not a:
        return ()
    # The frozen recursive derivative keeps one final zero row, including
    # for a constant. Modular identity witnesses must cover that raw width.
    return tuple(p.scale(m.integer(i), a[i], m) for i in range(1, len(a))) + ((),)


def at_rational(a: B, q: Q, m: r.Meter) -> p.P:
    result: p.P = ()
    for coefficient in reversed(a):
        m.structural()
        result = p.add(coefficient, p.scale(q, result, m), m)
    return result


@dataclass(frozen=True)
class Step:
    scale: p.P
    quotient: B


@dataclass(frozen=True)
class Skeleton:
    representative: B
    quotient: B
    power_quotient: B
    exponent: int
    root_scale: p.P
    power_scale: p.P
    bezout_left: B
    bezout_right: B
    bezout_scale: p.P
    tail: tuple[B, ...]
    steps: tuple[Step, ...]
    last: p.P


def guards(original: B, c: Skeleton, m: r.Meter) -> tuple[p.P, ...]:
    """Exact frozen-v1 decision/root guard order, before signed trim/dedup."""
    values = [at_rational(original, Q(0), m), at_rational(original, Q(1), m)]
    m.structural(2)
    for poly in (
        original,
        (c.root_scale, c.power_scale, c.bezout_scale, c.last),
        c.representative,
        c.quotient,
        c.power_quotient,
        c.bezout_left,
        c.bezout_right,
        *c.tail,
    ):
        m.structural(len(poly))
        values.extend(poly)
    for step in c.steps:
        m.structural(len(step.quotient) + 1)
        values.append(step.scale)
        values.extend(step.quotient)
    for poly in (c.representative, *c.tail):
        m.structural(2)
        values.extend((at_rational(poly, Q(0), m), at_rational(poly, Q(1), m)))
    m.structural(len(values))
    return tuple(values)


def signed_family(values: tuple[p.P, ...], m: r.Meter) -> tuple[p.P, ...]:
    """Deduplicate exact signed polynomials only; opposite signs remain distinct."""
    found: list[p.P] = []
    for poly in values:
        m.structural()
        poly = m.poly(poly)
        if not poly:
            continue
        if not any(p.equal(poly, previous, m) for previous in found):
            m.structural()
            found.append(poly)
    m.structural(len(found))
    return tuple(found)


def replay(original: B, c: Skeleton, m: r.Meter) -> None:
    """Check every generated identity, retaining the original signed H."""
    m.structural()
    if c.exponent <= 0 or not c.root_scale or not c.power_scale or not c.bezout_scale:
        raise r.InvalidWitness("invalid root-set scale or exponent")
    if not _bequal(
        _bscale(c.root_scale, original, m), _bmul(c.representative, c.quotient, m), m
    ):
        raise r.InvalidWitness("parametric root identity failed")
    if not _bequal(
        _bscale(c.power_scale, _bpower(c.representative, c.exponent, m), m),
        _bmul(original, c.power_quotient, m),
        m,
    ):
        raise r.InvalidWitness("parametric power identity failed")
    if not _bequal(
        _badd(
            _bmul(c.bezout_left, c.representative, m),
            _bmul(c.bezout_right, _bderivative(c.representative, m), m),
            m,
        ),
        (c.bezout_scale,),
        m,
    ):
        raise r.InvalidWitness("parametric Bezout identity failed")
    if c.tail and not _bequal(c.tail[0], _bderivative(c.representative, m), m):
        raise r.InvalidWitness("parametric derivative-first identity failed")
    chain = (c.representative,) + c.tail
    if len(c.steps) != max(0, len(chain) - 2):
        raise r.InvalidWitness("parametric signed chain shape failed")
    for i, step in enumerate(c.steps):
        m.structural()
        if not _bequal(
            _bscale(step.scale, chain[i], m),
            _badd(
                _bmul(chain[i + 1], step.quotient, m),
                _bscale((Q(-1),), chain[i + 2], m),
                m,
            ),
            m,
        ):
            raise r.InvalidWitness("parametric signed chain identity failed")
    if not c.last or not _bequal(chain[-1], (c.last,), m):
        raise r.InvalidWitness("parametric terminal identity failed")


@dataclass(frozen=True)
class RootData:
    representative: F
    quotient: F
    power_quotient: F
    exponent: int
    bezout_left: F
    bezout_right: F
    chain: tuple[F, ...]
    quotients: tuple[F, ...]


def _root_data(h: F, m: r.Meter) -> RootData:
    if not h:
        raise r.InvalidWitness("zero objective has no generic root skeleton")
    dh = _derivative(h, m)
    divisor, _, _ = _xgcd(h, dh, m)
    representative = _exact_divide(h, divisor, m)
    representative = _fmul(representative, (_inverse(representative[-1], m),), m)
    quotient = _exact_divide(h, representative, m)
    power: F = (ONE,)
    power_quotient: F | None = None
    for exponent in range(1, len(h)):
        m.structural()
        power = _fmul(power, representative, m)
        candidate, remainder = _divide(power, h, m)
        if not remainder:
            power_quotient = candidate
            break
    if power_quotient is None:
        if len(h) == 1:
            exponent = 1
            power_quotient = _exact_divide(representative, h, m)
        else:
            raise r.InvalidWitness("parametric root multiplicity bound failed")
    derivative = _derivative(representative, m)
    gcd, bezout_left, bezout_right = _xgcd(representative, derivative, m)
    if len(gcd) != 1:
        raise r.InvalidWitness("parametric squarefree Bezout construction failed")
    chain: list[F] = [representative]
    quotients: list[F] = []
    if derivative:
        chain.append(derivative)
    while len(chain[-1]) > 1:
        m.structural()
        q, remainder = _divide(chain[-2], chain[-1], m)
        if not remainder:
            raise r.InvalidWitness("parametric squarefree chain ended before constant")
        quotients.append(q)
        chain.append(_fneg(remainder, m))
    m.structural(8 + len(chain) + len(quotients))
    return RootData(
        representative,
        quotient,
        power_quotient,
        exponent,
        bezout_left,
        bezout_right,
        tuple(chain),
        tuple(quotients),
    )


def generate(original: B, m: r.Meter) -> Skeleton:
    """Construct one deterministic generic skeleton, then replay its identities.

    All loops are ordered by coefficient index, exponent or Euclidean degree.
    A resource refusal propagates with the original shared meter.  The zero
    polynomial belongs to a separate decision branch and has no root skeleton.
    """
    m.structural(len(original))
    original = tuple(m.poly(x) for x in original)
    h = _trim(tuple(_element(x, p.ONE, m) for x in original), m)
    data = _root_data(h, m)
    representative, quotient, power_quotient, exponent = (
        data.representative,
        data.quotient,
        data.power_quotient,
        data.exponent,
    )
    bezout_left, bezout_right, chain, quotients = (
        data.bezout_left,
        data.bezout_right,
        data.chain,
        data.quotients,
    )
    all_polys = [
        representative,
        quotient,
        power_quotient,
        bezout_left,
        bezout_right,
        *chain,
        *quotients,
    ]
    denominator = p.ONE
    for poly in all_polys:
        m.structural()
        for coefficient in poly:
            m.structural()
            common, _, _ = p.xgcd(denominator, coefficient.denominator, m)
            denominator = p.mul(
                denominator, p.exact_divide(coefficient.denominator, common, m), m
            )

    def lift(poly: F) -> B:
        m.structural(len(poly))
        return tuple(
            p.mul(c.numerator, p.exact_divide(denominator, c.denominator, m), m)
            for c in poly
        )

    cleared_chain = tuple(lift(poly) for poly in chain)
    cleared_quotients = tuple(lift(poly) for poly in quotients)
    d2 = p.power(denominator, 2, m)
    d4 = p.power(denominator, 4, m)
    adapted: list[B] = [cleared_chain[0]]
    weight = p.ONE
    for cleared_poly in cleared_chain[1:]:
        m.structural()
        adapted.append(_bscale(weight, cleared_poly, m))
        weight = p.mul(weight, d2, m)
    steps = tuple(
        Step(d2 if i == 0 else d4, _bscale(denominator, poly, m))
        for i, poly in enumerate(cleared_quotients)
    )
    m.structural(len(steps))
    terminal = adapted[-1]
    if len(terminal) != 1:
        raise r.InvalidWitness("parametric terminal was not constant in nuisance")
    c = Skeleton(
        lift(representative),
        lift(quotient),
        _bscale(p.power(denominator, exponent, m), lift(power_quotient), m),
        exponent,
        d2,
        denominator,
        lift(bezout_left),
        lift(bezout_right),
        d2,
        tuple(adapted[1:]),
        steps,
        terminal[0],
    )
    replay(original, c, m)
    return c
