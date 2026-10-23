"""Small exact polynomial calculations over Q(s) and a real embedding Q(alpha).

The projection certificate records rational-function identities and every
guard needed to specialize its signed Sturm chain. Exceptional effects are
rebuilt over their selected real embedding, never classified by a neighbour.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import Any

from ._algebraic import Element, Root, Work
from ._polynomial import Exact

FieldPolynomial = tuple[Element, ...]


def trim(a: Sequence[Element]) -> FieldPolynomial:
    if not a:
        raise ValueError("field polynomial needs at least one coefficient")
    a = list(a)
    while len(a) > 1 and not a[-1]:
        a.pop()
    a[0].work.tick("field_polynomial")
    if len(a) - 1 > a[0].work.limits.max_degree:
        from ._polynomial import OracleLimitError

        raise OracleLimitError("field polynomial degree budget exceeded")
    return tuple(a)


def iszero(a: Sequence[Element]) -> bool:
    return len(a) == 1 and not a[0]


def add(a: Sequence[Element], b: Sequence[Element]) -> FieldPolynomial:
    z = a[0].coerce(0)
    return trim(
        tuple(
            (a[i] if i < len(a) else z) + (b[i] if i < len(b) else z)
            for i in range(max(len(a), len(b)))
        )
    )


def neg(a: Sequence[Element]) -> FieldPolynomial:
    return tuple(-v for v in a)


def mul(a: Sequence[Element], b: Sequence[Element]) -> FieldPolynomial:
    z = a[0].coerce(0)
    if iszero(a) or iszero(b):
        return (z,)
    c = [z for _ in range(len(a) + len(b) - 1)]
    if len(c) - 1 > z.work.limits.max_degree:
        from ._polynomial import OracleLimitError

        raise OracleLimitError("field polynomial degree budget exceeded")
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] = c[i + j] + x * y
    return trim(c)


def derivative(a: Sequence[Element]) -> FieldPolynomial:
    return trim(tuple(i * a[i] for i in range(1, len(a))) or (a[0].coerce(0),))


def divide(
    a: Sequence[Element], b: Sequence[Element]
) -> tuple[FieldPolynomial, FieldPolynomial]:
    a, b = trim(a), trim(b)
    if iszero(b):
        raise ValueError("division by zero field polynomial")
    z = a[0].coerce(0)
    result = [z for _ in range(max(1, len(a) - len(b) + 1))]
    while not iszero(a) and len(a) >= len(b):
        shift = len(a) - len(b)
        factor = a[-1] / b[-1]
        result[shift] = result[shift] + factor
        remainder = list(a)
        for i, c in enumerate(b):
            remainder[shift + i] = remainder[shift + i] - factor * c
        a = trim(remainder)
    return trim(result), a


def exact_divide(a: Sequence[Element], b: Sequence[Element]) -> FieldPolynomial:
    q, r = divide(a, b)
    if not iszero(r):
        raise ArithmeticError("field polynomial identity did not divide exactly")
    return q


def monic(a: Sequence[Element]) -> FieldPolynomial:
    a = trim(a)
    return a if iszero(a) else trim(tuple(v / a[-1] for v in a))


def squarefree(a: Sequence[Element]) -> FieldPolynomial:
    if iszero(a):
        raise ValueError("zero polynomial has no finite root set")
    left, right = a, derivative(a)
    while not iszero(right):
        left, right = right, divide(left, right)[1]
    return monic(exact_divide(a, monic(left)))


def sturm(a: Sequence[Element]) -> tuple[FieldPolynomial, ...]:
    a = squarefree(trim(a))
    if len(a) == 1:
        return (a,)
    chain = [a, derivative(a)]
    while True:
        remainder = divide(chain[-2], chain[-1])[1]
        if iszero(remainder):
            return tuple(chain)
        chain.append(neg(remainder))


def evaluate(a: Sequence[Element], x: Element | int) -> Element:
    result = a[0].coerce(0)
    for c in reversed(a):
        result = result * x + c
    return result


def encode_element(c: Element) -> dict[str, Any]:
    return {"numerator": c.numerator, "denominator": c.denominator}


def encode_poly(a: Sequence[Element]) -> tuple[dict[str, Any], ...]:
    return tuple(encode_element(c) for c in a)


def projection(a: Sequence[Element]) -> dict[str, Any]:
    """Return a checked root-set identity and specialization-guard packet."""
    a = trim(a)
    if a[0].root is not None:
        raise ValueError("projection requires Q(s), not a selected embedding")
    if iszero(a):
        return {"zero": True, "guards": (), "original": encode_poly(a)}
    s = squarefree(a)
    d = exact_divide(a, s)
    # Use a checked exponent, avoiding degree(H)^2 growth when H is already
    # squarefree. At worst its degree bounds every root multiplicity.
    spower = (a[0].coerce(1),)
    for exponent in range(len(a)):
        t, remainder = divide(spower, a)
        if iszero(remainder):
            break
        spower = mul(spower, s)
    else:
        raise ArithmeticError("squarefree root-set power identity failed")
    # Executable independent algebraic checks of the recorded root-set identities.
    if not iszero(add(mul(s, d), neg(a))) or not iszero(add(mul(a, t), neg(spower))):
        raise ArithmeticError("root-set identity replay failed")
    chain = sturm(s)
    guards = set()
    for poly in (a, s, d, t, *chain):
        for c in poly:
            guards.add(c.denominator)
        guards.add(poly[-1].numerator)
    for poly in (a, *chain):
        for x in (0, 1):
            e = evaluate(poly, x)
            guards.update((e.numerator, e.denominator))
    guards = tuple(sorted(g for g in guards if len(g) > 1))
    return {
        "zero": False,
        "guards": guards,
        "original": encode_poly(a),
        "squarefree": encode_poly(s),
        "quotient": encode_poly(d),
        "power_quotient": encode_poly(t),
        "root_set_exponent": exponent,
        "chain": tuple(encode_poly(c) for c in chain),
    }


def decide(a: Sequence[Element]) -> dict[str, Any]:
    """Exact existence of q in [0,1] with original H(alpha,q)>=0."""
    a = trim(a)
    if a[0].root is None:
        raise ValueError("decision requires a selected real effect")
    if iszero(a):
        return {"accepted": True, "kind": "zero", "original": encode_poly(a)}
    signs = tuple(evaluate(a, x).sign() for x in (0, 1))
    if max(signs) >= 0:
        return {
            "accepted": True,
            "kind": "endpoint",
            "endpoint_signs": signs,
            "original": encode_poly(a),
        }
    chain = sturm(a)
    vectors = tuple(tuple(evaluate(poly, x).sign() for poly in chain) for x in (0, 1))

    def changes(vector):
        nonzero = tuple(v for v in vector if v)
        return sum(x != y for x, y in zip(nonzero, nonzero[1:]))

    variations = tuple(changes(vector) for vector in vectors)
    count = variations[0] - variations[1]
    if not 0 <= count < len(a):
        raise ArithmeticError("invalid algebraic Sturm count")
    return {
        "accepted": count > 0,
        "kind": "interior_roots",
        "endpoint_signs": signs,
        "original": encode_poly(a),
        "chain": tuple(encode_poly(c) for c in chain),
        "sign_vectors": vectors,
        "variations": variations,
        "root_count": count,
    }


def specialize(
    coefficients: Sequence[Sequence[Exact]], root: Root | None, work: Work
) -> FieldPolynomial:
    """Create the original coefficient polynomial over the selected embedding."""
    return trim(tuple(Element(root, c, (1,), work) for c in coefficients))
