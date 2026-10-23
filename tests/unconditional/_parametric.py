"""Small exact polynomial calculations over Q(s) and a real embedding Q(alpha).

The projection certificate records rational-function identities and every
guard needed to specialize its signed Sturm chain. Exceptional effects are
rebuilt over their selected real embedding, never classified by a neighbour.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import asdict, dataclass
from fractions import Fraction
from math import comb, gcd, lcm
from typing import Any

from . import _polynomial as p
from ._algebraic import Element, Root, Work, primitive
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


def primitive_part(a: Sequence[Element]) -> tuple[FieldPolynomial, Element]:
    """Clear coefficient denominators/content, returning a = scale * primitive.

    Over Q(s), clear rational polynomial content. At a selected embedding,
    normalize by a nonzero field coefficient; the identity then holds at that
    embedding, not necessarily as an identity in Q(s). No irreducibility is assumed.
    """
    a = trim(a)
    w, root = a[0].work, a[0].root
    if iszero(a):
        return a, a[0].coerce(1)
    if root is not None and root.rational is None:
        # In Q(alpha), polynomial content in the ambient rational variable is
        # representation-dependent. Normalize by one checked nonzero field
        # coefficient instead, and retain its sign in the remainder evidence.
        scale = a[-1]
        return trim(tuple(c / scale for c in a)), scale
    w.tick("primitive_content")
    denominator = p.ONE
    for c in a:
        if c.denominator == p.ONE or c.denominator == denominator:
            continue
        common = w.gcd(denominator, c.denominator)
        denominator = w.call(
            "multiply", denominator, w.call("divide", c.denominator, common)[0]
        )
    numerators = tuple(
        c.numerator
        if denominator == c.denominator
        else w.call(
            "multiply", c.numerator, w.call("divide", denominator, c.denominator)[0]
        )
        for c in a
    )
    common = p.ZERO
    for poly in numerators:
        common = w.gcd(common, poly)
        if common == p.ONE:
            break
    if common != p.ONE:
        numerators = tuple(w.call("divide", poly, common)[0] for poly in numerators)
    coefficients = tuple(v for poly in numerators for v in poly)
    den = lcm(*(v.denominator for v in coefficients))
    content = Fraction(gcd(*(int(v * den) for v in coefficients)), den)
    result = trim(
        tuple(
            Element(root, tuple(v / content for v in poly), p.ONE, w)
            for poly in numerators
        )
    )
    scale = Element(root, tuple(v * content for v in common), denominator, w)
    return result, scale


def primitive_remainder(a: Sequence[Element], b: Sequence[Element]):
    """Fraction-free remainder with factored exact rescaling.

    rem(a,b) = product(numerators) / product(denominators) * result.
    Clearing content at each elimination prevents removable coefficient growth.
    """
    a, b = trim(a), trim(b)
    if iszero(b):
        raise ValueError("division by zero field polynomial")
    if a[0].root is not None and a[0].root.rational is None:
        # Exact field division keeps coefficients reduced at the selected
        # embedding. The generic Q(s) branch below remains fraction-free.
        remainder = divide(a, b)[1]
        result, scale = primitive_part(remainder)
        return result, (scale,), ()
    numerators, denominators = [], []
    while not iszero(a) and len(a) >= len(b):
        shift = len(a) - len(b)
        leading = a[-1]
        remainder = [b[-1] * c for c in a]
        for i, c in enumerate(b):
            remainder[shift + i] = remainder[shift + i] - leading * c
        a, scale = primitive_part(remainder)
        numerators.append(scale)
        denominators.append(b[-1])
    return a, tuple(numerators), tuple(denominators)


def squarefree(a: Sequence[Element]) -> FieldPolynomial:
    if iszero(a):
        raise ValueError("zero polynomial has no finite root set")
    left, right = primitive_part(a)[0], primitive_part(derivative(a))[0]
    while not iszero(right):
        left, right = right, primitive_remainder(left, right)[0]
    return primitive_part(exact_divide(a, left))[0]


@dataclass(frozen=True)
class SturmTerm:
    """A signed Sturm polynomial with factored numerator/denominator scales.

    Keeping scales factored avoids expanding coefficients that do not affect
    root counts. Their signs and specialization zeros remain part of the proof
    data; making every remainder monic without these scales would be wrong.
    """

    polynomial: FieldPolynomial
    scales: tuple[Element, ...]
    divisors: tuple[Element, ...] = ()

    def sign_at(self, x: int) -> int:
        sign = evaluate(self.polynomial, x).sign()
        for scale in self.scales + self.divisors:
            sign *= scale.sign()
        return sign

    def encode(self) -> dict[str, Any]:
        return {
            "polynomial": encode_poly(self.polynomial),
            "scales": tuple(encode_element(c) for c in self.scales),
            "divisors": tuple(encode_element(c) for c in self.divisors),
        }


def sturm(
    a: Sequence[Element], *, squarefree_input: bool = False
) -> tuple[SturmTerm, ...]:
    a = trim(a) if squarefree_input else squarefree(trim(a))
    if len(a) == 1:
        return (SturmTerm(a, ()),)
    da, scale = primitive_part(derivative(a))
    chain = [SturmTerm(a, ()), SturmTerm(da, (scale,))]
    while True:
        remainder, scales, divisors = primitive_remainder(
            chain[-2].polynomial, chain[-1].polynomial
        )
        if iszero(remainder):
            return tuple(chain)
        chain.append(
            SturmTerm(
                remainder,
                chain[-2].scales + scales + (a[0].coerce(-1),),
                chain[-2].divisors + divisors,
            )
        )


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
    chain = sturm(s, squarefree_input=True)
    guards = set()
    for poly in (a, s, d, t, *(term.polynomial for term in chain)):
        for c in poly:
            guards.add(c.denominator)
        guards.add(poly[-1].numerator)
    for term in chain:
        for c in term.scales + term.divisors:
            guards.update((c.numerator, c.denominator))
    for poly in (a, *(term.polynomial for term in chain)):
        for x in (0, 1):
            e = evaluate(poly, x)
            guards.update((e.numerator, e.denominator))
    # Guards define zero sets, so nonzero scalar multiples and multiplicities
    # may be removed. The signed original polynomials remain in the packet.
    guards = tuple(sorted({primitive(g, a[0].work) for g in guards if len(g) > 1}))
    return {
        "zero": False,
        "guards": guards,
        "original": encode_poly(a),
        "squarefree": encode_poly(s),
        "quotient": encode_poly(d),
        "power_quotient": encode_poly(t),
        "root_set_exponent": exponent,
        "chain": tuple(c.encode() for c in chain),
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
    # Exact sufficient checks precede the complete root-count fallback. They
    # use the original signed H; field normalization never defines acceptance.
    for point in (Fraction(1, 2), Fraction(1, 4), Fraction(3, 4)):
        witness = evaluate(a, point)
        sign = witness.sign()
        if sign >= 0:
            return {
                "accepted": True,
                "kind": "rational_witness",
                "point": point,
                "value": encode_element(witness),
                "sign": sign,
                "original": encode_poly(a),
            }
    if a[0].root.rational is not None:
        # Coercion at a rational selected root has already produced constants.
        # Reuse the independent exact-rational certificate, avoiding repeated
        # algebraic wrappers around its ordinary rational polynomial arithmetic.
        coefficients = tuple(c.numerator[0] for c in a)
        certificate = a[0].work.call("root_certificate", coefficients)
        return {
            "accepted": certificate.interior_roots > 0,
            "kind": "rational_roots",
            "certificate": asdict(certificate),
            "original": encode_poly(a),
        }
    degree = len(a) - 1
    controls = tuple(
        sum(
            (a[j] * Fraction(comb(k, j), comb(degree, j)) for j in range(k + 1)),
            a[0].coerce(0),
        )
        for k in range(degree + 1)
    )
    control_signs = tuple(c.sign() for c in controls)
    if all(sign < 0 for sign in control_signs):
        return {
            "accepted": False,
            "kind": "negative_controls",
            "controls": encode_poly(controls),
            "signs": control_signs,
            "original": encode_poly(a),
        }
    chain = sturm(a)
    vectors = tuple(tuple(term.sign_at(x) for term in chain) for x in (0, 1))

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
        "chain": tuple(c.encode() for c in chain),
        "sign_vectors": vectors,
        "variations": variations,
        "root_count": count,
    }


def specialize(
    coefficients: Sequence[Sequence[Exact]], root: Root | None, work: Work
) -> FieldPolynomial:
    """Create the original coefficient polynomial over the selected embedding."""
    return trim(tuple(Element(root, c, (1,), work) for c in coefficients))
