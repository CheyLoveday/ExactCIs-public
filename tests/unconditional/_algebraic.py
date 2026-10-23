"""Exact selected-real-root arithmetic for the independent topology oracle.

Defining polynomials need not be irreducible. Arithmetic is evaluated at one
checked real embedding; a quotient-ring inverse is never assumed. All work is
bounded explicitly. This is test infrastructure, not the production engine.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass, field
from fractions import Fraction as F
from functools import cmp_to_key
from math import gcd, lcm
from typing import Any

from . import _polynomial as p


@dataclass(frozen=True)
class Limits:
    max_calls: int = 100_000
    max_refinements: int = 4096
    max_degree: int = 64
    max_bits: int = 16_384
    polynomial_operations: int = 2_000_000

    def __post_init__(self) -> None:
        for value in vars(self).values():
            if type(value) is not int or value <= 0:
                raise ValueError("algebraic limits must be positive integers")


@dataclass
class Work:
    limits: Limits = field(default_factory=Limits)
    counts: dict[str, int] = field(default_factory=dict)
    signs: dict[tuple[Root, p.Polynomial], int] = field(default_factory=dict)
    refined: dict[Root, Root] = field(default_factory=dict)
    inverses: dict[tuple[p.Polynomial, p.Polynomial], p.Polynomial | None] = field(
        default_factory=dict
    )
    primitives: dict[p.Polynomial, tuple[int, ...]] = field(default_factory=dict)
    chains: dict[p.Polynomial, tuple[p.Polynomial, ...]] = field(default_factory=dict)

    components: dict[Root, Root] = field(default_factory=dict)

    def tick(self, category: str) -> None:
        self.counts[category] = self.counts.get(category, 0) + 1
        if sum(self.counts.values()) > self.limits.max_calls:
            raise p.OracleLimitError(f"algebraic call budget exceeded: {category}")
        if self.counts.get("refinement", 0) > self.limits.max_refinements:
            raise p.OracleLimitError("algebraic refinement budget exceeded")

    def call(self, name: str, *args: Any, **kwargs: Any) -> Any:
        self.tick(name)
        if name == "count_roots":
            return self.count_roots(*args, **kwargs)
        return getattr(p, name)(
            *args,
            limits=p.OracleLimits(
                self.limits.max_degree,
                self.limits.max_bits,
                self.limits.polynomial_operations,
            ),
            **kwargs,
        )

    def positive_primitive(self, a: Sequence[p.Exact]) -> p.Polynomial:
        """Rescale only by a positive rational, preserving every sign."""
        a = self.call("trim", a)
        if a == p.ZERO:
            return a
        den = lcm(*(c.denominator for c in a))
        content = gcd(*(int(c * den) for c in a))
        return self.call("trim", tuple(F(int(c * den), content) for c in a))

    def signed_chain(self, a: Sequence[p.Exact]) -> tuple[p.Polynomial, ...]:
        a = self.call("trim", a)
        if a in self.chains:
            self.tick("chain_cache_hit")
            return self.chains[a]
        first = self.positive_primitive(a)
        chain = [first]
        if len(first) > 1:
            chain.append(self.positive_primitive(self.call("derivative", first)))
            while True:
                left, right = chain[-2], chain[-1]
                while left != p.ZERO and len(left) >= len(right):
                    shift = len(left) - len(right)
                    lead = left[-1] * (1 if right[-1] > 0 else -1)
                    multiplied = self.call("multiply", (abs(right[-1]),), left)
                    subtraction = (F(0),) * shift + tuple(-lead * c for c in right)
                    left = self.positive_primitive(
                        self.call("add", multiplied, subtraction)
                    )
                if left == p.ZERO:
                    break
                chain.append(tuple(-c for c in left))
        result = tuple(chain)
        self.chains[a] = result
        return result

    def root_variations(self, a, left, right):
        if not isinstance(left, F) or not isinstance(right, F) or left >= right:
            raise ValueError("root interval requires increasing Fractions")
        a = primitive(a, self)
        endpoints = []
        for point in (left, right):
            at_root = not self.call("evaluate", a, point)
            endpoints.append(at_root)
            if at_root:
                a, remainder = self.call("divide", a, (-point, F(1)))
                if remainder != p.ZERO:
                    raise ArithmeticError("root endpoint division failed")
        chain = self.signed_chain(a)
        variations = []
        for point in (left, right):
            values = tuple(self.call("evaluate", term, point) for term in chain)
            signs = tuple((v > 0) - (v < 0) for v in values if v)
            variations.append(sum(x != y for x, y in zip(signs, signs[1:])))
        if not 0 <= variations[0] - variations[1] <= len(a) - 1:
            raise ArithmeticError("invalid primitive Sturm root count")
        return tuple(variations), tuple(endpoints)

    def count_roots(self, a, left, right, *, closed=False):
        if type(closed) is not bool:
            raise ValueError("closed must be a bool")
        if len(a) <= 5:
            return p.count_roots(
                a,
                left,
                right,
                closed=closed,
                limits=p.OracleLimits(
                    self.limits.max_degree,
                    self.limits.max_bits,
                    self.limits.polynomial_operations,
                ),
            )
        variations, endpoints = self.root_variations(a, left, right)
        return variations[0] - variations[1] + (sum(endpoints) if closed else 0)

    def monic(self, a: Sequence[p.Exact]) -> p.Polynomial:
        a = self.call("trim", a)
        if a == p.ZERO:
            return a
        return self.call("trim", tuple(c / a[-1] for c in a))

    def gcd(self, a: Sequence[p.Exact], b: Sequence[p.Exact]) -> p.Polynomial:
        a, b = self.monic(a), self.monic(b)
        while b != p.ZERO:
            a, b = b, self.monic(self.call("divide", a, b)[1])
        return a

    def inverse_mod(
        self, denominator: Sequence[p.Exact], modulus: Sequence[p.Exact]
    ) -> p.Polynomial | None:
        """Invert only a proved unit, even when the modulus is reducible."""
        key = tuple(denominator), tuple(modulus)
        if key in self.inverses:
            self.tick("inverse_cache_hit")
            return self.inverses[key]
        left, right = self.monic(modulus), denominator
        old, current = p.ZERO, p.ONE
        while right != p.ZERO:
            quotient, remainder = self.call("divide", left, right)
            following = self.call(
                "add", old, tuple(-v for v in self.call("multiply", quotient, current))
            )
            if remainder != p.ZERO:
                lead = remainder[-1]
                remainder = self.call("trim", tuple(v / lead for v in remainder))
                following = self.call("trim", tuple(v / lead for v in following))
            left, right, old, current = right, remainder, current, following
        if len(left) > 1:
            self.inverses[key] = None
            return None
        inverse = self.call("trim", tuple(v / left[0] for v in old))
        product = self.call("multiply", denominator, inverse)
        if self.call("divide", product, modulus)[1] != p.ONE:
            raise ArithmeticError("modular inverse identity failed")
        self.inverses[key] = inverse
        return inverse


def primitive(a: Sequence[p.Exact], work: Work) -> tuple[int, ...]:
    """Primitive integer squarefree polynomial, with positive leading term."""
    a = work.call("trim", a)
    if a == p.ZERO:
        raise ValueError("the zero polynomial has infinitely many roots")
    key = a
    if key in work.primitives:
        work.tick("primitive_cache_hit")
        return work.primitives[key]
    divisor = work.gcd(a, work.call("derivative", a))
    a, remainder = work.call("divide", a, divisor)
    if remainder != p.ZERO:
        raise ArithmeticError("squarefree gcd did not divide exactly")
    den = lcm(*(c.denominator for c in a))
    integers = tuple(int(c * den) for c in a)
    content = gcd(*integers)
    result = tuple(v // (content if integers[-1] > 0 else -content) for v in integers)
    work.call("trim", result)
    work.primitives[key] = result
    return result


@dataclass(frozen=True)
class Root:
    polynomial: tuple[int, ...]
    left: F
    right: F

    @property
    def rational(self) -> F | None:
        return self.left if self.left == self.right else None

    def verify(self, work: Work) -> Root:
        if self.polynomial != primitive(self.polynomial, work):
            raise ValueError("root polynomial must be primitive and squarefree")
        if len(self.polynomial) < 2:
            raise ValueError("constant polynomial cannot define a root")
        if not isinstance(self.left, F) or not isinstance(self.right, F):
            raise ValueError("isolator endpoints must be exact Fractions")
        if self.left > self.right:
            raise ValueError("reversed root isolator")
        lv = work.call("evaluate", self.polynomial, self.left)
        rv = work.call("evaluate", self.polynomial, self.right)
        if self.rational is not None:
            if lv:
                raise ValueError("claimed rational point is not a root")
        elif (
            not lv
            or not rv
            or work.call("count_roots", self.polynomial, self.left, self.right) != 1
        ):
            raise ValueError("isolator must have nonroot ends and exactly one root")
        return self


def refine(root: Root, work: Work) -> Root:
    if root in work.refined:
        work.tick("refinement_cache_hit")
        return work.refined[root]
    if root.rational is not None:
        return root
    work.tick("refinement")
    mid = (root.left + root.right) / 2
    if not work.call("evaluate", root.polynomial, mid):
        result = Root(root.polynomial, mid, mid)
    elif work.call("count_roots", root.polynomial, root.left, mid):
        result = Root(root.polynomial, root.left, mid)
    else:
        result = Root(root.polynomial, mid, root.right)
    work.refined[root] = result
    return result


def isolate(a: Sequence[p.Exact], left: F, right: F, work: Work) -> tuple[Root, ...]:
    """Isolate all distinct roots on a closed rational interval, in order."""
    if not isinstance(left, F) or not isinstance(right, F) or left >= right:
        raise ValueError("isolation needs increasing Fraction endpoints")
    a = primitive(a, work)
    if len(a) == 1:
        return ()
    roots = []
    for endpoint in (left, right):
        if not work.call("evaluate", a, endpoint):
            roots.append(Root(a, endpoint, endpoint))
            # Endpoint factors are irrelevant to every interior embedding.
            # Remove them by checked exact division before isolating its roots.
            quotient, remainder = work.call("divide", a, (-endpoint, F(1)))
            if remainder != p.ZERO:
                raise ArithmeticError("endpoint factor did not divide exactly")
            a = primitive(quotient, work)
    if len(a) == 2:
        point = F(-a[0], a[1])
        if left < point < right:
            roots.append(Root(a, point, point))
        return tuple(sorted(roots, key=lambda r: (r.left, r.right)))
    pending = [(left, right)]
    while pending:
        lo, hi = pending.pop()
        count = work.call("count_roots", a, lo, hi)
        if not count:
            continue
        if count == 1 and work.call("evaluate", a, lo) and work.call("evaluate", a, hi):
            roots.append(Root(a, lo, hi))
            continue
        work.tick("refinement")
        mid = (lo + hi) / 2
        if not work.call("evaluate", a, mid):
            roots.append(Root(a, mid, mid))
        pending.extend(((mid, hi), (lo, mid)))
    return tuple(sorted(roots, key=lambda r: (r.left, r.right)))


def interval(a: Sequence[p.Exact], left: F, right: F) -> tuple[F, F]:
    """Exact Horner interval; no floating enclosure assumptions."""
    low = high = F(0)
    for c in reversed(a):
        products = (low * left, low * right, high * left, high * right)
        low, high = min(products) + c, max(products) + c
    return low, high


def sign_at(a: Sequence[p.Exact], root: Root, work: Work) -> int:
    root = work.components.get(root, root)
    a = work.call("trim", a)
    if len(a) == 1:
        return (a[0] > 0) - (a[0] < 0)
    key = root, a
    if key in work.signs:
        work.tick("sign_cache_hit")
        return work.signs[key]
    original = root
    root = work.refined.get(root, root)
    if root.rational is not None:
        v = work.call("evaluate", a, root.rational)
        result = (v > 0) - (v < 0)
        work.signs[key] = result
        return result
    # A strict rational interval sign already proves nonvanishing; computing
    # a gcd first can needlessly inflate coefficients at high-degree events.
    work.tick("sign_interval")
    lo, hi = interval(a, root.left, root.right)
    work.call("trim", (lo, hi))
    if lo > 0 or hi < 0:
        result = 1 if lo > 0 else -1
        work.signs[key] = result
        return result
    common = work.gcd(a, root.polynomial)
    if len(common) > 1 and work.call("count_roots", common, root.left, root.right):
        work.signs[key] = 0
        return 0
    while True:
        work.tick("sign_interval")
        lo, hi = interval(a, root.left, root.right)
        work.call("trim", (lo, hi))  # enforce coefficient-bit limits
        if lo > 0:
            if original != root:
                work.refined[original] = root
            work.signs[key] = 1
            return 1
        if hi < 0:
            if original != root:
                work.refined[original] = root
            work.signs[key] = -1
            return -1
        root = refine(root, work)


def compare(a: Root, b: Root, work: Work) -> int:
    """Order roots, detecting equality across different defining polynomials."""
    while a in work.refined:
        a = work.refined[a]
        work.tick("refinement_cache_hit")
    while b in work.refined:
        b = work.refined[b]
        work.tick("refinement_cache_hit")
    if a.rational is not None:
        return -sign_at((-a.rational, F(1)), b, work)
    if b.rational is not None:
        return sign_at((-b.rational, F(1)), a, work)
    common = work.gcd(a.polynomial, b.polynomial)
    while True:
        if a.right <= b.left:
            return -1
        if b.right <= a.left:
            return 1
        left, right = max(a.left, b.left), min(a.right, b.right)
        if len(common) > 1 and work.call("count_roots", common, left, right):
            return 0
        a, b = refine(a, work), refine(b, work)
        if a.rational is not None or b.rational is not None:
            return compare(a, b, work)


def merge_roots(roots: Sequence[Root], work: Work) -> tuple[Root, ...]:
    ordered = sorted(roots, key=cmp_to_key(lambda a, b: compare(a, b, work)))
    unique = []
    for root in ordered:
        if not unique or compare(unique[-1], root, work):
            unique.append(root)
        else:
            previous = unique[-1]
            common = primitive(work.gcd(previous.polynomial, root.polynomial), work)
            unique[-1] = Root(
                common, max(previous.left, root.left), min(previous.right, root.right)
            )
    return tuple(unique)


def between(left: Root, right: Root, work: Work) -> F:
    """A rational representative strictly between two proved distinct roots."""
    if compare(left, right, work) >= 0:
        raise ValueError("cell endpoints are not strictly ordered")
    while left.right >= right.left:
        left, right = refine(left, work), refine(right, work)
    return (left.right + right.left) / 2


class Element:
    """Rational function, or P(alpha)/D(alpha) at a checked real embedding.

    ``root=None`` denotes the rational function field Q(s), not an ordered
    embedding. An algebraic root must come from ``isolate`` or ``Root.verify``.
    """

    def __init__(
        self,
        root: Root | None,
        numerator: Sequence[p.Exact],
        denominator: Sequence[p.Exact],
        work: Work,
    ) -> None:
        self.root, self.work = root, work
        original_root = root
        root = work.components.get(root, root)
        if root is not None and root.rational is not None:
            num = work.call("evaluate", numerator, root.rational)
            den = work.call("evaluate", denominator, root.rational)
            if not den:
                raise ValueError("zero denominator at selected algebraic root")
            self.numerator = work.call("trim", (num / den,))
            self.denominator = p.ONE
            return
        if root is None:
            self.numerator = work.call("trim", numerator)
            self.denominator = work.call("trim", denominator)
            nonzero = self.denominator != p.ZERO
        else:

            def reduced(poly):
                poly = work.call("trim", poly)
                return (
                    work.call("divide", poly, root.polynomial)[1]
                    if len(poly) >= len(root.polynomial)
                    else poly
                )

            self.numerator = reduced(numerator)
            self.denominator = reduced(denominator)
            nonzero = sign_at(self.denominator, root, work)
        if not nonzero:
            raise ValueError("zero denominator at selected algebraic root")
        if self.numerator == p.ZERO:
            self.denominator = p.ONE
            return
        if len(self.denominator) == 1:
            self.numerator = work.call(
                "trim", tuple(v / self.denominator[0] for v in self.numerator)
            )
            self.denominator = p.ONE
            return
        if root is not None and len(self.denominator) > 1:
            inverse = work.inverse_mod(self.denominator, root.polynomial)
            if inverse is None:
                # The denominator is nonzero at the selected root. Remove
                # components where it vanishes by checked exact division.
                common = work.gcd(self.denominator, root.polynomial)
                quotient, remainder = work.call("divide", root.polynomial, common)
                if remainder != p.ZERO:
                    raise ArithmeticError("component factor did not divide exactly")
                root = Root(primitive(quotient, work), root.left, root.right).verify(
                    work
                )
                work.components[original_root] = root
                inverse = work.inverse_mod(self.denominator, root.polynomial)
                if inverse is None:
                    raise ArithmeticError("localized denominator is not a unit")
            if inverse is not None:
                self.numerator = work.call(
                    "divide",
                    work.call("multiply", self.numerator, inverse),
                    root.polynomial,
                )[1]
                self.denominator = p.ONE
                return
        common = work.gcd(self.numerator, self.denominator)
        self.numerator = work.call("divide", self.numerator, common)[0]
        self.denominator = work.call("divide", self.denominator, common)[0]
        scale = self.denominator[-1]
        self.numerator = work.call("trim", tuple(v / scale for v in self.numerator))
        self.denominator = work.call("trim", tuple(v / scale for v in self.denominator))

    def coerce(self, other: Element | int | F) -> Element:
        if isinstance(other, Element):
            if self.root != other.root or self.work is not other.work:
                raise ValueError("mixed algebraic embeddings or work contexts")
            return other
        if type(other) is int or isinstance(other, F):
            return Element(self.root, (F(other),), p.ONE, self.work)
        raise ValueError("algebraic arithmetic requires exact scalar values")

    def __bool__(self) -> bool:
        if self.root is None:
            return self.numerator != p.ZERO
        return bool(sign_at(self.numerator, self.root, self.work))

    def sign(self) -> int:
        if self.root is None:
            raise ValueError("a rational function needs a selected effect for its sign")
        return sign_at(self.numerator, self.root, self.work) * sign_at(
            self.denominator, self.root, self.work
        )

    def __neg__(self) -> Element:
        return Element(
            self.root, tuple(-c for c in self.numerator), self.denominator, self.work
        )

    def __add__(self, other: Element | int | F) -> Element:
        b, w = self.coerce(other), self.work
        if self.numerator == p.ZERO or b.numerator == p.ZERO:
            w.tick("zero_addition")
            return b if self.numerator == p.ZERO else self
        if self.denominator == p.ONE and b.denominator == p.ONE:
            return Element(
                self.root, w.call("add", self.numerator, b.numerator), p.ONE, w
            )
        common = (
            w.gcd(self.denominator, b.denominator)
            if len(self.denominator) > 1 and len(b.denominator) > 1
            else p.ONE
        )
        left_scale = w.call("divide", b.denominator, common)[0]
        right_scale = w.call("divide", self.denominator, common)[0]
        return Element(
            self.root,
            w.call(
                "add",
                w.call("multiply", self.numerator, left_scale),
                w.call("multiply", b.numerator, right_scale),
            ),
            w.call("multiply", self.denominator, left_scale),
            w,
        )

    __radd__ = __add__

    def __sub__(self, other: Element | int | F) -> Element:
        return self + -self.coerce(other)

    def __rsub__(self, other: Element | int | F) -> Element:
        return self.coerce(other) - self

    def _product(self, numerator: p.Polynomial, denominator: p.Polynomial) -> Element:
        w = self.work
        a, b, c, d = self.numerator, self.denominator, numerator, denominator
        if a == p.ZERO or c == p.ZERO:
            w.tick("zero_product")
            return self.coerce(0)
        if c == d:
            w.tick("unit_product")
            return self
        # Cancel before multiplication so removable factors do not exhaust
        # intermediate-degree limits. No sign or real-root assumption is used.
        if self.root is None and len(a) > 1 and len(d) > 1:
            common = w.gcd(a, d)
            a, d = w.call("divide", a, common)[0], w.call("divide", d, common)[0]
        if self.root is None and len(c) > 1 and len(b) > 1:
            common = w.gcd(c, b)
            c, b = w.call("divide", c, common)[0], w.call("divide", b, common)[0]
        return Element(
            self.root,
            w.call("multiply", a, c),
            w.call("multiply", b, d),
            w,
        )

    def __mul__(self, other: Element | int | F) -> Element:
        b = self.coerce(other)
        return self._product(b.numerator, b.denominator)

    __rmul__ = __mul__

    def __truediv__(self, other: Element | int | F) -> Element:
        b = self.coerce(other)
        if not b:
            raise ValueError("division by zero algebraic value")
        return self._product(b.denominator, b.numerator)

    def __rtruediv__(self, other: Element | int | F) -> Element:
        return self.coerce(other) / self

    def __pow__(self, exponent: int) -> Element:
        if type(exponent) is not int or exponent < 0:
            raise ValueError("element power must be a natural number")
        result, base = self.coerce(1), self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent //= 2
            if exponent:
                base = base * base
        return result
