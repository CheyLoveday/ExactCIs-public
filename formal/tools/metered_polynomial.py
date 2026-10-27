"""Precharged exact rational polynomial arithmetic for development replay.

``operations`` counts actual delegated Fraction binary +, -, *, / calls. Bit
preflight bounds both numerator and denominator integer intermediates before
those calls; it can conservatively refuse a result which would reduce to fit.
``coefficients`` counts cumulative reserved coefficient slots, including copies,
not live Python memory. Bounds and counters do not claim instruction/RSS costs,
Lean verification of Python, a production capability limit or completeness.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import NoReturn, cast

import resource_model as resource

P = tuple[Q, ...]
ZERO: P = ()
ONE_Q = Q(1)
ZERO_Q = Q(0)
NEG_ONE_Q = Q(-1)
ONE: P = (ONE_Q,)


@dataclass(frozen=True)
class MeterLimits:
    max_degree: int = 128
    max_bits: int = 4096
    max_coefficients: int = 20_000
    max_operations: int = 2_000_000
    max_exponent: int = 128

    def __post_init__(self) -> None:
        if any(type(v) is not int or v <= 0 for v in vars(self).values()):
            raise ValueError("all diagnostic limits must be positive integers")


@dataclass(frozen=True)
class MeterState:
    operations: int
    coefficients: int
    coefficient_bits: int
    result_bit_bound: int


class ResourceLimit(RuntimeError):
    """Named refusal, preserving the counters before the refused operation."""

    def __init__(
        self, limit: str, state: MeterState, *, operation: str, requested: int
    ) -> None:
        self.limit = limit
        self.state = state
        self.operation = operation
        self.requested = requested
        super().__init__(
            f"{limit} limit before {operation}: requested={requested_text(requested)}; state={state}"
        )


def requested_text(value: int) -> str:
    """Keep diagnostics bounded even when a refused count has millions of bits."""
    bits = value.bit_length()
    return str(value) if bits <= 256 else f"<integer with {bits} bits>"


def _bits(value: Q) -> int:
    return max(value.numerator.bit_length(), value.denominator.bit_length())


def _product_bound(a: int, b: int) -> int:
    """A bit bound without multiplying or allocating absolute-value copies."""
    if not a or not b:
        return 0
    if a in (-1, 1):
        return b.bit_length()
    if b in (-1, 1):
        return a.bit_length()
    return a.bit_length() + b.bit_length()


class Meter:
    def __init__(
        self,
        limits: MeterLimits | None = None,
        *,
        resources: resource.Meter | None = None,
    ) -> None:
        self.limits = MeterLimits() if limits is None else limits
        if type(self.limits) is not MeterLimits:
            raise ValueError("limits must be a MeterLimits instance")
        self.operations = 0
        self.coefficients = 0
        self.coefficient_bits = 0
        self.result_bit_bound = 0
        self.resources = resource.Meter() if resources is None else resources
        if type(self.resources) is not resource.Meter:
            raise ValueError("a resource_model.Meter is required")
        self._pending_bound = 0

    def snapshot(self) -> MeterState:
        return MeterState(
            self.operations,
            self.coefficients,
            self.coefficient_bits,
            self.result_bit_bound,
        )

    def refuse(self, limit: str, *, operation: str, requested: int) -> NoReturn:
        raise ResourceLimit(
            limit, self.snapshot(), operation=operation, requested=requested
        )

    def charge_operation(self, operation: str) -> None:
        """Overridable precharge, immediately before one Fraction +-*/ call."""
        if self.operations >= self.limits.max_operations:
            self.refuse("operations", operation=operation, requested=1)
        event = {
            "add": resource.Event.RAT_ADD,
            "sub": resource.Event.RAT_SUB,
            "mul": resource.Event.RAT_MUL,
            "div": resource.Event.RAT_DIV,
        }[operation]
        self.resources.charge(
            event,
            resource.CostVector(
                rational_operations=1, maximum_operand_bits=self._pending_bound
            ),
            phase="rational",
        )
        self.operations += 1

    def reserve(self, count: int, *, operation: str) -> None:
        """Reserve all new coefficient slots before their list/tuple allocation."""
        if type(count) is not int or count < 0:
            raise ValueError("slot reservation must be a nonnegative integer")
        if count > self.limits.max_coefficients - self.coefficients:
            self.refuse("coefficients", operation=operation, requested=count)
        self.resources.charge(
            resource.Event.COEFFICIENTS,
            resource.CostVector(coefficient_slots=count),
            phase="polynomial",
        )
        self.coefficients += count

    def structural(self, count: int = 1) -> None:
        self.resources.charge(
            resource.Event.STRUCTURAL,
            resource.CostVector(structural_steps=count),
            phase="traversal",
        )

    def integer_step(self, bits: int = 0) -> None:
        if type(bits) is not int or bits < 0:
            raise ValueError("integer bound must be a nonnegative exact integer")
        if bits > self.limits.max_bits:
            self.refuse("bits", operation="integer primitive", requested=bits)
        self.resources.charge(
            resource.Event.INTEGER,
            resource.CostVector(integer_operations=1, maximum_operand_bits=bits),
            phase="integer",
        )

    def compare(self, a: Q, b: Q) -> int:
        """Exact cross-product order, with every delegated bigint call prepaid."""
        self.check(a)
        self.check(b)
        left_bits = _product_bound(a.numerator, b.denominator)
        right_bits = _product_bound(b.numerator, a.denominator)
        self.integer_step(left_bits)
        left = a.numerator * b.denominator
        self.integer_step(right_bits)
        right = b.numerator * a.denominator
        self.integer_step(max(left_bits, right_bits))
        greater = left > right
        self.integer_step(max(left_bits, right_bits))
        less = left < right
        return int(greater) - int(less)

    def check(self, value: Q) -> Q:
        if type(value) is not Q:
            raise ValueError("arithmetic operands must be exact Fraction values")
        bits = _bits(value)
        if bits > self.limits.max_bits:
            self.refuse("bits", operation="operand", requested=bits)
        self.resources.charge(
            resource.Event.OPERAND,
            resource.CostVector(maximum_operand_bits=bits),
            phase="rational",
        )
        self.coefficient_bits = max(self.coefficient_bits, bits)
        return value

    def integer(self, value: int) -> Q:
        """Check integer magnitude before constructing a Fraction operand."""
        if type(value) is not int:
            raise ValueError("an exact integer is required")
        bits = max(1, value.bit_length())
        if bits > self.limits.max_bits:
            self.refuse("bits", operation="integer conversion", requested=bits)
        self.integer_step(bits)
        self.coefficient_bits = max(self.coefficient_bits, bits)
        return Q(value)

    def _result(self, numerator: int, denominator: int, operation: str) -> None:
        bound = max(numerator, denominator)
        if bound > self.limits.max_bits:
            self.refuse("bits", operation=operation, requested=bound)
        self._pending_bound = bound
        try:
            self.charge_operation(operation)
        finally:
            self._pending_bound = 0
        self.result_bit_bound = max(self.result_bit_bound, bound)

    def _sum(self, a: Q, b: Q, operation: str) -> None:
        self.check(a)
        self.check(b)
        numerator = (
            max(
                _product_bound(a.numerator, b.denominator),
                _product_bound(b.numerator, a.denominator),
            )
            + 1
        )
        denominator = _product_bound(a.denominator, b.denominator)
        self._result(numerator, denominator, operation)

    def add(self, a: Q, b: Q) -> Q:
        self._sum(a, b, "add")
        result = a + b
        self.coefficient_bits = max(self.coefficient_bits, _bits(result))
        return result

    def sub(self, a: Q, b: Q) -> Q:
        self._sum(a, b, "sub")
        result = a - b
        self.coefficient_bits = max(self.coefficient_bits, _bits(result))
        return result

    def mul(self, a: Q, b: Q) -> Q:
        self.check(a)
        self.check(b)
        self._result(
            _product_bound(a.numerator, b.numerator),
            _product_bound(a.denominator, b.denominator),
            "mul",
        )
        result = a * b
        self.coefficient_bits = max(self.coefficient_bits, _bits(result))
        return result

    def div(self, a: Q, b: Q) -> Q:
        self.check(a)
        self.check(b)
        if not b.numerator:
            raise ValueError("division by zero rational")
        self._result(
            _product_bound(a.numerator, b.denominator),
            _product_bound(a.denominator, b.numerator),
            "div",
        )
        result = a / b
        self.coefficient_bits = max(self.coefficient_bits, _bits(result))
        return result

    def size(self, count: int, *, operation: str) -> None:
        if type(count) is not int or count < 0:
            raise ValueError("polynomial size must be a nonnegative integer")
        if count > self.limits.max_degree + 1:
            self.refuse("degree", operation=operation, requested=max(0, count - 1))
        self.resources.charge(
            resource.Event.DEGREE,
            resource.CostVector(maximum_polynomial_degree=max(0, count - 1)),
            phase="polynomial",
        )

    def poly(self, values: Sequence[Q | int]) -> P:
        """Validate supplied exact inputs before allocating their normalized tuple."""
        if type(values) not in (tuple, list):
            raise ValueError("polynomial input must be a tuple or list")
        self.size(len(values), operation="input polynomial")
        self.reserve(len(values), operation="input polynomial tuple")
        for v in values:
            self.structural()
            if type(v) is Q:
                self.check(v)
            elif type(v) is int:
                bits = v.bit_length()
                if bits > self.limits.max_bits:
                    self.refuse("bits", operation="input integer", requested=bits)
            else:
                raise ValueError("only exact int/Fraction coefficients are allowed")
        return _finish(
            tuple(self.integer(v) if type(v) is int else cast(Q, v) for v in values),
            self,
        )


def trim(p: P) -> P:
    """Pure normalization; arithmetic callers use the metered `_finish` wrapper."""
    end = len(p)
    while end and not p[end - 1]:
        end -= 1
    return p if end == len(p) else p[:end]


def _finish(p: P, m: Meter) -> P:
    end = len(p)
    while end:
        m.structural()
        m.integer_step()
        if p[end - 1]:
            break
        end -= 1
    if end == len(p):
        return p
    if not end:
        return ZERO
    m.reserve(end, operation="trimmed polynomial tuple")
    return p[:end]


def _checked(p: P, m: Meter) -> P:
    if type(p) is not tuple:
        raise ValueError("arithmetic polynomials must be exact Fraction tuples")
    m.size(len(p), operation="polynomial operand")
    if len(p) > m.limits.max_coefficients:
        m.refuse("coefficients", operation="polynomial operand", requested=len(p))
    for c in p:
        m.structural()
        m.check(c)
    return _finish(p, m)


def equal(a: P, b: P, m: Meter) -> bool:
    """Equality of normalized signed coefficient vectors, preserving scale."""
    a, b = _checked(a, m), _checked(b, m)
    m.structural()
    if len(a) != len(b):
        return False
    for x, y in zip(a, b):
        m.structural()
        if m.compare(x, y):
            return False
    return True


def canonical(values: P, m: Meter) -> P:
    if type(values) is not tuple:
        raise ValueError("a canonical polynomial must be an immutable tuple")
    m.size(len(values), operation="canonical polynomial preflight")
    for coefficient in values:
        m.structural()
        if type(coefficient) is not Q:
            raise ValueError("canonical coefficients must be exact Fractions")
    result = m.poly(values)
    if len(result) != len(values):
        raise ValueError("canonical polynomials cannot have trailing zero slots")
    return result


def add(a: P, b: P, m: Meter) -> P:
    a, b = _checked(a, m), _checked(b, m)
    count = max(len(a), len(b))
    m.size(count, operation="polynomial sum")
    m.reserve(count, operation="polynomial sum tuple")
    return _finish(
        tuple(
            m.add(a[i] if i < len(a) else ZERO_Q, b[i] if i < len(b) else ZERO_Q)
            for i in range(count)
        ),
        m,
    )


def scale(c: Q, p: P, m: Meter) -> P:
    m.check(c)
    p = _checked(p, m)
    m.reserve(len(p), operation="scaled polynomial tuple")
    return _finish(tuple(m.mul(c, a) for a in p), m)


def mul(a: P, b: P, m: Meter) -> P:
    a, b = _checked(a, m), _checked(b, m)
    if not a or not b:
        return ZERO
    count = len(a) + len(b) - 1
    m.size(count, operation="polynomial product")
    m.reserve(count, operation="polynomial product list")
    out = [ZERO_Q for _ in range(count)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            m.structural()
            out[i + j] = m.add(out[i + j], m.mul(x, y))
    m.reserve(count, operation="polynomial product tuple")
    return _finish(tuple(out), m)


def power(p: P, n: int, m: Meter) -> P:
    p = _checked(p, m)
    if type(n) is not int or n < 0:
        raise ValueError("exponent must be a nonnegative integer")
    if n > m.limits.max_exponent:
        m.refuse("exponent", operation="polynomial power", requested=n)
    if p and n * (len(p) - 1) > m.limits.max_degree:
        m.refuse("degree", operation="polynomial power", requested=n * (len(p) - 1))
    out = ONE
    for _ in range(n):
        m.structural()
        out = mul(out, p, m)
    return out


def derivative(p: P, m: Meter) -> P:
    p = _checked(p, m)
    count = max(0, len(p) - 1)
    m.reserve(count, operation="derivative tuple")
    return _finish(tuple(m.mul(m.integer(i), p[i]) for i in range(1, len(p))), m)


def value(p: P, x: Q, m: Meter) -> Q:
    p = _checked(p, m)
    m.check(x)
    out = ZERO_Q
    for c in reversed(p):
        m.structural()
        out = m.add(c, m.mul(x, out))
    return out


def divide(a: P, b: P, m: Meter) -> tuple[P, P]:
    a, b = _checked(a, m), _checked(b, m)
    if not b:
        raise ValueError("division by zero polynomial")
    if len(a) < len(b):
        return ZERO, a
    qcount = len(a) - len(b) + 1
    m.reserve(len(a) + qcount, operation="division remainder and quotient lists")
    rem, quot = list(a), [ZERO_Q for _ in range(qcount)]
    while rem and len(rem) >= len(b):
        m.structural()
        offset = len(rem) - len(b)
        c = m.div(rem[-1], b[-1])
        quot[offset] = m.add(quot[offset], c)
        for j, coefficient in enumerate(b):
            m.structural()
            rem[offset + j] = m.sub(rem[offset + j], m.mul(c, coefficient))
        while rem:
            m.structural()
            m.integer_step()
            if rem[-1]:
                break
            rem.pop()
    m.reserve(len(quot) + len(rem), operation="division output tuples")
    return _finish(tuple(quot), m), tuple(rem)


def exact_divide(a: P, b: P, m: Meter) -> P:
    quotient, remainder = divide(a, b, m)
    if remainder:
        raise ValueError("nonzero exact-division remainder")
    return quotient


def xgcd(a: P, b: P, m: Meter) -> tuple[P, P, P]:
    a, b = _checked(a, m), _checked(b, m)
    u, v, u1, v1 = ONE, ZERO, ZERO, ONE
    while b:
        m.structural()
        q, r = divide(a, b, m)
        a, b = b, r
        u, u1 = u1, add(u, scale(NEG_ONE_Q, mul(q, u1, m), m), m)
        v, v1 = v1, add(v, scale(NEG_ONE_Q, mul(q, v1, m), m), m)
    if not a:
        return ZERO, ZERO, ZERO
    c = m.div(ONE_Q, a[-1])
    return scale(c, a, m), scale(c, u, m), scale(c, v, m)
