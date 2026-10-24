"""Independent, bounded rational polynomial reference for U1 fixtures.

Coefficients are ascending powers and use only exact ``int``/``Fraction`` input.
The limits below bound this small-table diagnostic oracle; they are neither
production capability limits nor claims about all ExactCIs inputs. A counted
operation is one Fraction addition, subtraction, multiplication, or division;
bit telemetry checks every arithmetic result and input coefficient. Root counts
are distinct real roots, with explicit ownership of the two interval endpoints.

Monic normalisation preserves root sets, not signs. Threshold decisions retain
the original polynomial, and signed Sturm remainders are never made monic.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction

Exact = int | Fraction
Polynomial = tuple[Fraction, ...]
EncodedRational = tuple[int, int]
EncodedPolynomial = tuple[EncodedRational, ...]
ZERO: Polynomial = (Fraction(0),)
ONE: Polynomial = (Fraction(1),)


class OracleLimitError(RuntimeError):
    """The reference calculation exceeded its explicit diagnostic scope."""


@dataclass(frozen=True)
class OracleLimits:
    """Reference-only budgets, independent of future production capability."""

    max_degree: int = 64
    max_coefficient_bits: int = 16_384
    max_operations: int = 2_000_000

    def __post_init__(self) -> None:
        for name in ("max_degree", "max_coefficient_bits", "max_operations"):
            value = getattr(self, name)
            if type(value) is not int or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")
        if self.max_coefficient_bits == 0:
            raise ValueError("max_coefficient_bits must be positive")


DEFAULT_LIMITS = OracleLimits()


@dataclass(frozen=True)
class RootCertificate:
    """Exact replay data; ``dataclasses.asdict`` is directly JSON encodable.

    Every rational is an integer ``(numerator, denominator)`` pair. The chain
    belongs to ``interior_polynomial``, obtained by removing each endpoint root
    once from the squarefree representative. Endpoint values retain the original
    polynomial's sign. Root counts intentionally exclude endpoint roots.
    """

    original: EncodedPolynomial
    squarefree: EncodedPolynomial
    interior_polynomial: EncodedPolynomial
    chain: tuple[EncodedPolynomial, ...]
    endpoint_values: tuple[EncodedRational, EncodedRational]
    endpoint_roots: tuple[bool, bool]
    variations_left: int
    variations_right: int
    interior_roots: int
    operation_count: int
    max_coefficient_bits: int


@dataclass
class _Budget:
    limits: OracleLimits
    operations: int = 0
    coefficient_bits: int = 0

    def value(self, value: Fraction, *, operation: bool = False) -> Fraction:
        if operation:
            self.operations += 1
            if self.operations > self.limits.max_operations:
                raise OracleLimitError("oracle Fraction-operation budget exceeded")
        bits = max(abs(value.numerator).bit_length(), value.denominator.bit_length())
        self.coefficient_bits = max(self.coefficient_bits, bits)
        if bits > self.limits.max_coefficient_bits:
            raise OracleLimitError("oracle coefficient-bit budget exceeded")
        return value

    def polynomial(self, coefficients: Polynomial) -> Polynomial:
        if len(coefficients) - 1 > self.limits.max_degree:
            raise OracleLimitError("oracle polynomial-degree budget exceeded")
        for coefficient in coefficients:
            self.value(coefficient)
        return coefficients


def _trim(coefficients: Sequence[Fraction]) -> Polynomial:
    last = len(coefficients)
    while last and coefficients[last - 1] == 0:
        last -= 1
    return tuple(coefficients[:last]) if last else ZERO


def _input(coefficients: Sequence[Exact], budget: _Budget) -> Polynomial:
    if not isinstance(coefficients, (tuple, list)):
        raise ValueError("coefficients must be a finite tuple or list")
    if any(
        type(value) is not int and not isinstance(value, Fraction)
        for value in coefficients
    ):
        raise ValueError(
            "coefficients must be exact integers or Fractions, never floats/bools"
        )
    # Check every supplied coefficient, including trailing zero slots.
    values = tuple(budget.value(Fraction(value)) for value in coefficients)
    return budget.polynomial(_trim(values))


def _point(value: Fraction, budget: _Budget) -> Fraction:
    if not isinstance(value, Fraction):
        raise ValueError(
            "interval endpoints and evaluation points must be explicit Fractions"
        )
    return budget.value(value)


def _new_budget(limits: OracleLimits) -> _Budget:
    if not isinstance(limits, OracleLimits):
        raise ValueError("limits must be an OracleLimits instance")
    return _Budget(limits)


def _evaluate(coefficients: Polynomial, value: Fraction, budget: _Budget) -> Fraction:
    answer = Fraction(0)
    for coefficient in reversed(coefficients):
        answer = budget.value(answer * value, operation=True)
        answer = budget.value(answer + coefficient, operation=True)
    return answer


def _add(left: Polynomial, right: Polynomial, budget: _Budget) -> Polynomial:
    result = []
    for i in range(max(len(left), len(right))):
        a = left[i] if i < len(left) else Fraction(0)
        b = right[i] if i < len(right) else Fraction(0)
        result.append(budget.value(a + b, operation=True))
    return budget.polynomial(_trim(result))


def _multiply(left: Polynomial, right: Polynomial, budget: _Budget) -> Polynomial:
    if left == ZERO or right == ZERO:
        return ZERO
    if len(left) + len(right) - 2 > budget.limits.max_degree:
        raise OracleLimitError("oracle polynomial-degree budget exceeded")
    result = [Fraction(0)] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            product = budget.value(a * b, operation=True)
            result[i + j] = budget.value(result[i + j] + product, operation=True)
    return budget.polynomial(_trim(result))


def _derivative(coefficients: Polynomial, budget: _Budget) -> Polynomial:
    return budget.polynomial(
        _trim(
            [
                budget.value(i * value, operation=True)
                for i, value in enumerate(coefficients)
                if i
            ]
        )
    )


def _divide(
    dividend: Polynomial, divisor: Polynomial, budget: _Budget
) -> tuple[Polynomial, Polynomial]:
    if divisor == ZERO:
        raise ValueError("division by the zero polynomial")
    remainder = list(dividend)
    quotient = [Fraction(0)] * max(1, len(dividend) - len(divisor) + 1)
    while tuple(remainder) != ZERO and len(remainder) >= len(divisor):
        offset = len(remainder) - len(divisor)
        factor = budget.value(remainder[-1] / divisor[-1], operation=True)
        quotient[offset] = budget.value(quotient[offset] + factor, operation=True)
        for i, coefficient in enumerate(divisor):
            product = budget.value(factor * coefficient, operation=True)
            remainder[offset + i] = budget.value(
                remainder[offset + i] - product, operation=True
            )
        remainder = list(_trim(remainder))
    return budget.polynomial(_trim(quotient)), budget.polynomial(_trim(remainder))


def _monic(coefficients: Polynomial, budget: _Budget) -> Polynomial:
    if coefficients == ZERO:
        return ZERO
    return budget.polynomial(
        tuple(
            budget.value(value / coefficients[-1], operation=True)
            for value in coefficients
        )
    )


def _squarefree(coefficients: Polynomial, budget: _Budget) -> Polynomial:
    if coefficients == ZERO:
        raise ValueError("the zero polynomial has infinitely many roots")
    if len(coefficients) == 1:
        return ONE
    a, b = coefficients, _derivative(coefficients, budget)
    while b != ZERO:
        _, remainder = _divide(a, b, budget)
        a, b = b, remainder
    quotient, remainder = _divide(coefficients, _monic(a, budget), budget)
    if remainder != ZERO:
        raise ArithmeticError("exact polynomial gcd did not divide the input")
    return _monic(quotient, budget)


def _chain(coefficients: Polynomial, budget: _Budget) -> tuple[Polynomial, ...]:
    if coefficients == ZERO:
        raise ValueError("the zero polynomial has infinitely many roots")
    if len(coefficients) == 1:
        return (coefficients,)
    chain = [coefficients, _derivative(coefficients, budget)]
    while True:
        _, remainder = _divide(chain[-2], chain[-1], budget)
        if remainder == ZERO:
            return tuple(chain)
        # The minus sign is essential. No negative or monic rescaling follows.
        chain.append(tuple(-value for value in remainder))


def _variations(chain: tuple[Polynomial, ...], point: Fraction, budget: _Budget) -> int:
    signs = []
    for polynomial in chain:
        value = _evaluate(polynomial, point, budget)
        if value:
            signs.append(1 if value > 0 else -1)
    return sum(a != b for a, b in zip(signs, signs[1:]))


def _encode(coefficients: Polynomial) -> EncodedPolynomial:
    return tuple((value.numerator, value.denominator) for value in coefficients)


def trim(
    coefficients: Sequence[Exact], *, limits: OracleLimits = DEFAULT_LIMITS
) -> Polynomial:
    """Validate exact input and remove trailing zero coefficients."""
    return _input(coefficients, _new_budget(limits))


def add(
    left: Sequence[Exact],
    right: Sequence[Exact],
    *,
    limits: OracleLimits = DEFAULT_LIMITS,
) -> Polynomial:
    budget = _new_budget(limits)
    return _add(_input(left, budget), _input(right, budget), budget)


def multiply(
    left: Sequence[Exact],
    right: Sequence[Exact],
    *,
    limits: OracleLimits = DEFAULT_LIMITS,
) -> Polynomial:
    budget = _new_budget(limits)
    return _multiply(_input(left, budget), _input(right, budget), budget)


def derivative(
    coefficients: Sequence[Exact], *, limits: OracleLimits = DEFAULT_LIMITS
) -> Polynomial:
    budget = _new_budget(limits)
    return _derivative(_input(coefficients, budget), budget)


def divide(
    dividend: Sequence[Exact],
    divisor: Sequence[Exact],
    *,
    limits: OracleLimits = DEFAULT_LIMITS,
) -> tuple[Polynomial, Polynomial]:
    budget = _new_budget(limits)
    return _divide(_input(dividend, budget), _input(divisor, budget), budget)


def evaluate(
    coefficients: Sequence[Exact],
    value: Fraction,
    *,
    limits: OracleLimits = DEFAULT_LIMITS,
) -> Fraction:
    budget = _new_budget(limits)
    return _evaluate(_input(coefficients, budget), _point(value, budget), budget)


def squarefree(
    coefficients: Sequence[Exact], *, limits: OracleLimits = DEFAULT_LIMITS
) -> Polynomial:
    """Return a monic representative with the same distinct roots, not sign."""
    budget = _new_budget(limits)
    return _squarefree(_input(coefficients, budget), budget)


def sturm_chain(
    coefficients: Sequence[Exact], *, limits: OracleLimits = DEFAULT_LIMITS
) -> tuple[Polynomial, ...]:
    """Return the signed Euclidean Sturm chain of a monic squarefree input."""
    budget = _new_budget(limits)
    return _chain(_squarefree(_input(coefficients, budget), budget), budget)


def root_certificate(
    coefficients: Sequence[Exact],
    left: Fraction = Fraction(0),
    right: Fraction = Fraction(1),
    *,
    limits: OracleLimits = DEFAULT_LIMITS,
) -> RootCertificate:
    """Construct exact distinct-root evidence, owning endpoints separately."""
    budget = _new_budget(limits)
    original = _input(coefficients, budget)
    left, right = _point(left, budget), _point(right, budget)
    if left >= right:
        raise ValueError("root interval must have left < right")
    if original == ZERO:
        raise ValueError("the zero polynomial has infinitely many roots")
    values = (_evaluate(original, left, budget), _evaluate(original, right, budget))
    endpoints = (values[0] == 0, values[1] == 0)
    representative = _squarefree(original, budget)
    interior = representative
    for point, is_root in zip((left, right), endpoints):
        if is_root:
            interior, remainder = _divide(interior, (-point, Fraction(1)), budget)
            if remainder != ZERO:
                raise ArithmeticError("endpoint root failed exact linear deflation")
    chain = _chain(interior, budget)
    variation_left = _variations(chain, left, budget)
    variation_right = _variations(chain, right, budget)
    count = variation_left - variation_right
    if not 0 <= count <= len(interior) - 1:
        raise ArithmeticError("invalid distinct-root count")
    return RootCertificate(
        original=_encode(original),
        squarefree=_encode(representative),
        interior_polynomial=_encode(interior),
        chain=tuple(_encode(polynomial) for polynomial in chain),
        endpoint_values=(
            (values[0].numerator, values[0].denominator),
            (values[1].numerator, values[1].denominator),
        ),
        endpoint_roots=endpoints,
        variations_left=variation_left,
        variations_right=variation_right,
        interior_roots=count,
        operation_count=budget.operations,
        max_coefficient_bits=budget.coefficient_bits,
    )


def count_roots(
    coefficients: Sequence[Exact],
    left: Fraction = Fraction(0),
    right: Fraction = Fraction(1),
    *,
    closed: bool = False,
    limits: OracleLimits = DEFAULT_LIMITS,
) -> int:
    """Count distinct roots on (left,right), or [left,right] when closed."""
    if type(closed) is not bool:
        raise ValueError("closed must be a bool")
    certificate = root_certificate(coefficients, left, right, limits=limits)
    return certificate.interior_roots + (
        sum(certificate.endpoint_roots) if closed else 0
    )


def threshold_decision(
    coefficients: Sequence[Exact], *, limits: OracleLimits = DEFAULT_LIMITS
) -> bool:
    """Decide exactly whether some real q in [0,1] has original H(q)>=0.

    If neither endpoint is nonnegative, continuity makes acceptance equivalent
    to an interior zero. Thus even roots and equality tangencies accept without
    a rational maximiser or any optimisation. The zero polynomial accepts.
    """
    budget = _new_budget(limits)
    original = _input(coefficients, budget)
    if original == ZERO:
        return True
    left = _evaluate(original, Fraction(0), budget)
    right = _evaluate(original, Fraction(1), budget)
    if left >= 0 or right >= 0:
        return True
    if len(original) == 1:
        return False
    # Account for endpoint work when passing the remaining operation budget.
    remaining = OracleLimits(
        max_degree=limits.max_degree,
        max_coefficient_bits=limits.max_coefficient_bits,
        max_operations=limits.max_operations - budget.operations,
    )
    return root_certificate(original, limits=remaining).interior_roots > 0
