"""Exact polynomial adversaries and U0 anchors for the bounded U1 oracle.

These finite checks are independent of production implementation and do not
certify global inversion, Lean correspondence, or the production root checker.
"""

import json
from dataclasses import asdict
from fractions import Fraction as F
from math import comb

import pytest

from ._oracle import comparison_polynomial, rejection_mask, threshold_coefficients
from ._polynomial import (
    OracleLimitError,
    OracleLimits,
    add,
    count_roots,
    derivative,
    divide,
    evaluate,
    multiply,
    root_certificate,
    squarefree,
    sturm_chain,
    threshold_decision,
    trim,
)


def _factor(root: F, multiplicity: int) -> tuple[F, ...]:
    """Binomial-theorem coefficients with a known root and multiplicity."""
    return tuple(
        F(comb(multiplicity, k)) * (-root) ** (multiplicity - k)
        for k in range(multiplicity + 1)
    )


def _decode(encoded):
    return tuple(F(numerator, denominator) for numerator, denominator in encoded)


def test_exact_polynomial_arithmetic_and_degree_drops():
    p = (F(1, 3), F(-2), F(3, 2))
    q = (F(-4, 5), F(7, 3))
    product = multiply(p, q)
    assert product == (F(-4, 15), F(107, 45), F(-88, 15), F(7, 2))
    assert add(p, tuple(-x for x in p)) == (F(0),)
    assert derivative(p) == (F(-2), F(3))
    assert divide(product, p) == (q, (F(0),))
    assert divide((1, 0, 1), (1, 1)) == ((F(-1), F(1)), (F(2),))
    assert trim((0, 1, 0, 0, 0)) == (F(0), F(1))
    assert trim(()) == (F(0),)
    assert derivative((7,)) == (F(0),)
    for point in (F(-2), F(0), F(2, 5), F(3)):
        assert evaluate(product, point) == evaluate(p, point) * evaluate(q, point)
    assert count_roots((-1, 2, 0, 0, 0)) == 1
    assert threshold_decision((-1, 0, 0, 0)) is False


@pytest.mark.parametrize("multiplicity", (1, 2, 3, 4, 7, 12))
@pytest.mark.parametrize("scale", (F(-3), F(5)))
def test_distinct_roots_survive_odd_even_and_high_multiplicity(multiplicity, scale):
    root = F(2, 5)
    polynomial = tuple(
        scale * coefficient for coefficient in _factor(root, multiplicity)
    )
    assert squarefree(polynomial) == (-root, F(1))
    assert count_roots(polynomial) == 1
    assert count_roots(polynomial, F(0), root) == 0
    assert count_roots(polynomial, root, F(1)) == 0
    assert count_roots(polynomial, F(0), root, closed=True) == 1
    assert evaluate(polynomial, root) == 0
    assert threshold_decision(polynomial) is True


def test_squarefree_normalisation_preserves_roots_but_can_reverse_sign():
    polynomial = (-1, -2, -1)  # -(q+1)^2 is strictly negative on [0,1].
    representative = squarefree(polynomial)
    assert representative == (F(1), F(1))
    assert count_roots(polynomial, F(-2), F(0)) == 1
    assert count_roots(representative, F(-2), F(0)) == 1
    assert count_roots(polynomial) == count_roots(representative) == 0
    assert evaluate(polynomial, F(1, 2)) < 0 < evaluate(representative, F(1, 2))
    assert threshold_decision(polynomial) is False
    assert threshold_decision(representative) is True


def test_endpoint_roots_are_deflated_and_owned_separately():
    endpoints = multiply(_factor(F(0), 3), _factor(F(1), 4))
    polynomial = multiply(endpoints, _factor(F(2, 5), 2))
    assert count_roots(endpoints) == 0
    assert count_roots(endpoints, closed=True) == 2
    assert count_roots(polynomial) == 1
    assert count_roots(polynomial, closed=True) == 3
    certificate = root_certificate(polynomial)
    assert certificate.endpoint_roots == (True, True)
    assert _decode(certificate.endpoint_values) == (0, 0)
    assert _decode(certificate.interior_polynomial) == (-F(2, 5), F(1))
    assert certificate.interior_roots == 1
    assert certificate.variations_left - certificate.variations_right == 1
    assert threshold_decision(tuple(-x for x in endpoints)) is True
    assert json.loads(json.dumps(asdict(certificate)))["interior_roots"] == 1


@pytest.mark.parametrize("constant,expected", ((-7, False), (0, True), (5, True)))
def test_zero_and_constant_threshold_branches(constant, expected):
    assert threshold_decision((constant,)) is expected
    assert threshold_decision((constant, 0, 0)) is expected
    if constant == 0:
        for operation in (count_roots, root_certificate, squarefree, sturm_chain):
            with pytest.raises(ValueError, match="infinitely many roots"):
                operation((0,))
    else:
        assert count_roots((constant,)) == 0
        assert count_roots((constant,), closed=True) == 0


def test_signed_sturm_remainders_are_not_made_monic():
    # q^2+1 has no real root. Monic rescaling of the final -1 changes its count.
    chain = sturm_chain((1, 0, 1))
    assert chain == ((F(1), F(0), F(1)), (F(0), F(2)), (F(-1),))
    assert count_roots((1, 0, 1), F(-5), F(5)) == 0
    assert threshold_decision((-1, 0, -1)) is False


def test_nondyadic_equality_tangency_uses_the_original_threshold():
    mask = rejection_mask(2, 3, (2, 0), F(1), "greater")
    assert mask == ((2, 0),)
    polynomial = threshold_coefficients(2, 3, mask, F(1), F(108, 3125))
    assert polynomial == (-F(108, 3125), F(0), F(1), F(-3), F(3), F(-1))
    assert evaluate(polynomial, F(2, 5)) == 0
    assert evaluate(polynomial, F(0)) < 0
    assert evaluate(polynomial, F(1)) < 0
    # A'(q)=q(1-q)^2(2-5q), so its sole interior maximum is q=2/5.
    assert derivative(polynomial) == (F(0), F(2), F(-9), F(12), F(-5))
    assert multiply((0, 1), multiply((1, -2, 1), (2, -5))) == derivative(polynomial)
    quotient, remainder = divide(polynomial, _factor(F(2, 5), 2))
    assert quotient == (-F(27, 125), -F(27, 25), F(11, 5), F(-1))
    assert remainder == (F(0),)
    assert evaluate(quotient, F(2, 5)) != 0  # Multiplicity is exactly two.
    assert count_roots(polynomial) == 1
    assert threshold_decision(polynomial) is True


@pytest.mark.parametrize(
    "psi,roots,accepted",
    ((F(23, 9), 4, True), (F(47, 17), 0, False), (F(3), 2, True), (F(25, 7), 0, False)),
)
def test_disconnected_acceptance_anchor(psi, roots, accepted):
    mask = rejection_mask(4, 4, (0, 2), psi, "less")
    polynomial = threshold_coefficients(4, 4, mask, psi, F(1, 40))
    assert evaluate(polynomial, F(0)) == -F(1, 40)
    assert evaluate(polynomial, F(1)) == -(psi**4) / 40
    assert count_roots(polynomial) == roots
    assert threshold_decision(polynomial) is accepted


def test_signed_ordering_breakpoint_and_unique_positive_root():
    comparison = comparison_polynomial(4, 4, (0, 2), (1, 3), "less")
    assert comparison == (F(0), F(16), F(46), F(0), F(-6))
    cubic = (F(-8), F(-23), F(0), F(3))
    assert multiply((0, -2), cubic) == comparison
    left, right = F(29, 10), F(59, 20)
    assert evaluate(cubic, left) == -F(1533, 1000)
    assert evaluate(cubic, right) == F(9337, 8000)
    assert evaluate(comparison, left) > 0 > evaluate(comparison, right)
    assert count_roots(comparison, left, right) == 1
    # Cauchy's 1+max(|a_i/a_n|) bound is below 9 for the cubic.
    assert 1 + max(abs(cubic[i] / cubic[-1]) for i in range(3)) < 9
    assert count_roots(comparison, F(0), F(9)) == 1
    assert (1, 3) not in rejection_mask(4, 4, (0, 2), left, "less")
    assert (1, 3) in rejection_mask(4, 4, (0, 2), right, "less")


def test_multiple_maxima_stationary_root_cells_and_endpoint_ownership():
    psi = F(1, 4)
    mask = rejection_mask(2, 4, (1, 0), psi, "greater")
    numerator = trim(threshold_coefficients(2, 4, mask, psi, F(0)))
    denominator = (F(1), -F(3, 2), F(9, 16))
    stationary = add(
        multiply(derivative(numerator), denominator),
        tuple(-x for x in multiply(numerator, derivative(denominator))),
    )
    assert stationary == (
        F(1, 2),
        -F(39, 8),
        F(147, 8),
        F(-35),
        F(585, 16),
        F(-21),
        F(393, 64),
        -F(45, 64),
    )
    assert count_roots(stationary) == 3
    assert count_roots(stationary, closed=True) == 4
    assert root_certificate(stationary).endpoint_roots == (False, True)
    for left, right, sign in (
        (F(27, 100), F(28, 100), 1),
        (F(48, 100), F(49, 100), -1),
        (F(69, 100), F(70, 100), 1),
    ):
        assert count_roots(stationary, left, right) == 1
        assert evaluate(stationary, left) * sign > 0
        assert evaluate(stationary, right) * sign < 0


@pytest.mark.parametrize(
    "coefficients,limits,message",
    (
        ((1, 0, 1), OracleLimits(max_degree=1), "degree"),
        ((-1, 1 << 20), OracleLimits(max_coefficient_bits=10), "coefficient-bit"),
        ((-1, 2), OracleLimits(max_operations=0), "operation"),
    ),
)
def test_scoped_budget_exhaustion_refuses_without_an_answer(
    coefficients, limits, message
):
    for operation in (count_roots, root_certificate, threshold_decision):
        with pytest.raises(OracleLimitError, match=message):
            operation(coefficients, limits=limits)


@pytest.mark.parametrize("coefficients", ((0.1, 1), (True, 1), (F(1), False)))
def test_binary_floats_and_booleans_cannot_enter_exact_polynomial_arithmetic(
    coefficients,
):
    with pytest.raises(ValueError, match="exact integers or Fractions"):
        threshold_decision(coefficients)


def test_invalid_root_intervals_and_zero_divisor_refuse():
    with pytest.raises(ValueError, match="explicit Fractions"):
        count_roots((-1, 2), 0, F(1))
    with pytest.raises(ValueError, match="left < right"):
        count_roots((-1, 2), F(1), F(1))
    with pytest.raises(ValueError, match="zero polynomial"):
        divide((1,), (0,))
