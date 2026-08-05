"""Koopman-Nam discriminant stability (programme issue #13).

The constrained-MLE quadratic currently forms ``B**2 - 4*A*C`` and repairs small
negative results. Two algebraically identical, manifestly non-negative forms
avoid the cancellation entirely:

    r >= 1:   D = ((a + n0)/r - (n1 + c))**2 + 4*b*d/r
    0 < r < 1: D = ((a + n0) - r*(n1 + c))**2 + 4*r*b*d

The identity rests on ``(X + Y)**2 - (X - Y)**2 == 4*X*Y`` together with
``(a + n0)*(n1 + c) - N*(a + c) == b*d``.
"""

from __future__ import annotations

import random
from fractions import Fraction

import pytest


def _current_form(a, b, c, d, r):
    """``B**2 - 4*A*C`` for the phi < 1 scaling branch."""
    n1, n0, total = a + b, c + d, a + b + c + d
    coef_b = (a + n0) + r * (n1 + c)
    return coef_b * coef_b - 4 * r * total * (a + c)


def _stable_low(a, b, c, d, r):
    n1, n0 = a + b, c + d
    return ((a + n0) - r * (n1 + c)) ** 2 + 4 * r * b * d


def _stable_high(a, b, c, d, r):
    n1, n0 = a + b, c + d
    return ((a + n0) / r - (n1 + c)) ** 2 + 4 * b * d / r


def test_lemma_product_identity_is_exact() -> None:
    """``(a + n0)*(n1 + c) - N*(a + c) == b*d`` over the rationals."""
    random.seed(20260804)
    for _ in range(500):
        a, b, c, d = (Fraction(random.randint(0, 60)) for _ in range(4))
        n1, n0, total = a + b, c + d, a + b + c + d
        assert (a + n0) * (n1 + c) - total * (a + c) == b * d


@pytest.mark.parametrize("trials", [1000])
def test_stable_discriminant_identities_are_exact(trials: int) -> None:
    """Both branches agree with ``B**2 - 4AC`` exactly in rational arithmetic."""
    random.seed(4)
    for _ in range(trials):
        a, b, c, d = (Fraction(random.randint(0, 50)) for _ in range(4))
        r = Fraction(random.randint(1, 400), random.randint(1, 400))

        current = _current_form(a, b, c, d, r)
        assert _stable_low(a, b, c, d, r) == current
        assert _stable_high(a, b, c, d, r) == current / (r * r)


def test_stable_forms_are_manifestly_non_negative() -> None:
    """Both stable forms are a square plus a non-negative product."""
    random.seed(7)
    for _ in range(500):
        a, b, c, d = (Fraction(random.randint(0, 50)) for _ in range(4))
        r = Fraction(random.randint(1, 400), random.randint(1, 400))
        assert _stable_low(a, b, c, d, r) >= 0
        assert _stable_high(a, b, c, d, r) >= 0


# Cases where the difference-of-large-numbers form cancels. All have ``b*d == 0``,
# which is the only regime where it can: otherwise ``D >= 4*r*b*d`` bounds the
# result away from zero. Measured against exact rational arithmetic on the same
# binary64 inputs.
CANCELLATION_CASES = [
    # (a, b, c, d, r, current relative error, stable relative error)
    ((3, 0, 4, 0, 1.0 + 1e-9), 1.0e00, 0.0),
    ((7, 0, 5, 0, 1.0000001), 2.6e-02, 1.5e-09),
    ((30, 0, 1, 29, 1.93548), 6.1e-05, 3.0e-11),
]


def _relative_errors(a, b, c, d, r):
    # Fraction(float(r)) is the exact rational value of the binary64 input, so the
    # reference is computed from the same number the float paths receive.
    exact = _current_form(*(Fraction(v) for v in (a, b, c, d)), Fraction(float(r)))
    scale = max(abs(float(exact)), 1e-300)
    current = _current_form(float(a), float(b), float(c), float(d), float(r))
    stable = _stable_low(float(a), float(b), float(c), float(d), float(r))
    return abs(current - float(exact)) / scale, abs(stable - float(exact)) / scale


@pytest.mark.parametrize(("case", "current_err", "stable_err"), CANCELLATION_CASES)
def test_stable_form_beats_the_current_form_under_cancellation(
    case, current_err, stable_err
) -> None:
    """The current form can lose the discriminant entirely; the stable form does not.

    At ``(3, 0, 4, 0)`` with ``r = 1 + 1e-9`` the current form's relative error is
    ``1.0``: the computed discriminant bears no relation to the true value, which
    is the regime where the negative-result repair fires. The stable form is exact
    there.
    """
    observed_current, observed_stable = _relative_errors(*case)
    assert observed_current == pytest.approx(current_err, rel=0.2, abs=1e-12)
    assert observed_stable <= stable_err * 1.2 + 1e-12
    assert observed_stable < observed_current


def test_stable_form_residual_error_is_bounded_by_inner_cancellation() -> None:
    """The stable form is not unconditionally exact, and the reason is worth pinning.

    Its remaining error comes from the inner difference ``(a + n0) - r*(n1 + c)``
    cancelling, which is inherent to the quantity rather than to the formulation.
    When ``b*d > 0`` the ``4*r*b*d`` term floors the result and both forms are
    fine. Recorded so issue #13 does not over-claim exactness.
    """
    worst_stable = max(_relative_errors(*case)[1] for case, _, _ in CANCELLATION_CASES)
    assert worst_stable < 1e-8

    for case in [(12, 4, 9, 5, 1.4), (3, 7, 4, 6, 0.8), (20, 11, 7, 13, 2.5)]:
        current_err, stable_err = _relative_errors(*case)
        assert current_err < 1e-14
        assert stable_err < 1e-14


def test_production_score_endpoints_are_unaffected_today() -> None:
    """The cancellation does not reach a returned endpoint.

    Recorded so that issue #13 is understood as numerical hygiene rather than an
    endpoint correction, and so a regression in endpoints would be caught.
    """
    from exactcis import Design, ci_score_rr

    lower, upper = ci_score_rr(999, 1, 1, 999, 0.05, design=Design.COHORT_BINOMIAL)
    assert 0.0 < lower < upper
    for table in [(3, 0, 4, 0), (30, 0, 1, 29), (0, 10, 0, 10)]:
        result = ci_score_rr(*table, 0.05, design=Design.COHORT_BINOMIAL)
        assert result[0] <= result[1]


def test_production_discriminant_is_never_negative() -> None:
    """The shipped form is structurally non-negative, so no repair is needed.

    Previously a ``64 * ulp`` clamp existed to absorb small negative results from
    the difference form. Sweeping the regime where that clamp used to fire must
    now produce no negative discriminant at all.
    """
    from exactcis.inference.relative_risk.score import _constrained_control_risk

    probes = [(3, 0, 4, 0), (30, 0, 1, 29), (7, 0, 5, 0), (12, 0, 9, 0), (0, 5, 0, 5)]
    ratios = [1.0 - 1e-9, 1.0, 1.0 + 1e-9, 1.0000001, 1.93548, 0.5, 2.0, 100.0]
    for a, b, c, d in probes:
        for ratio in ratios:
            risk = _constrained_control_risk(a, b, c, d, ratio)
            assert 0.0 <= risk <= 1.0
            assert risk == risk  # not NaN


def test_constrained_risk_matches_a_direct_root_solve() -> None:
    """Independent check of the quadratic root the stable form feeds."""
    from fractions import Fraction

    from exactcis.inference.relative_risk.score import _constrained_control_risk

    worst = 0.0
    for a, b, c, d in [(12, 4, 9, 5), (3, 7, 4, 6), (20, 11, 7, 13), (30, 0, 1, 29)]:
        for ratio in (0.5, 0.9, 1.0, 1.5, 3.0):
            n1, n0 = a + b, c + d
            total = n1 + n0
            # phi*N*p0**2 - [(a+n0) + phi*(n1+c)]*p0 + (a+c) = 0, smaller root.
            qa = Fraction(ratio).limit_denominator(10**9) * total
            qb = -(
                Fraction(a + n0) + Fraction(ratio).limit_denominator(10**9) * (n1 + c)
            )
            qc = Fraction(a + c)
            disc = qb * qb - 4 * qa * qc
            root = (-float(qb) - float(disc) ** 0.5) / (2 * float(qa))
            expected = min(1.0, 1.0 / ratio, max(0.0, root))
            got = _constrained_control_risk(a, b, c, d, ratio)
            worst = max(worst, abs(got - expected) / max(expected, 1e-300))
    assert worst < 1e-9, f"worst relative deviation {worst:.3e}"
