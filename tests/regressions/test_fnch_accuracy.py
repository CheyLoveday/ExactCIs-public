"""High-precision agreement for FNCH quantities (programme issues #11, #18, #19).

These are the accuracy envelopes the replacement kernel must not widen. They are
written against independently derived ``mpmath`` values at 60 digits, not against
recorded outputs of the implementation under test.
"""

from __future__ import annotations

import math

import pytest

from exactcis import exact_ci_conditional, exact_ci_midp
from exactcis._numerics import fnch_probabilities

from . import _oracles
from ._evidence import CASE_CONTROL

pytestmark = pytest.mark.skipif(
    not _oracles.HAVE_MPMATH,
    reason="mpmath (validation extra) is required for oracle comparison",
)

# Envelope for the probability vector, chosen from measured 1.0.0 behaviour with
# headroom. The replacement kernel is expected to improve on this, never widen it.
PROBABILITY_ENVELOPE = 1e-12
ENDPOINT_ENVELOPE = 5e-11

MARGIN_CASES = [(60, 60, 60), (200, 150, 180), (500, 500, 400)]
LOG_ODDS_CASES = [-2.0, -0.5, 0.0, 0.7, 2.0]


@pytest.mark.parametrize(("n1", "n0", "events"), MARGIN_CASES)
@pytest.mark.parametrize("log_odds", LOG_ODDS_CASES)
def test_probability_vector_matches_high_precision_oracle(
    n1, n0, events, log_odds
) -> None:
    points, probabilities = fnch_probabilities(n1, n0, events, log_odds)
    ref_points, ref_probabilities = _oracles.fnch_probabilities(
        n1, n0, events, log_odds
    )
    assert list(points) == ref_points

    worst = 0.0
    for got, ref in zip(probabilities, ref_probabilities):
        if float(ref) <= 1e-14:
            continue
        worst = max(worst, _oracles.relative_error(got, ref))
    assert worst <= PROBABILITY_ENVELOPE, (
        f"worst relative probability error {worst:.3e}"
    )


@pytest.mark.parametrize(("n1", "n0", "events"), MARGIN_CASES)
@pytest.mark.parametrize("log_odds", LOG_ODDS_CASES)
def test_conditional_moments_match_high_precision_oracle(
    n1, n0, events, log_odds
) -> None:
    points, probabilities = fnch_probabilities(n1, n0, events, log_odds)
    mean = math.fsum(k * p for k, p in zip(points, probabilities))
    variance = math.fsum((k - mean) ** 2 * p for k, p in zip(points, probabilities))

    ref_mean, ref_variance = _oracles.moments(n1, n0, events, log_odds)
    assert _oracles.relative_error(mean, ref_mean) <= PROBABILITY_ENVELOPE
    assert _oracles.relative_error(variance, ref_variance) <= 1e-10


def test_moment_derivative_identity_holds_numerically() -> None:
    """``dE[X]/deta == Var(X)``, the identity safeguarded Newton rests on (#19)."""
    step = 1e-5
    worst = 0.0
    for n1, n0, events in [(35, 12, 36), (100, 80, 90), (500, 500, 400)]:
        for eta in (-1.5, 0.0, 0.7, 2.0):

            def mean_at(value: float) -> float:
                points, probabilities = fnch_probabilities(n1, n0, events, value)
                return math.fsum(k * p for k, p in zip(points, probabilities))

            derivative = (mean_at(eta + step) - mean_at(eta - step)) / (2 * step)
            points, probabilities = fnch_probabilities(n1, n0, events, eta)
            mean = math.fsum(k * p for k, p in zip(points, probabilities))
            variance = math.fsum(
                (k - mean) ** 2 * p for k, p in zip(points, probabilities)
            )
            worst = max(worst, abs(derivative - variance) / max(variance, 1e-300))
    assert worst < 1e-7, f"worst relative deviation {worst:.3e}"


@pytest.mark.parametrize(
    "table",
    [(5, 2, 5, 8), (12, 5, 8, 10), (1, 9, 11, 3), (30, 20, 15, 35)],
)
def test_conditional_endpoints_match_high_precision_oracle(table) -> None:
    lower, upper = exact_ci_conditional(*table, 0.05, design=CASE_CONTROL)
    ref_lower, ref_upper = _oracles.conditional_interval(*table, alpha=0.05)
    assert _oracles.relative_error(lower, ref_lower) <= ENDPOINT_ENVELOPE
    assert _oracles.relative_error(upper, ref_upper) <= ENDPOINT_ENVELOPE


def test_midp_is_strictly_inside_the_conditional_interval() -> None:
    for table in [(5, 2, 5, 8), (12, 5, 8, 10), (30, 20, 15, 35)]:
        cond = exact_ci_conditional(*table, 0.05, design=CASE_CONTROL)
        midp = exact_ci_midp(*table, 0.05, design=CASE_CONTROL)
        assert cond[0] <= midp[0]
        assert midp[1] <= cond[1]
