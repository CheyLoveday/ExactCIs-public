"""Safeguarded Newton for the conditional-MLE mean inversion (issue #19).

Scope per the programme: the conditional mean inversion only. Equal-tail and
ordered-endpoint acceleration are explicitly out of scope. The bracket
certificate remains authoritative; Newton only changes how fast the bracket
shrinks.
"""

from __future__ import annotations

import math
import random

import pytest

import exactcis._numerics as numerics
from exactcis import compute_or_with_policy
from exactcis._numerics import (
    _ROOT_TOL,
    conditional_mle,
    prepare_margins,
    solve_monotone_log_parameter,
)

from ._evidence import CASE_CONTROL, count_work


def _bisection_reference(n1: int, n0: int, events: int, target: float) -> float:
    """The pre-Newton solver, run on the same kernel, as the agreement oracle."""
    margins = prepare_margins(n1, n0, events)
    return solve_monotone_log_parameter(
        margins.mean, target, increasing=True, method="reference", side="point"
    )


def test_agrees_with_bisection_within_the_shared_certificate() -> None:
    """Both solvers certify the same bracket-width contract on the same root."""
    rng = random.Random(19)
    checked = 0
    for _ in range(120):
        a = rng.randint(0, 40)
        b = rng.randint(0, 40)
        c = rng.randint(0, 40)
        d = rng.randint(0, 40)
        n1, n0, events = a + b, c + d, a + c
        lower, upper = (max(0, events - n0), min(events, n1))
        if lower >= upper or a in (lower, upper):
            continue
        point = conditional_mle(a, b, c, d)
        reference = math.exp(_bisection_reference(n1, n0, events, float(a)))
        tolerance = 4.0 * _ROOT_TOL * max(1.0, abs(math.log(max(point, 1e-300))))
        assert math.log(point) == pytest.approx(math.log(reference), abs=tolerance)
        checked += 1
    assert checked > 60


def test_boundary_and_singleton_behaviour_is_unchanged() -> None:
    assert conditional_mle(0, 5, 3, 7) == 0.0
    assert math.isinf(conditional_mle(5, 0, 7, 3))
    assert math.isnan(conditional_mle(0, 0, 0, 1000))


def test_newton_reduces_distribution_evaluations_severalfold() -> None:
    """The point of the change: materially fewer FNCH traversals.

    Pure bisection needs about 45 evaluations to close the bracket; safeguarded
    Newton with the variance from the same traversal needs a bounded handful.
    """
    with count_work() as counter:
        conditional_mle(200, 200, 160, 240)
    newton_evals = counter.fnch_calls
    assert newton_evals <= 20, newton_evals

    margins = prepare_margins(400, 440, 360)
    with count_work() as counter:
        solve_monotone_log_parameter(
            margins.mean, 180.0, increasing=True, method="reference", side="point"
        )
    bisection_evals = counter.fnch_calls
    assert bisection_evals >= 40, bisection_evals
    assert newton_evals * 2 < bisection_evals


def test_bracket_certificate_is_still_enforced(monkeypatch) -> None:
    """Termination is by bracket width; a stalled bracket still fails closed."""
    from exactcis.exceptions import NumericalError

    def stuck_moments(self, log_odds: float) -> tuple[float, float]:
        return (10.0, float("nan"))

    monkeypatch.setattr(numerics.PreparedMargins, "moments", stuck_moments)
    margins = prepare_margins(40, 30, 25)
    with pytest.raises(NumericalError):
        numerics._solve_mean_newton(margins, 12.0, method="probe")


def test_policy_route_still_returns_certified_results() -> None:
    result = compute_or_with_policy(1400, 1400, 1120, 1680, design=CASE_CONTROL)
    assert result.lower <= result.point <= result.upper


def test_extreme_targets_near_the_support_edge() -> None:
    """Variance collapses near the edges; the safeguard must hold the bracket."""
    for a, b, c, d in [(1, 39, 38, 2), (39, 1, 2, 38), (1, 1, 1, 39)]:
        n1, n0, events = a + b, c + d, a + c
        lower, upper = (max(0, events - n0), min(events, n1))
        if a in (lower, upper):
            continue
        point = conditional_mle(a, b, c, d)
        assert 0.0 < point < math.inf
        reference = math.exp(_bisection_reference(n1, n0, events, float(a)))
        assert math.log(point) == pytest.approx(math.log(reference), abs=1e-9)
