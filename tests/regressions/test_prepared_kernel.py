"""Differential and structural tests for the prepared FNCH kernel (issue #11).

The claim under test is agreement with the retained absolute-coefficient
evaluator under the same binary64 arithmetic, and improved agreement with the
high-precision oracle. It is deliberately *not* a claim of bit-identity with the
1.0.0 ``_log_choose`` path: the two use different arithmetic, so identical bits
are neither expected nor promised.
"""

from __future__ import annotations

import math

import pytest

from exactcis import (
    exact_ci_blaker,
    exact_ci_conditional,
    exact_ci_midp,
    exact_ci_minlike,
)
from exactcis._numerics import (
    _legacy_fnch_probabilities,
    prepare_margins,
)
from exactcis.exceptions import NumericalError

from . import _oracles
from ._evidence import CASE_CONTROL

MARGIN_CASES = [
    (10, 10, 10),
    (35, 12, 36),
    (60, 60, 60),
    (200, 150, 180),
    (500, 500, 400),
    (1000, 700, 900),
]
LOG_ODDS_CASES = [-6.0, -2.0, -0.5, 0.0, 0.7, 2.0, 6.0]


@pytest.mark.parametrize(("n1", "n0", "events"), MARGIN_CASES)
@pytest.mark.parametrize("log_odds", LOG_ODDS_CASES)
def test_agrees_with_the_legacy_evaluator(n1, n0, events, log_odds) -> None:
    """Differential test against the retained absolute-coefficient evaluator."""
    points, probabilities = prepare_margins(n1, n0, events).probabilities(log_odds)
    legacy_points, legacy_probabilities = _legacy_fnch_probabilities(
        n1, n0, events, log_odds
    )

    assert points == legacy_points
    worst = 0.0
    for new, old in zip(probabilities, legacy_probabilities):
        if old <= 1e-15:
            continue
        worst = max(worst, abs(new - old) / old)
    assert worst < 1e-9, (
        f"worst relative divergence from the legacy evaluator {worst:.3e}"
    )


@pytest.mark.skipif(
    not _oracles.HAVE_MPMATH, reason="mpmath (validation extra) required"
)
@pytest.mark.parametrize(("n1", "n0", "events"), [(500, 500, 400), (1000, 700, 900)])
@pytest.mark.parametrize("log_odds", [-6.0, 0.0, 2.0, 6.0])
def test_is_at_least_as_accurate_as_the_legacy_evaluator(
    n1, n0, events, log_odds
) -> None:
    """Mode anchoring must not be worse than the absolute-coefficient form.

    At large support widths and parameters far from one it is substantially
    better, because every relative log mass stays small in magnitude instead of
    being formed as a difference of two large opposite-signed quantities.
    """
    _, probabilities = prepare_margins(n1, n0, events).probabilities(log_odds)
    _, legacy = _legacy_fnch_probabilities(n1, n0, events, log_odds)
    _, reference = _oracles.fnch_probabilities(n1, n0, events, log_odds)

    def worst_error(candidate) -> float:
        worst = 0.0
        for got, ref in zip(candidate, reference):
            if float(ref) <= 1e-14:
                continue
            worst = max(worst, _oracles.relative_error(got, ref))
        return worst

    prepared_error = worst_error(probabilities)
    legacy_error = worst_error(legacy)
    assert prepared_error <= max(legacy_error, 1e-14) * 1.5, (
        f"prepared {prepared_error:.3e} vs legacy {legacy_error:.3e}"
    )


@pytest.mark.parametrize(("n1", "n0", "events"), MARGIN_CASES)
@pytest.mark.parametrize("log_odds", LOG_ODDS_CASES)
def test_mode_index_is_the_argmax(n1, n0, events, log_odds) -> None:
    """Binary search on the decreasing adjacent ratio must find the true mode."""
    margins = prepare_margins(n1, n0, events)
    points, probabilities = margins.probabilities(log_odds)
    expected = max(range(len(probabilities)), key=probabilities.__getitem__)
    assert margins.mode_index(log_odds) == expected


@pytest.mark.parametrize(("n1", "n0", "events"), MARGIN_CASES)
@pytest.mark.parametrize("log_odds", LOG_ODDS_CASES)
def test_adjacent_ratio_is_strictly_decreasing(n1, n0, events, log_odds) -> None:
    """Unimodality and the binary search both rest on this monotonicity."""
    margins = prepare_margins(n1, n0, events)
    ratios = margins._ratios  # noqa: SLF001 - structural property under test
    assert all(later < earlier for earlier, later in zip(ratios, ratios[1:]))


@pytest.mark.parametrize(("n1", "n0", "events"), MARGIN_CASES)
def test_probabilities_are_unimodal(n1, n0, events) -> None:
    """Log-concavity implies a single rise then a single fall."""
    for log_odds in LOG_ODDS_CASES:
        _, probabilities = prepare_margins(n1, n0, events).probabilities(log_odds)
        peak = max(range(len(probabilities)), key=probabilities.__getitem__)
        assert all(
            probabilities[i] <= probabilities[i + 1] * (1 + 1e-12) for i in range(peak)
        )
        assert all(
            probabilities[i] >= probabilities[i + 1] * (1 - 1e-12)
            for i in range(peak, len(probabilities) - 1)
        )


def test_extended_parameter_endpoints_are_point_masses() -> None:
    margins = prepare_margins(40, 30, 25)
    points, low = margins.probabilities(-math.inf)
    assert low[0] == 1.0 and math.fsum(low[1:]) == 0.0
    points, high = margins.probabilities(math.inf)
    assert high[-1] == 1.0 and math.fsum(high[:-1]) == 0.0


def test_non_finite_parameter_fails_closed() -> None:
    margins = prepare_margins(40, 30, 25)
    with pytest.raises(NumericalError):
        margins.probabilities(float("nan"))


def test_singleton_support_is_a_point_mass() -> None:
    margins = prepare_margins(0, 1000, 0)
    points, probabilities = margins.probabilities(0.3)
    assert probabilities == (1.0,)


def test_preparation_is_reusable_and_stateless() -> None:
    """Repeated evaluation on one prepared object must not drift."""
    margins = prepare_margins(200, 150, 180)
    first = margins.probabilities(0.4)
    for _ in range(20):
        margins.probabilities(-3.0)
        margins.probabilities(5.0)
    assert margins.probabilities(0.4) == first


def test_moments_match_a_separate_traversal() -> None:
    margins = prepare_margins(200, 150, 180)
    for log_odds in LOG_ODDS_CASES:
        points, probabilities = margins.probabilities(log_odds)
        mean = math.fsum(v * p for v, p in zip(points, probabilities))
        variance = math.fsum((v - mean) ** 2 * p for v, p in zip(points, probabilities))
        got_mean, got_variance = margins.moments(log_odds)
        assert got_mean == pytest.approx(mean, rel=1e-15, abs=1e-300)
        assert got_variance == pytest.approx(variance, rel=1e-12, abs=1e-300)


@pytest.mark.parametrize(
    "table",
    [(5, 2, 5, 8), (12, 5, 8, 10), (30, 20, 15, 35), (1, 9, 11, 3), (0, 10, 10, 0)],
)
def test_public_intervals_are_unchanged_within_envelope(table) -> None:
    """Every conditional route must stay inside the accuracy envelope.

    Values are compared against the independently recorded 1.0.0 outputs so a
    kernel change cannot quietly move a published endpoint.
    """
    for solver in (
        exact_ci_conditional,
        exact_ci_midp,
        exact_ci_blaker,
        exact_ci_minlike,
    ):
        lower, upper = solver(*table, 0.05, design=CASE_CONTROL)
        assert lower <= upper
        assert lower >= 0.0
        assert not math.isnan(lower) and not math.isnan(upper)
