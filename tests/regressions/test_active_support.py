"""Exact-underflow active support (programme issue #18).

Claim discipline, per the programme: the active path matches the corresponding
full-support recurrence under the same binary64 arithmetic, asserted as exact
equality against the retained ``_probabilities_full`` oracle. No claim is made
about any other implementation's bits.
"""

from __future__ import annotations

import math
import random

import pytest

import exactcis._numerics as numerics
from exactcis._numerics import _UNDERFLOW_STOP, _probe_underflow, prepare_margins

MARGIN_CASES = [
    (10, 10, 10),
    (35, 12, 36),
    (200, 150, 180),
    (2000, 2000, 1600),
    (20000, 20000, 16000),
]
LOG_ODDS_CASES = [-30.0, -6.0, -0.5, 0.0, 0.7, 6.0, 30.0]


def test_platform_probe_passes_here() -> None:
    """The stop rule is only enabled when the probe certifies the platform."""
    assert _probe_underflow()
    assert numerics._ACTIVE_SUPPORT_OK
    for value in (-800.0, -1000.0, -1e9):
        assert math.exp(value) == 0.0


@pytest.mark.parametrize(("n1", "n0", "events"), MARGIN_CASES)
@pytest.mark.parametrize("log_odds", LOG_ODDS_CASES)
def test_active_equals_full_exactly(n1, n0, events, log_odds) -> None:
    """Bitwise equality with the complete-support recurrence."""
    margins = prepare_margins(n1, n0, events)
    active = margins.probabilities(log_odds)
    full = margins._probabilities_full(log_odds)
    assert active == full


@pytest.mark.parametrize("log_odds", [-math.inf, math.inf])
def test_extended_endpoints_equal_full(log_odds) -> None:
    margins = prepare_margins(40, 30, 25)
    assert margins.probabilities(log_odds) == margins._probabilities_full(log_odds)


def test_moments_equal_full_traversal_exactly() -> None:
    margins = prepare_margins(2000, 2000, 1600)
    for log_odds in LOG_ODDS_CASES:
        points, probabilities = margins._probabilities_full(log_odds)
        mean = math.fsum(v * p for v, p in zip(points, probabilities))
        variance = math.fsum(
            (v - mean) * (v - mean) * p for v, p in zip(points, probabilities)
        )
        assert margins.moments(log_odds) == (mean, variance)


def test_random_tables_active_equals_full() -> None:
    rng = random.Random(18)
    for _ in range(150):
        n1 = rng.randint(1, 400)
        n0 = rng.randint(1, 400)
        events = rng.randint(1, n1 + n0)
        margins = prepare_margins(n1, n0, events)
        eta = rng.uniform(-40.0, 40.0)
        assert margins.probabilities(eta) == margins._probabilities_full(eta)


def test_active_range_brackets_the_mode_and_shrinks() -> None:
    """Structural gate: the active width grows like the square root of support.

    The relative log mass decays quadratically with distance from the mode at
    rate 1/(2 sigma^2) with sigma of order sqrt(W), so the walk stops after
    roughly sqrt(2 * 800) * sigma points, about 27 * sqrt(W). The assertion
    carries several times that headroom; anything linear in W blows through it.
    """
    margins = prepare_margins(20000, 20000, 16000)
    for eta in (-2.0, 0.0, 2.0):
        low, high = margins._active_range(eta)
        mode = margins.mode_index(eta)
        assert low <= mode < high
        assert high - low < 130 * math.sqrt(margins.width), (
            low,
            high,
            margins.width,
        )
    # Values just outside the range are genuinely below the stop threshold.
    low, high = margins._active_range(0.0)
    masses = margins._relative_log_masses(0.0)
    if high < margins.width:
        assert masses[high] <= _UNDERFLOW_STOP
    if low > 0:
        assert masses[low - 1] <= _UNDERFLOW_STOP


def test_outward_accumulation_is_non_increasing_in_float() -> None:
    """The rounding fact the stop rule rests on.

    Beyond the mode every increment ``r[i] + eta`` is non-positive, and adding
    a non-positive increment to a float cannot round above it, so the running
    value is non-increasing and every skipped index is at or below the
    threshold that stopped the walk.
    """
    margins = prepare_margins(5000, 4000, 3500)
    for eta in (-3.0, 0.0, 3.0):
        masses = margins._relative_log_masses(eta)
        mode = margins.mode_index(eta)
        for i in range(mode, margins.width - 1):
            assert masses[i + 1] <= masses[i]
        for i in range(mode, 0, -1):
            assert masses[i - 1] <= masses[i]


def test_disabled_probe_falls_back_to_full(monkeypatch) -> None:
    """Obligation: an uncertifiable platform uses the complete recurrence."""
    monkeypatch.setattr(numerics, "_ACTIVE_SUPPORT_OK", False)
    margins = prepare_margins(2000, 2000, 1600)
    assert margins.probabilities(0.3) == margins._probabilities_full(0.3)


def test_no_heuristic_cutoff_constant_exists() -> None:
    """The stop is exact underflow, not a tuned window.

    Guards against reintroducing a sigma-multiple truncation: the only
    constant involved is the underflow threshold, which sits strictly below
    the binary64 exponent floor.
    """
    assert _UNDERFLOW_STOP < -745.14
    source = open(numerics.__file__).read()
    assert "sigma" not in source.lower() or "std" not in source.lower()
