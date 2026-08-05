"""Certified-hull obligations from docs_md/ordered_hull_specification.md (#16).

The adversarial evidence behind this module is larger than CI should carry:
500 random tables at six alphas under both orderings, 643,920 accepted-probe
checks, zero escapees, and an exhaustive small-table sweep against installed
1.0.0 with zero narrower endpoints and worst outward movement 2.6e-8 on the log
scale. The tests here pin the same properties on a corpus sized for CI.
"""

from __future__ import annotations

import math
import random

import pytest

from exactcis import (
    exact_ci_blaker,
    exact_ci_conditional,
    exact_ci_midp,
    exact_ci_minlike,
)
from exactcis._capability import _HULL_MAX_WIDTH, support_width
from exactcis._numerics import (
    _ordered_p_upper_bound,
    ordered_p_value,
    prepare_margins,
)
from exactcis.exceptions import NumericalError

from ._evidence import CASE_CONTROL, membership_breakpoints

ORDERINGS = [("minlike", exact_ci_minlike), ("blaker", exact_ci_blaker)]

# The measured graze case: p approaches alpha to within 5e-7 over a band of
# width 1.3e-3 before plunging at a membership breakpoint. Exercises the
# amortised frontier sweep and the conservative near-accepted exit.
GRAZE_TABLE = (23, 21, 23, 10)
GRAZE_ALPHA = 0.1


def _probe_grid(n1: int, n0: int, events: int, observed: int) -> list[float]:
    breakpoints = membership_breakpoints(n1, n0, events, observed)
    grid = list(breakpoints)
    for left, right in zip(breakpoints, breakpoints[1:]):
        grid += [left + (right - left) * f for f in (0.25, 0.5, 0.75)]
    if breakpoints:
        grid += [breakpoints[0] - 0.5, breakpoints[-1] + 0.5]
        grid += [breakpoints[0] - 5.0, breakpoints[-1] + 5.0]
    return [t for t in grid if -700.0 < t < 700.0]


def _containment_violations(table, alpha, ordering, solver) -> list[float]:
    a, b, c, d = table
    n1, n0, events = a + b, c + d, a + c
    lower, upper = solver(a, b, c, d, alpha, design=CASE_CONTROL)
    margins = prepare_margins(n1, n0, events)
    out = []
    for t in _probe_grid(n1, n0, events, a):
        p = ordered_p_value(n1, n0, events, a, t, ordering=ordering, prepared=margins)
        if p >= alpha and not (lower <= math.exp(t) <= upper):
            out.append(math.exp(t))
    return out


@pytest.mark.parametrize(("ordering", "solver"), ORDERINGS)
@pytest.mark.parametrize("alpha", [0.01, 0.05, 0.1])
def test_random_corpus_containment(ordering, solver, alpha) -> None:
    """Every accepted probe lies inside the returned interval."""
    rng = random.Random(20260805)
    tables = 0
    while tables < 25:
        table = tuple(rng.randint(0, 25) for _ in range(4))
        a, b, c, d = table
        if a + b == 0 or c + d == 0 or a + c == 0 or b + d == 0:
            continue
        n1, n0, events = a + b, c + d, a + c
        if max(0, events - n0) == min(events, n1):
            continue
        tables += 1
        assert not _containment_violations(table, alpha, ordering, solver), table


@pytest.mark.parametrize(("ordering", "solver"), ORDERINGS)
def test_graze_band_terminates_and_contains(ordering, solver) -> None:
    """The flat-graze table resolves within budget and satisfies containment."""
    lower, upper = solver(*GRAZE_TABLE, GRAZE_ALPHA, design=CASE_CONTROL)
    assert 0.0 < lower < upper < math.inf
    assert not _containment_violations(GRAZE_TABLE, GRAZE_ALPHA, ordering, solver)
    # The upper endpoint sits just beyond the last accepted parameter near
    # exp(0.15385); the conservative exit may leave excess up to the width of
    # the near-accepted band, measured below 1e-5 on the log scale here.
    assert math.log(upper) == pytest.approx(0.15385, abs=1e-4)


def test_hull_extends_beyond_first_transition_on_the_reproducer() -> None:
    """The frozen defect table now returns the hull, not the first component."""
    lower, upper = exact_ci_minlike(4, 300, 150, 4, 0.01, design=CASE_CONTROL)
    first_transition_upper = 0.0021640717255946864  # 1.0.0 value, frozen
    assert upper > first_transition_upper
    assert lower <= 0.00229 <= upper


@pytest.mark.parametrize("ordering", ["minlike", "blaker"])
def test_region_upper_bound_is_sound_against_dense_sampling(ordering) -> None:
    """E2: the inflated envelope dominates p everywhere in the region.

    Validates the _BOUND_INFLATION margin the certificates rest on, across
    region widths spanning four orders of magnitude.
    """
    rng = random.Random(11)
    checked = 0
    for _ in range(60):
        table = tuple(rng.randint(0, 20) for _ in range(4))
        a, b, c, d = table
        if a + b == 0 or c + d == 0 or a + c == 0 or b + d == 0:
            continue
        n1, n0, events = a + b, c + d, a + c
        if max(0, events - n0) == min(events, n1):
            continue
        margins = prepare_margins(n1, n0, events)
        centre = rng.uniform(-4.0, 4.0)
        for width in (1.0, 0.1, 0.01, 0.001):
            t_low, t_high = centre - width / 2, centre + width / 2
            bound = _ordered_p_upper_bound(margins, a, t_low, t_high, ordering=ordering)
            for j in range(21):
                t = t_low + width * j / 20
                p = ordered_p_value(
                    n1, n0, events, a, t, ordering=ordering, prepared=margins
                )
                checked += 1
                assert p <= bound, (
                    f"bound {bound!r} below true p {p!r} at t={t!r} "
                    f"on {table} width {width}"
                )
    assert checked > 3000


def test_determinism() -> None:
    """Identical inputs produce identical intervals across repeated calls."""
    for ordering, solver in ORDERINGS:
        first = solver(*GRAZE_TABLE, GRAZE_ALPHA, design=CASE_CONTROL)
        for _ in range(3):
            assert solver(*GRAZE_TABLE, GRAZE_ALPHA, design=CASE_CONTROL) == first


def test_budget_exhaustion_fails_closed(monkeypatch) -> None:
    """R5: an uncertifiable enclosure raises rather than returning best effort."""
    import exactcis._numerics as numerics

    monkeypatch.setattr(numerics, "_HULL_BOUND_BUDGET", 1)
    with pytest.raises(NumericalError):
        exact_ci_minlike(*GRAZE_TABLE, GRAZE_ALPHA, design=CASE_CONTROL)


@pytest.mark.parametrize(("ordering", "solver"), ORDERINGS)
def test_ordered_width_preflight_refuses_before_any_preparation(
    monkeypatch, ordering, solver
) -> None:
    """An over-cap ordered call must not enter either preparation entry point."""
    import exactcis._numerics as numerics

    monkeypatch.setattr(numerics, "_HULL_MAX_WIDTH", 10)

    def unexpected_preparation(*args, **kwargs):
        raise AssertionError("ordered preflight entered support preparation")

    monkeypatch.setattr(numerics, "prepare_margins", unexpected_preparation)
    monkeypatch.setattr(numerics.PreparedMargins, "__init__", unexpected_preparation)
    with pytest.raises(NumericalError) as excinfo:
        solver(5, 5, 5, 5, 0.05, design=CASE_CONTROL)
    diagnostics = excinfo.value.diagnostics
    assert excinfo.value.method == ordering
    assert diagnostics == {
        "method": ordering,
        "support_size": 11,
        "limit": 10,
        "limit_kind": "ordered_hull_certification",
    }


@pytest.mark.parametrize(("ordering", "solver"), ORDERINGS)
def test_ordered_small_cap_boundary_enters_preparation_only_at_cap(
    monkeypatch, ordering, solver
) -> None:
    """An injected cap proves the at-cap and cap-plus-one execution order."""
    import exactcis._numerics as numerics

    monkeypatch.setattr(numerics, "_HULL_MAX_WIDTH", 10)
    original_prepare_margins = numerics.prepare_margins
    prepared_calls: list[tuple[int, int, int]] = []

    def spy_prepare_margins(n1: int, n0: int, events: int):
        prepared_calls.append((n1, n0, events))
        return original_prepare_margins(n1, n0, events)

    monkeypatch.setattr(numerics, "prepare_margins", spy_prepare_margins)
    lower, upper = solver(4, 5, 5, 5, 0.05, design=CASE_CONTROL)
    assert 0.0 <= lower <= upper
    assert prepared_calls == [(9, 10, 9)]

    prepared_calls.clear()
    with pytest.raises(NumericalError):
        solver(5, 5, 5, 5, 0.05, design=CASE_CONTROL)
    assert prepared_calls == []


def test_ordered_real_cap_boundary_is_calculated_without_allocation() -> None:
    """The production cap and cap-plus-one boundary use pure arithmetic."""
    assert support_width(999_999, 1_000_000, 999_999) == _HULL_MAX_WIDTH
    assert support_width(1_000_000, 1_000_000, 1_000_000) == _HULL_MAX_WIDTH + 1


@pytest.mark.parametrize("solver", (exact_ci_conditional, exact_ci_midp))
def test_equal_tail_routes_keep_their_common_preparation_cap(
    monkeypatch, solver
) -> None:
    """Conditional and Mid-P do not inherit the ordered-hull cap."""
    import exactcis._numerics as numerics

    monkeypatch.setattr(numerics, "_HULL_MAX_WIDTH", 10)
    lower, upper = solver(5, 5, 5, 5, 0.05, design=CASE_CONTROL)
    assert 0.0 <= lower <= upper


def test_structural_endpoints_and_sentinels() -> None:
    """R2 and R4: exact structural values, never a finite search sentinel."""
    lower, upper = exact_ci_minlike(0, 10, 10, 0, 0.05, design=CASE_CONTROL)
    assert lower == 0.0
    lower, upper = exact_ci_blaker(10, 0, 0, 10, 0.05, design=CASE_CONTROL)
    assert math.isinf(upper)
    for ordering, solver in ORDERINGS:
        lower, upper = solver(0, 0, 0, 1000, 0.05, design=CASE_CONTROL)
        assert (lower, upper) == (0.0, math.inf)


def test_boundary_observation_with_extreme_ratios_is_not_refused() -> None:
    """Regression for a pre-existing false refusal, exposed by review.

    For a boundary observation the likelihood supremum sits at an extended
    endpoint, and the acceptance probe must be taken beyond every mass-ordering
    tie, which all lie at t = -r_k. The previous fixed +/-36 proxy was inside
    that span for extreme margins and produced a false "below alpha at its
    likelihood maximum" refusal on a valid table.
    """
    lower, upper = exact_ci_minlike(0, 10**12, 50000, 0, 0.05, design=CASE_CONTROL)
    assert lower == 0.0
    assert 0.0 < upper < 1e-12


def test_registry_wording_matches_the_specification() -> None:
    from exactcis.estimands import Design as RegistryDesign
    from exactcis.estimands import Estimand, get_method_spec

    for key in ("minlike", "blaker"):
        spec = get_method_spec(
            RegistryDesign.CASE_CONTROL_FIXED_MARGIN, Estimand.OR, key
        )
        assert spec.interval_type == (
            "numerically certified interval hull of the inverted ordered"
            " conditional exact confidence set"
        )
