"""Ordered minlike/Blaker interval completeness (programme issue #16).

Measured against installed ``exactcis==1.0.0``: ``ordered_interval`` walks
outward from the conditional MLE and stops at the first transition, so when the
accepted set is disconnected it returns only the component containing the MLE.
The returned interval is then a strict subset of the accepted set rather than an
enclosure of its hull.
"""

from __future__ import annotations

import math

import pytest

from exactcis import exact_ci_blaker, exact_ci_minlike
from exactcis._numerics import ordered_p_value

from ._evidence import CASE_CONTROL, membership_breakpoints, ordering_membership

# Frozen reproducer. Provenance: adjudication pass, 4 August 2026, installed 1.0.0.
HULL_REPRODUCER = {
    "table": (4, 300, 150, 4),
    "alpha": 0.01,
    "ordering": "minlike",
    "returned_1_0_0": (4.905126e-05, 0.0021640717255946864),
    "accepted_outside": 0.00229,
    "accepted_outside_p": 0.01001655,
}


def _probe_grid(
    n1: int, n0: int, events: int, observed: int, ordering: str
) -> list[float]:
    """Membership breakpoints plus midpoints, as accepted-set probe locations."""
    breakpoints = membership_breakpoints(n1, n0, events, observed)
    grid = list(breakpoints)
    for left, right in zip(breakpoints, breakpoints[1:]):
        grid.append(0.5 * (left + right))
    return sorted(t for t in grid if -700.0 < t < 700.0)


@pytest.mark.xfail(
    strict=True,
    reason="issue #16: first-transition search returns a subset of the accepted set",
)
def test_named_accepted_parameter_lies_inside_returned_interval() -> None:
    a, b, c, d = HULL_REPRODUCER["table"]
    alpha = HULL_REPRODUCER["alpha"]
    theta = HULL_REPRODUCER["accepted_outside"]
    n1, n0, events = a + b, c + d, a + c

    p_value = ordered_p_value(n1, n0, events, a, math.log(theta), ordering="minlike")
    assert p_value >= alpha, (
        "probe point is no longer accepted; reproducer needs regenerating"
    )

    lower, upper = exact_ci_minlike(a, b, c, d, alpha, design=CASE_CONTROL)
    assert lower <= theta <= upper


@pytest.mark.xfail(
    strict=True,
    reason="issue #16: accepted parameters exist outside the returned interval",
)
@pytest.mark.parametrize(
    ("table", "alpha", "ordering"),
    [
        ((4, 300, 150, 4), 0.01, "minlike"),
        ((3, 100, 100, 3), 0.05, "minlike"),
        ((1, 300, 300, 2), 0.05, "minlike"),
        ((0, 35, 9, 15), 0.10, "minlike"),
    ],
)
def test_no_accepted_probe_lies_outside_returned_interval(
    table, alpha, ordering
) -> None:
    """Search the membership grid for accepted points outside the interval."""
    a, b, c, d = table
    n1, n0, events = a + b, c + d, a + c
    solver = exact_ci_minlike if ordering == "minlike" else exact_ci_blaker
    lower, upper = solver(a, b, c, d, alpha, design=CASE_CONTROL)

    escapees = []
    for log_odds in _probe_grid(n1, n0, events, a, ordering):
        if ordered_p_value(n1, n0, events, a, log_odds, ordering=ordering) < alpha:
            continue
        theta = math.exp(log_odds)
        if not (lower <= theta <= upper):
            escapees.append((theta, log_odds))

    assert not escapees, (
        f"{len(escapees)} accepted parameters fall outside ({lower!r}, {upper!r}); "
        f"first at theta={escapees[0][0]!r}"
    )


def test_ordered_p_value_is_not_monotone_within_fixed_membership() -> None:
    """Membership being constant on a segment does not make the p-value monotone.

    This is a property of the mathematics, not a defect, and it is the reason a
    complete construction cannot evaluate only at membership breakpoints: a
    single bisection per segment can miss a pair of crossings. Frozen here so the
    obligation stays visible to whoever implements issue #16.
    """
    n1, n0, events, observed = 35, 12, 36, 31
    breakpoints = membership_breakpoints(n1, n0, events, observed)

    non_monotone = []
    for left, right in zip(breakpoints, breakpoints[1:]):
        if right - left < 1e-6:
            continue
        interior = [left + (right - left) * j / 40 for j in range(1, 40)]
        membership = ordering_membership(
            n1, n0, events, observed, interior[len(interior) // 2]
        )
        if any(
            ordering_membership(n1, n0, events, observed, t) != membership
            for t in (interior[0], interior[-1])
        ):
            continue
        values = [
            ordered_p_value(n1, n0, events, observed, t, ordering="minlike")
            for t in interior
        ]
        deltas = [values[j + 1] - values[j] for j in range(len(values) - 1)]
        turns = sum(1 for j in range(len(deltas) - 1) if deltas[j] * deltas[j + 1] < 0)
        if turns:
            non_monotone.append((left, right, len(membership), turns))

    assert non_monotone, (
        "expected at least one fixed-membership segment on which the ordered "
        "p-value changes direction; none found"
    )


def test_structural_endpoints_are_returned_exactly() -> None:
    """Boundary observations must map to exact ``0`` and ``+inf`` endpoints."""
    lower, upper = exact_ci_minlike(0, 10, 10, 0, 0.05, design=CASE_CONTROL)
    assert lower == 0.0
    lower, upper = exact_ci_minlike(10, 0, 0, 10, 0.05, design=CASE_CONTROL)
    assert math.isinf(upper)


def test_singleton_support_returns_full_set() -> None:
    lower, upper = exact_ci_minlike(0, 0, 0, 1000, 0.05, design=CASE_CONTROL)
    assert lower == 0.0
    assert math.isinf(upper)
