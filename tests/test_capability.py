"""Tests for the private numerical-capability source."""

from __future__ import annotations

from exactcis._capability import support_width
from exactcis._numerics import support_bounds


def test_support_width_matches_support_bounds_on_margin_grid() -> None:
    """The O(1) formula agrees with the existing support definition."""
    for n1 in range(8):
        for n0 in range(8):
            for events in range(n1 + n0 + 1):
                lower, upper = support_bounds(n1, n0, events)
                assert support_width(n1, n0, events) == upper - lower + 1


def test_support_width_distinguishes_the_ordered_cap_boundary() -> None:
    """The live #23 table is one support point above the ordered cap."""
    assert support_width(999_999, 1_000_000, 999_999) == 1_000_000
    assert support_width(1_000_000, 1_000_000, 1_000_000) == 1_000_001
