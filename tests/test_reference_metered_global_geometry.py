from __future__ import annotations

import sys
from fractions import Fraction as Q
from pathlib import Path

import pytest

REFERENCE_ROOT = Path(__file__).resolve().parents[1] / "formal"
pytestmark = pytest.mark.skipif(
    not REFERENCE_ROOT.is_dir(), reason="repository-only checked reference"
)
if REFERENCE_ROOT.is_dir():
    sys.path.insert(0, str(REFERENCE_ROOT / "tools"))
    import metered_algebraic as a
    import metered_global_geometry as g
    import metered_polynomial as p
    import metered_root as r


def root(poly: p.P, lower: Q, upper: Q, m: r.Meter) -> a.Root:
    return a.Root(poly, lower, upper, r.generate_witness_with_meter(poly, m))


def test_equal_mixed_representations_merge_to_a_rational_point() -> None:
    m = r.Meter()
    half = root((Q(-1), Q(2)), Q(0), Q(1), m)
    assert g.merge_sort((Q(1, 2), half, Q(1, 3), Q(1, 2)), m) == (Q(1, 3), Q(1, 2))


def test_overlapping_distinct_algebraic_roots_are_separated_exactly() -> None:
    m = r.Meter()
    first = root((Q(-1, 2), Q(0), Q(1)), Q(0), Q(1), m)
    second = root((Q(-3, 4), Q(0), Q(1)), Q(0), Q(1), m)
    values = g.merge_sort((second, first), m)
    assert isinstance(values[0], a.Root) and isinstance(values[1], a.Root)
    assert values[0].upper <= values[1].lower


def test_selected_root_is_never_replaced_by_an_isolator_midpoint() -> None:
    m = r.Meter()
    selected = root((Q(-1, 2), Q(0), Q(1)), Q(0), Q(1), m)
    midpoint, left, right = g.sample(Q(0), selected, m)
    assert isinstance(right, a.Root)
    assert Q(0) < midpoint <= right.lower
    assert left == Q(0)
