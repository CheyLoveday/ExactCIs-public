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
    import metered_isolate as i
    import metered_root as r


def test_structural_roots_are_excluded() -> None:
    assert i.isolate((Q(0), Q(-1), Q(1)), r.Meter()) == ()


def test_all_distinct_internal_roots_are_isolated_once() -> None:
    roots = i.isolate((Q(3, 16), Q(-1), Q(1)), r.Meter())
    assert len(roots) == 2
    assert all(type(root) is a.Root for root in roots)
    assert isinstance(roots[0], a.Root) and isinstance(roots[1], a.Root)
    assert roots[0].upper <= roots[1].lower


def test_midpoint_root_is_emitted_rationally_and_endpoint_roots_are_omitted() -> None:
    # (2*x-1)*(x-1)*(x+1)
    assert i.isolate((Q(1), Q(-2), Q(-1), Q(2)), r.Meter()) == (Q(1, 2),)


def test_repeated_root_is_counted_once() -> None:
    roots = i.isolate((Q(1, 4), Q(-1), Q(1)), r.Meter())
    assert len(roots) == 1


def test_complete_zero_polynomial_is_refused() -> None:
    with pytest.raises(r.InvalidWitness, match="zero projection"):
        i.isolate((), r.Meter())


def test_midpoint_is_emitted_between_its_left_and_right_subtrees() -> None:
    # Three rational roots expose the ordering error of a breadth-first
    # emission queue: the central root must wait for the left subtree.
    assert i.isolate((Q(-3, 32), Q(11, 16), Q(-3, 2), Q(1)), r.Meter()) == (
        Q(1, 4),
        Q(1, 2),
        Q(3, 4),
    )
