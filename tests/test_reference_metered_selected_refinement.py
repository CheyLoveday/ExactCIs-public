from __future__ import annotations

import sys
from dataclasses import replace
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
    import metered_polynomial as p
    import metered_root as r
    import metered_selected_refinement as selected
    import resource_model as v


def root(poly: p.P, lower: Q, upper: Q, m: r.Meter) -> a.Root:
    return a.Root(poly, lower, upper, r.generate_witness_with_meter(poly, m))


def test_one_common_interval_establishes_every_finite_sign() -> None:
    m = r.Meter()
    d = (Q(-1, 2), Q(0), Q(1))
    point = root(d, Q(0), Q(1), m)
    family = (d, (Q(-1, 2), Q(1)), (Q(-3, 4), Q(1)), ())
    result = selected.localize(point, family, m)
    assert result.signs == (0, 1, -1, 0)
    assert isinstance(result.point, a.Root)
    for poly, witness, sign in zip(family, result.witnesses, result.signs):
        assert witness is not None
        assert a.sign_at(result.point, poly, witness, m) == sign


def test_encountered_midpoint_root_becomes_exact_rational() -> None:
    m = r.Meter()
    d = (Q(3, 4), Q(-2), Q(1))
    point = root(d, Q(0), Q(1), m)
    result = selected.localize(point, ((Q(-1, 4), Q(1)),), m)
    assert result.point == Q(1, 2)
    assert result.signs == (1,)


def test_gcd_zero_localization_refers_to_the_same_selected_factor() -> None:
    m = r.Meter()
    d = p.mul((Q(-1, 2), Q(0), Q(1)), (Q(-1, 4), Q(1)), m)
    point = root(d, Q(0), Q(1, 2), m)
    result = selected.localize(point, ((Q(-1, 4), Q(1)),), m)
    assert result.point == Q(1, 4)
    assert result.signs == (0,)


def test_depth_refusal_is_precharged_and_keeps_the_shared_state() -> None:
    profile = replace(
        v.DEVELOPMENT, shapes=replace(v.DEVELOPMENT.shapes, refinement_depth=0)
    )
    m = r.Meter(r.Limits(profile=profile))
    d = (Q(-1, 2), Q(0), Q(1))
    point = root(d, Q(0), Q(1), m)
    with pytest.raises(v.ShapeRefusal):
        selected.localize(point, ((Q(-1, 2), Q(1)),), m)
    assert m.operations > 0
    assert m.resources.snapshot().used.projection_roots > 0
