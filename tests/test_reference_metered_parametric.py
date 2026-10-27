"""Independent arithmetic and adverse cases for generic skeleton construction."""

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
    import metered_parametric as f
    import metered_polynomial as p
    import metered_root as r


def meter() -> r.Meter:
    return r.Meter(
        r.Limits(
            arithmetic=p.MeterLimits(max_coefficients=200_000, max_operations=200_000),
            total_work=500_000,
        )
    )


@pytest.mark.parametrize(
    "h,exponent",
    [
        (((Q(-1),), (Q(1),)), 1),
        (((Q(-1),), (), (Q(1),)), 1),
        (((Q(0), Q(0), Q(1)), (Q(0), Q(-2)), (Q(1),)), 2),
        (((Q(-1), Q(1)), (Q(2),), (Q(1),)), 1),
        (((Q(-3),),), 1),
    ],
)
def test_actual_construction_replays(h: f.B, exponent: int) -> None:
    m = meter()
    c = f.generate(h, m)
    assert c.exponent == exponent
    assert c.steps == () or c.steps[0].scale == c.root_scale
    assert all(step.scale for step in c.steps)
    f.replay(h, c, m)
    assert m.operations > 0
    assert m.resources.snapshot().used.coefficient_slots > 0


def test_signed_original_is_never_made_monic() -> None:
    h = ((Q(1), Q(-1)), (Q(-2),), (Q(-1),))
    m = meter()
    c = f.generate(h, m)
    f.replay(h, c, m)
    with pytest.raises(r.InvalidWitness, match="root identity"):
        f.replay(tuple(p.scale(Q(-1), row, m) for row in h), c, m)


def test_tampered_power_identity_is_rejected() -> None:
    h = ((Q(0), Q(0), Q(1)), (Q(0), Q(-2)), (Q(1),))
    m = meter()
    c = f.generate(h, m)
    with pytest.raises(r.InvalidWitness, match="power identity"):
        f.replay(h, replace(c, power_quotient=()), m)


def test_deterministic_output_and_construction_work() -> None:
    h = ((Q(-1), Q(1)), (Q(2),), (Q(1),))
    first, second = meter(), meter()
    assert f.generate(h, first) == f.generate(h, second)
    assert first.root_state() == second.root_state()


def test_strict_q_degree_descent() -> None:
    m = meter()
    a = tuple(f._element((Q(c),), p.ONE, m) for c in (1, 0, 0, 1))
    b = tuple(f._element((Q(c),), p.ONE, m) for c in (1, 1))
    quotient, remainder = f._divide(a, b, m)
    assert len(remainder) < len(b)
    rebuilt = f._fadd(f._fmul(quotient, b, m), remainder, m)
    assert not f._fadd(rebuilt, f._fneg(a, m), m)


def test_exact_signed_family_retains_opposites_and_multiplicity() -> None:
    m = meter()
    family = f.signed_family(
        ((Q(-1), Q(1), Q(0)), (Q(1), Q(-1)), (Q(-1), Q(1)), (Q(1), Q(-2), Q(1)), ()), m
    )
    assert family == ((Q(-1), Q(1)), (Q(1), Q(-1)), (Q(1), Q(-2), Q(1)))


def test_zero_objective_refuses_without_inventing_a_root_packet() -> None:
    with pytest.raises(r.InvalidWitness, match="zero objective"):
        f.generate(((), (Q(0),)), meter())


def test_construction_budget_is_shared_with_replay() -> None:
    m = r.Meter(r.Limits(arithmetic=p.MeterLimits(max_operations=1)))
    with pytest.raises((p.ResourceLimit, r.BudgetRefusal)):
        f.generate(((Q(-1),), (Q(1),)), m)
    assert m.operations == 1


def test_specialized_native_chain_matches_an_independent_rational_root_build() -> None:
    h = ((Q(-1),), (Q(1),), (Q(-1, 2), Q(1)))
    m = meter()
    c = f.generate(h, m)

    def specialize(poly: f.B, effect: Q) -> p.P:
        return tuple(
            sum((coefficient * effect**i for i, coefficient in enumerate(row)), Q(0))
            for row in poly
        )

    def variations(chain: tuple[p.P, ...], point: Q) -> int:
        values = [
            sum((coefficient * point**i for i, coefficient in enumerate(poly)), Q(0))
            for poly in chain
        ]
        signs = [(value > 0) - (value < 0) for value in values if value]
        return sum(left != right for left, right in zip(signs, signs[1:]))

    counts = []
    for effect in (Q(1, 4), Q(3, 4)):
        native_chain = tuple(
            specialize(poly, effect) for poly in (c.representative, *c.tail)
        )
        count = variations(native_chain, Q(0)) - variations(native_chain, Q(1))
        rational = r.generate_with_meter(specialize(h, effect), m, Q(0), Q(1))
        assert count == rational[1].roots_ioc
        counts.append(count)
    assert counts == [0, 1]


def test_bivariate_derivative_keeps_frozen_raw_zero_row() -> None:
    m = meter()
    assert f._bderivative(((Q(7),),), m) == ((),)
    assert f._bderivative(((Q(3),), (Q(4),), (Q(5),)), m) == ((Q(4),), (Q(10),), ())
