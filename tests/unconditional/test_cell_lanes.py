"""Whole-effect-cell evidence and attacks against independent sufficient lanes."""

from fractions import Fraction as F

import pytest

from . import _cell_lanes as cells
from . import _cutoff_cover_reference as cutoff
from . import _tensor_reference as tensor
from ._topology import topology


@pytest.mark.parametrize(
    "n1,n0,observed", [(1, 1, (1, 0)), (1, 2, (1, 0)), (2, 1, (0, 1)), (2, 2, (1, 1))]
)
def test_whole_cell_lanes_compare_with_exact_projected_events(n1, n0, observed):
    rows = cells.compare_cells(
        n1, n0, observed, F(1, 40), topology(n1, n0, observed, F(1, 40))
    )
    assert rows
    for row in rows:
        for name in ("tensor", "cutoff_cover"):
            answer = row[name]["decision"]
            assert answer is None or answer == row["projected_event"]
            assert row[name]["counts"]["effect_nodes"] > 0


@pytest.mark.parametrize("direction", ["greater", "less"])
def test_independent_comparison_signs_match_normalized_fisher(direction):
    family = cells.comparisons(2, 3, (1, 0), direction)
    for psi in (F(1, 4), F(1), F(7, 3)):
        s = psi / (1 + psi)
        target = cutoff._fisher(2, 3, (1, 0), psi, direction == "greater")
        for point, polynomial in family.items():
            value = sum((c * s**i for (i, _), c in polynomial.items()), F(0))
            tail = cutoff._fisher(2, 3, point, psi, direction == "greater")
            assert (value > 0) - (value < 0) == (tail > target) - (tail < target)


def test_mask_band_and_scientific_mutations_are_detected(monkeypatch):
    result = topology(1, 1, (1, 0), F(1, 40))
    monkeypatch.setattr(cells, "bands", lambda *args, **kwargs: (((0, 0),), ()))
    with pytest.raises(AssertionError, match="mask-band"):
        cells.compare_cells(1, 1, (1, 0), F(1, 40), result)
    monkeypatch.undo()
    monkeypatch.setattr(cells, "decide", lambda *args, **kwargs: (True, {}))
    with pytest.raises(AssertionError, match="scientific decision"):
        cells.compare_cells(1, 1, (1, 0), F(1, 40), result)


def test_direction_switching_rejection_is_a_cover_not_one_global_direction():
    # Generic polynomial certificate attack, not a discovered Boschloo table.
    greater = {(1, 0): F(1), (0, 0): F(-3, 4)}
    less = {(0, 0): F(1, 4), (1, 0): F(-1)}
    assert tensor.hull(tensor.controls(greater, (1, 0), (F(0), F(1, 2), F(0), F(1))))[
        1
    ] == F(-1, 4)
    assert tensor.hull(tensor.controls(less, (1, 0), (F(1, 2), F(1), F(0), F(1))))[
        1
    ] == F(-1, 4)
    assert (
        tensor.hull(tensor.controls(greater, (1, 0), (F(0), F(1), F(0), F(1))))[1] > 0
    )
    assert tensor.hull(tensor.controls(less, (1, 0), (F(0), F(1), F(0), F(1))))[1] > 0


def test_two_witness_cover_succeeds_where_no_single_witness_covers():
    # Generic H=1/16-(q-s)^2. No fixed q covers s=0 and s=1, while
    # q=1/4 and q=3/4 cover the two closed half-effect intervals.
    power = {(0, 0): F(1, 16), (2, 0): F(-1), (1, 1): F(2), (0, 2): F(-1)}
    for a, b, q in ((F(0), F(1, 2), F(1, 4)), (F(1, 2), F(1), F(3, 4))):
        controls = tensor.controls(power, (2, 2), (a, b, F(0), F(1)))
        assert tensor.constant_witness(controls, q)
    whole = tensor.controls(power, (2, 2), (F(0), F(1), F(0), F(1)))
    assert not tensor.constant_witness(whole, F(1, 4))
    assert not tensor.constant_witness(whole, F(3, 4))
    # max(q,1-q)>=1/2, so at one effect endpoint H<=-3/16.
    assert F(1, 16) - F(1, 2) ** 2 == F(-3, 16)


def test_local_derivative_control_certificate_rejects_sign_mutation():
    # Generic f(s)=s-s^2 is strictly increasing on [0,1/4].
    derivative = {(0, 0): F(1), (1, 0): F(-2)}
    controls = tensor.controls(derivative, (1, 0), (F(0), F(1, 4), F(0), F(1)))
    assert tensor.hull(controls)[0] == F(1, 2)
    reversed_sign = {key: -value for key, value in derivative.items()}
    forged = tensor.controls(reversed_sign, (1, 0), (F(0), F(1, 4), F(0), F(1)))
    assert tensor.hull(forged)[0] < 0


def test_actual_asymmetric_boschloo_maximizer_moves():
    # n1=1,n0=2, observed=(1,0): the greater mask is {(1,0)}.
    # At psi=1 the unique maximizer is q=1/3. At psi=1/4 the
    # derivative numerator at q=1/3 is positive, so that witness is not maximal.
    for psi in (F(1, 4), F(1)):
        assert cutoff.mask(1, 2, (1, 0), psi, "greater") == ((1, 0),)
    q = F(1, 3)

    def derivative_factor(psi):
        return 1 - 3 * q + 2 * (1 - psi) * q * q

    assert derivative_factor(F(1)) == 0
    assert derivative_factor(F(1, 4)) > 0
    assert cutoff.probability(1, 2, ((1, 0),), F(1, 4), F(2, 5)) > cutoff.probability(
        1, 2, ((1, 0),), F(1, 4), q
    )
    # This proves movement of an actual maximizer, not impossibility of every
    # constant acceptance witness. The generic ridge test covers that stronger attack.


def test_t1_min_uses_global_hull_excess_and_retains_ghost_fringe():
    inner = ((F(2, 5), F(3, 5)),)
    outer = ((F(1, 100), F(1, 50)), (F(39, 100), F(61, 100)))
    tolerance = F(1, 50)
    excess = max(inner[0][0] - outer[0][0], outer[-1][1] - inner[-1][1])
    assert all(b - a <= tolerance for a, b in outer[:1])
    assert excess > tolerance  # narrow unmatched ghost still spoils global hull
    adjacent_fringe = ((F(0), F(1, 100)), (F(1, 100), F(1, 50)))
    assert all(b - a <= F(1, 100) for a, b in adjacent_fringe)
    assert adjacent_fringe[-1][1] - adjacent_fringe[0][0] > F(1, 100)
