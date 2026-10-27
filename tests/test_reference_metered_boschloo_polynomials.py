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
    import metered_boschloo_polynomials as b
    import metered_polynomial as p
    import metered_root as r


def test_comparisons_match_frozen_complete_unit_table_fixture() -> None:
    model = b.Model((0, 1, 0, 1), Q(1, 20), r.Meter())
    assert model.comparisons("greater") == ((), (), (Q(-1), Q(2), Q(-1)), ())
    assert model.comparisons("less") == ((), (Q(0), Q(-1), Q(1)), (), ())


def test_original_compact_objective_preserves_the_frozen_degree_factor() -> None:
    model = b.Model((1, 0, 0, 1), Q(1, 20), r.Meter())
    h = model.objective((False, False, True, False))
    assert h == (
        (Q(-1, 20), Q(1, 10), Q(-1, 20)),
        (Q(1, 20), Q(17, 20), Q(-9, 10)),
        (Q(0), Q(-1), Q(1)),
    )


def test_raw_zero_lengths_survive_until_compactification_degree_is_selected() -> None:
    m = r.Meter()
    assert b.mul((Q(0), Q(0), Q(1)), (), m) == (Q(0), Q(0))
    assert b.scale(Q(0), (Q(1), Q(2)), m) == (Q(0), Q(0))
    assert b.transform((Q(0), Q(0)), 2, m) == ()


def test_opposite_signed_masks_retain_original_probability_level() -> None:
    m = r.Meter()
    model = b.Model((1, 0, 0, 1), Q(1, 20), m)
    h = model.objective((False, False, True, False))
    effect, nuisance = Q(1, 2), Q(1, 2)
    value = sum(
        (p.value(row, effect, m) * nuisance**i for i, row in enumerate(h)), Q(0)
    )
    assert value == Q(1, 20)
