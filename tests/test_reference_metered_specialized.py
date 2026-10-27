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
    import metered_specialized as s


def meter() -> r.Meter:
    return r.Meter(
        r.Limits(
            arithmetic=p.MeterLimits(max_coefficients=500_000, max_operations=500_000),
            total_work=1_000_000,
        )
    )


def root(definer: p.P, lower: Q, upper: Q, m: r.Meter) -> a.Root:
    return a.Root(definer, lower, upper, r.generate_witness_with_meter(definer, m))


def test_actual_selected_field_root_packet_replays() -> None:
    m = meter()
    selected = root((Q(-1, 2), Q(0), Q(1)), Q(1, 2), Q(1), m)
    h = ((Q(0), Q(-1)), (), (Q(1),))
    localized, certificate = s.generate(h, selected, m)
    assert localized.definer == selected.definer
    assert certificate.exponent == 1
    assert len(certificate.derivative_witness) == len(certificate.representative)
    s.replay(h, localized, certificate, m)


def test_nonunit_at_irrelevant_root_is_removed_and_packet_restarted() -> None:
    m = meter()
    d = p.mul((Q(-1, 2), Q(0), Q(1)), (Q(-1, 4), Q(1)), m)
    selected = root(d, Q(1, 2), Q(1), m)
    h = ((Q(-1),), (Q(-1, 4), Q(1)))
    localized, certificate = s.generate(h, selected, m)
    assert len(localized.definer) < len(d)
    assert len(localized.definer) == 3
    s.replay(h, localized, certificate, m)


def test_degree_drop_at_selected_root_keeps_its_factor() -> None:
    m = meter()
    d = p.mul((Q(-1, 2), Q(0), Q(1)), (Q(-1, 4), Q(1)), m)
    selected = root(d, Q(0), Q(1, 2), m)
    h = ((Q(-1, 2),), (Q(1),), (Q(-1, 4), Q(1)))
    localized, certificate = s.generate(h, selected, m)
    assert len(localized.definer) == 2
    assert len(certificate.representative) == 2
    s.replay(h, localized, certificate, m)


def test_tampered_modular_witness_is_refused() -> None:
    m = meter()
    selected = root((Q(-1, 2), Q(0), Q(1)), Q(1, 2), Q(1), m)
    h = ((Q(0), Q(-1)), (), (Q(1),))
    localized, certificate = s.generate(h, selected, m)
    with pytest.raises(r.InvalidWitness, match="coefficient count"):
        s.replay(h, localized, replace(certificate, root_witness=()), m)


def test_frozen_derivative_zero_row_cannot_be_omitted() -> None:
    m = meter()
    selected = root((Q(-1, 2), Q(0), Q(1)), Q(1, 2), Q(1), m)
    h = ((Q(0), Q(-1)), (), (Q(1),))
    localized, certificate = s.generate(h, selected, m)
    shortened = replace(
        certificate, derivative_witness=certificate.derivative_witness[:-1]
    )
    with pytest.raises(r.InvalidWitness, match="coefficient count"):
        s.replay(h, localized, shortened, m)
