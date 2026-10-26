"""Independent lane identities, inclusive boundaries and honest inconclusions."""

from fractions import Fraction as F
from pathlib import Path

import pytest

from . import _tensor_reference as tensor
from ._lane_comparison import compare


def test_stored_full_qualification_replays_from_source_or_sdist():
    from ._lane_comparison import read_packet, verify_packet

    packet = read_packet(
        Path(__file__).parents[1] / "references/unconditional/qualification_v1.json"
    )
    assert len(packet["results"]) == 1440
    assert packet["domain"]["positive_groups_total_at_most"] == 6
    verify_packet(packet)


@pytest.mark.parametrize(
    "n1,n0,observed", ((1, 1, (1, 0)), (1, 2, (1, 1)), (2, 2, (0, 1)), (4, 4, (0, 2)))
)
@pytest.mark.parametrize("psi", (F(1, 3), F(1), F(7, 3)))
@pytest.mark.parametrize("direction", ("greater", "less"))
@pytest.mark.parametrize("level", (F(0), F(1, 40), F(1, 2)))
def test_independent_exact_lane_comparison(n1, n0, observed, psi, direction, level):
    row = compare(n1, n0, observed, psi, direction, level)
    assert row["projected_event"] in ("accepted", "rejected", "resource_refused")
    if row["projected_event"] != "resource_refused":
        for lane in ("tensor", "cutoff_cover"):
            assert row[lane] == "inconclusive" or row[lane] == row["projected_event"]


def test_constant_witness_does_not_claim_moving_ridge_complete():
    # Generic checker attack H(s,q)=-(q-s)^2; not a Boschloo table fixture.
    power = {(2, 0): F(-1), (1, 1): F(2), (0, 2): F(-1)}
    controls = tensor.controls(power, (2, 2), (F(0), F(1), F(0), F(1)))
    assert tensor.evaluate(controls, F(2, 7), F(2, 7)) == 0
    assert not any(tensor.constant_witness(controls, q) for q in (F(0), F(1, 2), F(1)))


def test_strict_rejection_and_inclusive_equality_are_separate():
    assert tensor.decide_nuisance((F(0), F(0)))[0] is True
    assert tensor.decide_nuisance((F(-1), F(-1)))[0] is False
    # Negative endpoints with a zero tangency at an unresolved nuisance are not
    # entitled to a negative answer just because bounded controls remain mixed.
    assert tensor.decide_nuisance((F(-1), F(2), F(-4)), depth=0)[0] is None


def test_irrational_tangency_requires_exact_fallback():
    from ._polynomial import threshold_decision

    # Generic attack H(q)=-(q*q-1/2)**2; no dyadic sample owns its zero.
    power = {(0, 0): F(-1, 4), (0, 2): F(1), (0, 4): F(-1)}
    controls = tensor.controls(power, (0, 4), (F(0), F(1), F(0), F(1)))
    assert tensor.decide_nuisance(controls[0], depth=4)[0] is None
    assert threshold_decision((F(-1, 4), F(0), F(1), F(0), F(-1)))


def test_effect_only_subdivision_can_stall_on_a_negative_objective():
    # Generic attack, independent of s: -(q-1/2)**2 - 1/100 < 0.
    power = {(0, 0): F(-13, 50), (0, 1): F(1), (0, 2): F(-1)}
    parent = tensor.controls(power, (1, 2), (F(0), F(1), F(0), F(1)))
    left_effect = tensor.controls(power, (1, 2), (F(0), F(1, 2), F(0), F(1)))
    right_effect = tensor.controls(power, (1, 2), (F(1, 2), F(1), F(0), F(1)))
    assert left_effect == right_effect == parent
    assert tensor.hull(parent)[1] > 0
    for lo, hi in ((F(0), F(1, 2)), (F(1, 2), F(1))):
        child = tensor.controls(power, (1, 2), (F(0), F(1), lo, hi))
        assert tensor.hull(child)[1] == F(-1, 100)


def test_rehashed_scientific_corruption_is_rejected():
    from ._lane_comparison import qualification, verify_packet
    from ._replay import digest

    packet = qualification(2)
    packet["results"][0]["projected_event"] = "rejected"
    packet["outputs_sha256"] = digest(
        "exactcis.three_lane.outputs.v1", packet["results"]
    )
    with pytest.raises(ValueError, match="scientific replay mismatch"):
        verify_packet(packet)


def test_source_identity_and_omitted_case_are_rejected():
    from ._lane_comparison import qualification, verify_packet

    packet = qualification(2)
    packet["sources"]["tests/unconditional/_tensor_reference.py"] = "0" * 64
    with pytest.raises(ValueError, match="identity"):
        verify_packet(packet)
    packet = qualification(2)
    packet["results"].pop()
    with pytest.raises(ValueError, match="replay mismatch"):
        verify_packet(packet)


def test_real_polynomial_budget_refusal_is_retained():
    from ._polynomial import OracleLimits

    row = compare(
        1,
        1,
        (1, 0),
        F(1),
        "greater",
        F(1, 40),
        polynomial_limits=OracleLimits(max_degree=0),
    )
    assert row["projected_event"] == "resource_refused"
    assert row["projected_profile"]["max_degree"] == 0
    assert row["refusal"]


@pytest.mark.parametrize(
    "mutation,match",
    (
        ("mask", "cutoff/mask"),
        ("coefficients", "coefficient"),
        ("probability", "probability/tensor"),
        ("decision", "scientific decision"),
    ),
)
def test_independent_science_mutations_are_detected(monkeypatch, mutation, match):
    from . import _lane_comparison as lanes

    if mutation == "mask":
        monkeypatch.setattr(lanes.cutoff, "mask", lambda *args: ())
    elif mutation == "coefficients":
        monkeypatch.setattr(lanes.tensor, "objective", lambda *args: {})
    elif mutation == "probability":
        monkeypatch.setattr(lanes.cutoff, "probability", lambda *args: F(7))
    else:
        monkeypatch.setattr(lanes, "threshold_decision", lambda *args, **kwargs: False)
    with pytest.raises(AssertionError, match=match):
        lanes.compare(1, 1, (1, 0), F(1), "greater", F(0))


def test_packet_cli_and_exact_json_types(tmp_path, monkeypatch, capsys):
    import json
    import sys

    from . import _lane_comparison as lanes

    path = tmp_path / "qualification.json"
    monkeypatch.setattr(
        sys, "argv", ["lanes", "--max-total", "2", "--output", str(path)]
    )
    assert lanes.main() == 0
    monkeypatch.setattr(sys, "argv", ["lanes", "--verify", str(path)])
    assert lanes.main() == 0
    assert "replay passed" in capsys.readouterr().out
    packet = lanes.read_packet(path)
    packet["results"][0]["n1"] = True  # Python equality alone conflates True and 1.
    with pytest.raises(ValueError, match="replay mismatch"):
        lanes.verify_packet(packet)
    path.write_bytes(json.dumps(packet).encode())
    with pytest.raises(ValueError, match="noncanonical"):
        lanes.read_packet(path)
    path.write_bytes(b" " * 8_000_001)
    with pytest.raises(ValueError, match="byte limit"):
        lanes.read_packet(path)


@pytest.mark.parametrize(
    "packet",
    ({}, {"domain": None}, {"domain": {"positive_groups_total_at_most": True}}),
)
def test_malformed_qualification_domain_refuses(packet):
    from ._lane_comparison import verify_packet

    with pytest.raises(ValueError):
        verify_packet(packet)


def test_unsupported_shapes_and_reference_budgets_refuse():
    from . import _cutoff_cover_reference as cutoff
    from ._lane_comparison import qualification

    with pytest.raises(ValueError):
        qualification(7)
    with pytest.raises(ValueError):
        tensor.objective(0, 1, (), F(0))
    with pytest.raises(ValueError):
        tensor.objective(1, 1, ((1, 0), (1, 0)), F(0))
    with pytest.raises(ValueError):
        tensor.controls({(2, 0): F(1)}, (1, 1), (F(0), F(1), F(0), F(1)))
    with pytest.raises(ValueError):
        tensor.evaluate(((F(1),),), F(2), F(0))
    with pytest.raises(ValueError):
        tensor.decide_nuisance((F(1),), depth=13)
    with pytest.raises(ValueError):
        cutoff.mask(1, 1, (0, 0), F(0), "greater")
    with pytest.raises(ValueError):
        cutoff.probability(1, 1, (), F(1), F(-1))
