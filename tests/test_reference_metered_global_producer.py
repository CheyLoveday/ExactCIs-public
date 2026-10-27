from __future__ import annotations

import json
import sys
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path

# The existing schema-validation dependency does not distribute typing stubs.
import jsonschema  # type: ignore[import-untyped]
import pytest

REFERENCE_ROOT = Path(__file__).resolve().parents[1] / "formal"
pytestmark = pytest.mark.skipif(
    not REFERENCE_ROOT.is_dir(), reason="repository-only checked reference"
)
if REFERENCE_ROOT.is_dir():
    sys.path.insert(0, str(REFERENCE_ROOT / "tools"))
    import metered_algebraic as a
    import metered_global_producer as producer
    import metered_polynomial as p
    import metered_root as r
    import metered_specialized as specialized
    import resource_model as v

if REFERENCE_ROOT.is_dir():
    SCHEMA = json.loads((REFERENCE_ROOT / "global-checker-v1.schema.json").read_text())


def test_constructs_full_candidate_with_actual_open_decisions() -> None:
    m = r.Meter()
    candidate = producer.generate((0, 1, 0, 1), Q(1, 10), Q(0), m)
    assert candidate.payload["terminal"] == {"kind": "FULL_CERTIFIED"}
    assert candidate.payload["openLeaves"][0]["state"] == "ACCEPTED"
    assert len(candidate.payload["rootCovers"]) == 2
    assert len(candidate.checkpoints) == 8
    jsonschema.validate(
        {"input": candidate.input, "payload": candidate.payload}, SCHEMA
    )


def test_canonical_serialization_has_actual_prepaid_byte_counts() -> None:
    m = r.Meter()
    candidate = producer.generate((0, 1, 0, 1), Q(1, 10), Q(0), m)
    first = producer.serialize(candidate, m)
    assert json.loads(first.input_bytes) == candidate.input
    assert json.loads(first.payload_bytes) == candidate.payload
    assert first.input_bytes == json.dumps(
        candidate.input, separators=(",", ":")
    ).encode("ascii")
    assert first.payload_bytes == json.dumps(
        candidate.payload, separators=(",", ":")
    ).encode("ascii")
    assert (
        first.construction_and_serialization.resources.used.certificate_bytes
        == 2 * (len(first.input_bytes) + len(first.payload_bytes))
    )


def test_failed_output_charge_precedes_the_next_output_allocation() -> None:
    m = r.Meter()
    candidate = producer.generate((0, 1, 0, 1), Q(1, 10), Q(0), m)
    profile = replace(
        v.DEVELOPMENT, limits=replace(v.DEVELOPMENT.limits, certificate_bytes=1)
    )
    tight = r.Meter(r.Limits(profile=profile))
    with pytest.raises(v.ResourceRefusal) as refused:
        producer.serialize(candidate, tight)
    assert refused.value.previous.used.certificate_bytes <= 1


def test_input_error_cannot_return_a_partial_candidate() -> None:
    with pytest.raises(r.InvalidWitness, match="group totals"):
        producer.generate((0, 0, 1, 1), Q(1, 10), Q(1, 100), r.Meter())


def test_family_product_retains_exact_signed_unit_and_multiplicity() -> None:
    left, right = (Q(-1, 3), Q(1)), (Q(1, 3), Q(-1))
    points = producer._family_roots((left, right), r.Meter())
    assert len(points) == 1
    assert isinstance(points[0], a.Root)
    expected = p.mul(left, right, r.Meter())
    assert points[0].definer == expected
    assert points[0].certificate.exponent == 2


def test_merged_family_keeps_one_exact_root_for_opposite_signed_members() -> None:
    left, right = (Q(-1, 3), Q(1)), (Q(1, 3), Q(-1))
    points = producer._merged_family_roots((left, right), r.Meter())
    assert len(points) == 1
    point = points[0]
    if isinstance(point, Q):
        assert point == Q(1, 3)
    else:
        assert point.lower < Q(1, 3) < point.upper
        assert p.value(point.definer, Q(1, 3), r.Meter()) == 0


def test_merged_route_produces_a_full_candidate_without_the_family_product() -> None:
    m = r.Meter()
    candidate = producer.generate(
        (0, 1, 0, 1), Q(1, 10), Q(0), m, isolation_strategy="merge"
    )
    assert candidate.payload["terminal"] == {"kind": "FULL_CERTIFIED"}
    jsonschema.validate(
        {"input": candidate.input, "payload": candidate.payload}, SCHEMA
    )


def test_unknown_root_route_is_refused_before_candidate_construction() -> None:
    with pytest.raises(r.InvalidWitness, match="unknown family"):
        producer.generate(
            (0, 1, 0, 1), Q(1, 10), Q(0), r.Meter(), isolation_strategy="unknown"
        )


def test_modular_wire_witnesses_are_canonical_without_changing_typed_width() -> None:
    m = r.Meter()
    d = (Q(-1, 2), Q(0), Q(1))
    selected = a.Root(d, Q(1, 2), Q(1), r.generate_witness_with_meter(d, m))
    h = ((Q(0), Q(-1)), (), (Q(1),))
    localized, certificate = specialized.generate(h, selected, m)
    raw_derivative = certificate.derivative_witness
    wire = producer._specialized_wire(certificate, m)
    for witness in (
        wire["rootWitness"],
        wire["powerWitness"],
        wire["bezoutWitness"],
        wire["derivativeWitness"],
        *wire["witnesses"],
    ):
        assert not witness or witness[-1]
    assert len(wire["derivativeWitness"]) < len(raw_derivative)
    assert certificate.derivative_witness == raw_derivative
    specialized.replay(h, localized, certificate, m)
