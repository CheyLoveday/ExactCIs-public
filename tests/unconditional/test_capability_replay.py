"""Scientific reconstruction defeats rehashed measurement corruption."""

import copy
import json

import pytest

from . import _capability_replay as replay
from . import _replay as base


@pytest.fixture
def packet():
    return json.loads(
        (base.FIXTURE_DIRECTORY / "capability_measurement_v1.json").read_bytes()
    )


def reseal(packet):
    for row in packet["results"]:
        row["record_sha256"] = base.digest(
            "exactcis.capability.record.v1",
            {key: value for key, value in row.items() if key != "record_sha256"},
        )
    packet["measurement_sha256"] = base.digest(
        "exactcis.capability.measurement.v1",
        {key: value for key, value in packet.items() if key != "measurement_sha256"},
    )
    return base.canonical_bytes(packet)


def timeout_row(packet):
    row = copy.deepcopy(packet["results"][0])
    for field in (
        "topology",
        "topology_sha256",
        "cell_comparisons",
        "topology_elapsed_ns",
        "lanes_elapsed_ns",
    ):
        row.pop(field, None)
    row.update(
        status="topology_timeout",
        counts=None,
        peak_rss_bytes=None,
        reason="controlled interruption before the first checkpoint",
    )
    return row


@pytest.mark.parametrize(
    "mutation", ["topology", "lanes", "counts", "false_refusal", "profile"]
)
def test_rehashed_scientific_measurement_corruption_refuses(packet, mutation):
    row = packet["results"][0]
    assert row["status"] == "complete"
    if mutation == "topology":
        row["topology"]["full"] = not row["topology"]["full"]
    elif mutation == "lanes":
        cell = row["cell_comparisons"][0]
        cell["tensor"]["decision"] = not cell["tensor"]["decision"]
    elif mutation == "counts":
        row["counts"]["add"] = True
    elif mutation == "false_refusal":
        row.update(status="resource_refused", reason="forged failure")
    else:
        row["profile"]["max_degree"] += 1
    with pytest.raises(ValueError):
        replay.verify(reseal(packet))


@pytest.mark.parametrize(
    "mutation",
    [
        "version",
        "source",
        "source_set",
        "domain",
        "omission",
        "primitive",
        "record_hash",
        "packet_hash",
    ],
)
def test_malformed_measurement_identity_refuses(packet, mutation):
    if mutation == "version":
        packet["procedure_version"] = "unknown"
    elif mutation == "source":
        packet["sources"]["tests/unconditional/_cell_lanes.py"] = "0" * 64
    elif mutation == "source_set":
        packet["sources"]["unexpected.py"] = "0" * 64
    elif mutation == "domain":
        packet["domain"]["positive_groups_total_at_most"] = True
    elif mutation == "omission":
        packet["results"].pop()
    elif mutation == "primitive":
        packet["results"][0]["inputs"]["n1"] = True
    raw = reseal(packet)
    if mutation in ("record_hash", "packet_hash"):
        if mutation == "record_hash":
            packet["results"][0]["record_sha256"] = "0" * 64
            packet["measurement_sha256"] = base.digest(
                "exactcis.capability.measurement.v1",
                {
                    key: value
                    for key, value in packet.items()
                    if key != "measurement_sha256"
                },
            )
        else:
            packet["measurement_sha256"] = "0" * 64
        raw = base.canonical_bytes(packet)
    with pytest.raises(ValueError):
        replay.verify(raw)


def test_packet_byte_and_canonical_limits_precede_science(packet):
    with pytest.raises(ValueError, match="byte limit"):
        replay.verify(b" " * 8_000_001)
    with pytest.raises(ValueError, match="noncanonical"):
        replay.verify(b" " + base.canonical_bytes(packet))


@pytest.mark.parametrize(
    "field",
    [
        "topology",
        "topology_sha256",
        "cell_comparisons",
        "topology_elapsed_ns",
        "lanes_elapsed_ns",
    ],
)
def test_wall_timeout_never_claims_an_unavailable_scientific_stage(packet, field):
    row = timeout_row(packet)
    replay.verify_record(row)
    row[field] = []
    with pytest.raises(ValueError, match="unavailable"):
        replay.verify_record(row)


def test_small_completed_record_reconstructs_including_lane_timeout_checkpoint(packet):
    row = packet["results"][0]
    replay.verify_record(row)
    row["status"] = "lane_timeout"
    replay.verify_record(row)


def test_actual_refusal_is_reconstructed_and_cannot_be_relabelled(packet):
    row = next(row for row in packet["results"] if row["status"] == "resource_refused")
    replay.verify_record(row)
    row["reason"] = "forged refusal reason"
    with pytest.raises(ValueError, match="refusal replay"):
        replay.verify_record(row)


def test_rehashed_timeout_cannot_smuggle_unreplayed_cell_output(packet):
    row = timeout_row(packet)
    packet["results"][0] = row
    row["cell_comparisons"] = [{"projected_event": True, "tensor": {"decision": False}}]
    with pytest.raises(ValueError, match="unavailable"):
        replay.verify(reseal(packet))


@pytest.mark.parametrize(
    "field", ["topology", "topology_sha256", "cell_comparisons", "lanes_elapsed_ns"]
)
def test_refusal_cannot_claim_unreplayed_completed_outputs(packet, field):
    row = next(row for row in packet["results"] if row["status"] == "resource_refused")
    row[field] = []
    with pytest.raises(ValueError, match="unavailable"):
        replay.verify_record(row)
