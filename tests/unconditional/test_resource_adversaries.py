"""Retained real refusals and deterministic diagnostic attempt denominator."""

import json
from pathlib import Path

from ._replay import canonical_bytes, digest


def test_all_declared_capability_attempts_are_retained():
    raw = (
        Path(__file__).parents[1]
        / "references/unconditional/capability_measurement_v1.json"
    ).read_bytes()
    packet = json.loads(raw)
    assert raw == canonical_bytes(packet)
    expected = [
        (n1, total - n1, [x, y])
        for total in range(2, 7)
        for n1 in range(1, total)
        for x in range(n1 + 1)
        for y in range(total - n1 + 1)
    ] + [(4, 4, [0, 2])]
    rows = packet["results"]
    assert packet["measurement_sha256"] == digest(
        "exactcis.capability.measurement.v1",
        {key: value for key, value in packet.items() if key != "measurement_sha256"},
    )
    assert [
        (row["inputs"]["n1"], row["inputs"]["n0"], row["inputs"]["observed"])
        for row in rows
    ] == expected
    assert len(rows) == 156
    for row in rows:
        assert row["input_sha256"] == digest(
            "exactcis.capability.input.v1", row["inputs"]
        )
        assert row["record_sha256"] == digest(
            "exactcis.capability.record.v1",
            {key: value for key, value in row.items() if key != "record_sha256"},
        )
        assert row["status"] in (
            "complete",
            "resource_refused",
            "topology_timeout",
            "lane_timeout",
        )
        assert row["attempt_elapsed_ns"] > 0
        if row["status"] != "complete":
            assert row["reason"]
        if row["status"] == "complete":
            assert row["topology"]["events"]
            for comparison in row["cell_comparisons"]:
                for name in ("tensor", "cutoff_cover"):
                    answer = comparison[name]["decision"]
                    assert answer is None or answer == comparison["projected_event"]
