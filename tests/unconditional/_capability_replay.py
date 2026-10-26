"""Reconstruct every completed scientific stage of the capability measurement.

Wall time and RSS are observations, not reproducible scientific answers. Named
wall timeouts are retained without pretending to replay their scheduling.
Completed topology/lane outputs and exact work refusals are reconstructed.
This module works without repository-only generation tools in an sdist.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict
from fractions import Fraction as F
from pathlib import Path

from . import _cell_lanes as lanes
from . import _replay as base
from . import _topology as topology
from ._algebraic import Limits, Work
from ._polynomial import OracleLimitError
from ._topology_replay import SOURCES as TOPOLOGY_SOURCES

SOURCES = (
    *TOPOLOGY_SOURCES,
    "tests/unconditional/_tensor_reference.py",
    "tests/unconditional/_cell_lanes.py",
    "tools/unconditional_oracle/measure_capability.py",
)


def verify_record(row):
    inputs = row["inputs"]
    n1, n0, observed = inputs["n1"], inputs["n0"], tuple(inputs["observed"])
    profile = (
        Limits(max_calls=500_000, max_degree=128) if (n1, n0) == (4, 4) else Limits()
    )
    if row["status"] == "topology_timeout":
        if (
            row["counts"] is not None
            or row["peak_rss_bytes"] is not None
            or "topology" in row
        ):
            raise ValueError("topology timeout claims an unavailable completed stage")
        return
    if base.canonical_bytes(row["profile"]) != base.canonical_bytes(asdict(profile)):
        raise ValueError("unknown measurement profile")
    work = Work(profile)
    try:
        result = topology.topology(n1, n0, observed, F(1, 40), work=work)
    except OracleLimitError as error:
        if (
            row["status"] != "resource_refused"
            or row["reason"] != str(error)
            or base.canonical_bytes(row["counts"]) != base.canonical_bytes(work.counts)
        ):
            raise ValueError("resource refusal replay mismatch") from error
        return
    if row["status"] not in ("complete", "lane_timeout"):
        raise ValueError("completed topology mislabeled as refusal")
    summary = {
        key: result[key]
        for key in ("events", "components", "ideal_hull", "empty", "full")
    }
    summary["leaves"] = [
        {
            key: leaf[key]
            for key in (
                "kind",
                "left_event",
                "right_event",
                "accepted",
                "masks",
                "pair",
            )
            if key in leaf
        }
        for leaf in result["leaves"]
    ]
    if (
        row["topology_sha256"] != base.digest("exactcis.topology.output.v4", result)
        or base.canonical_bytes(row["topology"]) != base.canonical_bytes(summary)
        or base.canonical_bytes(row["counts"]) != base.canonical_bytes(work.counts)
    ):
        raise ValueError("topology scientific replay mismatch")
    if row["status"] == "complete" or "cell_comparisons" in row:
        expected = lanes.compare_cells(n1, n0, observed, F(1, 40), result)
        if base.canonical_bytes(row["cell_comparisons"]) != base.canonical_bytes(
            expected
        ):
            raise ValueError("whole-cell scientific replay mismatch")


def verify(raw, *, root=base.ROOT):
    if len(raw) > 8_000_000:
        raise ValueError("measurement packet byte limit")
    packet = json.loads(raw)
    if raw != base.canonical_bytes(packet):
        raise ValueError("noncanonical measurement JSON")
    if (
        packet["schema_version"] != "exactcis.capability_measurement.v1"
        or packet["procedure_version"] != "boschloo_three_lane_cell_measurement_v1"
    ):
        raise ValueError("unknown measurement version")
    payload = {
        key: value for key, value in packet.items() if key != "measurement_sha256"
    }
    if packet["measurement_sha256"] != base.digest(
        "exactcis.capability.measurement.v1", payload
    ):
        raise ValueError("measurement packet digest mismatch")
    if set(packet["sources"]) != set(SOURCES):
        raise ValueError("measurement source set mismatch")
    for name, digest in packet["sources"].items():
        if (
            not isinstance(digest, str)
            or len(digest) != 64
            or any(c not in "0123456789abcdef" for c in digest)
        ):
            raise ValueError("invalid measurement source hash")
        path = root / name
        if name.startswith("tools/") and not path.is_file():
            continue
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError("measurement source identity mismatch")
    total = packet["domain"]["positive_groups_total_at_most"]
    if (
        type(total) is not int
        or not 2 <= total <= 6
        or packet["domain"]["extra"] != [4, 4, 0, 2]
    ):
        raise ValueError("unsupported measurement domain")
    cases = [
        (n1, size - n1, [x, y])
        for size in range(2, total + 1)
        for n1 in range(1, size)
        for x in range(n1 + 1)
        for y in range(size - n1 + 1)
    ] + [(4, 4, [0, 2])]
    if len(cases) != len(packet["results"]):
        raise ValueError("measurement attempt omission")
    for (n1, n0, observed), row in zip(cases, packet["results"]):
        inputs = {
            "n1": n1,
            "n0": n0,
            "observed": observed,
            "side_level": F(1, 40),
            "alpha": F(1, 20),
        }
        if base.canonical_bytes(row["inputs"]) != base.canonical_bytes(inputs) or row[
            "input_sha256"
        ] != base.digest("exactcis.capability.input.v1", inputs):
            raise ValueError("measurement primitive input mismatch")
        if row["record_sha256"] != base.digest(
            "exactcis.capability.record.v1",
            {key: value for key, value in row.items() if key != "record_sha256"},
        ):
            raise ValueError("measurement record digest mismatch")
        if row["status"] not in (
            "complete",
            "resource_refused",
            "topology_timeout",
            "lane_timeout",
        ):
            raise ValueError("unknown measurement outcome")
        verify_record(row)
    return len(cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--packet",
        type=Path,
        default=base.FIXTURE_DIRECTORY / "capability_measurement_v1.json",
    )
    args = parser.parse_args()
    with args.packet.open("rb") as stream:
        raw = stream.read(8_000_001)
    count = verify(raw)
    print(
        f"Scientific stages replayed for {count} retained attempts; "
        "wall scheduling not replayed"
    )


if __name__ == "__main__":
    main()
