"""Generate the bounded topology reference; no production imports."""

from __future__ import annotations

import argparse
import hashlib
from dataclasses import asdict
from fractions import Fraction as F
from pathlib import Path

from tests.unconditional import _topology_replay as replay


def cases():
    def inputs(n1, n0, point, level, kind="topology"):
        return {
            "kind": kind,
            "n1": n1,
            "n0": n0,
            "observed": point,
            "level": level,
            "resource_profile": replay.PROFILE,
        }

    exact = {"kind": "exact_side_level", "value": F(1, 40)}
    decoded = {"kind": "public_alpha", "hex": (0.05).hex()}
    result = []
    for label, level in (("rational", exact), ("binary64", decoded)):
        for x in (0, 1):
            for y in (0, 1):
                result.append(
                    (f"one_trial_{label}_{x}{y}", inputs(1, 1, (x, y), level))
                )
    result.extend(
        [
            ("unequal_12", inputs(1, 2, (1, 0), exact)),
            ("unequal_21", inputs(2, 1, (0, 1), exact)),
            ("cubic_ordering_event", inputs(4, 4, (0, 2), exact, "ordering_anchor")),
        ]
    )
    return sorted(result)


def generate(directory):
    records = [replay.record(identity, inputs) for identity, inputs in cases()]
    packet = {
        "schema_version": replay.SCHEMA,
        "procedure_version": replay.PROCEDURE,
        "sources": {
            name: hashlib.sha256((replay.base.ROOT / name).read_bytes()).hexdigest()
            for name in replay.SOURCES
        },
        "specification_sha256": hashlib.sha256(
            (replay.base.ROOT / replay.base.SPEC_PATH).read_bytes()
        ).hexdigest(),
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "profile": asdict(replay.Limits()),
        "records": records,
    }
    manifest = {
        "schema_version": "exactcis.topology_manifest.v1",
        "packet_sha256": replay.base.digest("exactcis.topology.packet.v1", packet),
        "fixture_ids": [r["fixture_id"] for r in records],
    }
    directory.mkdir(parents=True, exist_ok=True)
    for name, data in ((replay.PACKET, packet), (replay.MANIFEST, manifest)):
        (directory / name).write_bytes(replay.base.canonical_bytes(data))
    return len(records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=replay.base.FIXTURE_DIRECTORY)
    args = parser.parse_args()
    print(f"Generated {generate(args.output)} topology/algebraic-event records")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
