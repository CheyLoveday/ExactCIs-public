"""Canonical reconstruction of bounded exact topology and algebraic events."""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict
from pathlib import Path

from . import _replay as base
from . import _topology as topology
from ._algebraic import Limits
from ._polynomial import OracleLimitError

SCHEMA = "exactcis.unconditional.topology_packet.v1"
PROCEDURE = "boschloo_or_u0_topology_reference_v1"
RECORD = "exactcis.unconditional.topology_record.v1"
PROFILE = "algebraic_reference_v1"
PACKET = "boschloo_topology_v1.json"
MANIFEST = "topology_manifest_v1.json"
GENERATOR = "tools/unconditional_oracle/generate_topology.py"
SOURCES = (
    *base.SOURCE_PATHS,
    "tests/unconditional/_algebraic.py",
    "tests/unconditional/_parametric.py",
    "tests/unconditional/_topology.py",
    "tests/unconditional/_topology_replay.py",
)
CLAIMS = {
    "topology": "exact_finite_oracle_topology_on_declared_input",
    "ordering_anchor": "exact_algebraic_event_mask_only",
}


def derive(inputs):
    base._keys(inputs, {"kind", "n1", "n0", "observed", "level", "resource_profile"})
    if inputs["resource_profile"] != PROFILE:
        raise ValueError("unknown topology resource profile")
    n1, n0, observed = base._table(inputs)
    level = base._level(inputs["level"])
    if inputs["kind"] == "topology":
        return topology.topology(n1, n0, observed, level)
    if inputs["kind"] == "ordering_anchor":
        if (n1, n0, observed) != (4, 4, (0, 2)) or level != base.Fraction(1, 40):
            raise ValueError("ordering anchor primitives changed")
        # U0's candidate (1,3), less direction, psi in (29/10,59/20).
        return topology.ordering_anchor()
    raise ValueError("unknown topology record kind")


def record(identity, inputs):
    inputs = base.encode(inputs)
    result = derive(inputs)
    return {
        "fixture_id": identity,
        "schema_version": RECORD,
        "procedure_version": PROCEDURE,
        "orientation": base.ORIENTATION,
        "claim_ceiling": CLAIMS[inputs["kind"]],
        "inputs": inputs,
        "input_sha256": base.digest("exactcis.topology.input.v1", inputs),
        "derived": result,
        "output_sha256": base.digest("exactcis.topology.output.v1", result),
    }


def verify(packet_bytes, manifest_bytes, *, root=base.ROOT):
    if len(packet_bytes) > 8_000_000 or len(manifest_bytes) > 64_000:
        raise OracleLimitError("topology packet byte budget exceeded")
    packet, manifest = json.loads(packet_bytes), json.loads(manifest_bytes)
    if (
        base.canonical_bytes(packet) != packet_bytes
        or base.canonical_bytes(manifest) != manifest_bytes
    ):
        raise ValueError("noncanonical topology JSON")
    base._keys(
        packet,
        {
            "schema_version",
            "procedure_version",
            "sources",
            "specification_sha256",
            "generator_sha256",
            "profile",
            "records",
        },
    )
    base._keys(manifest, {"schema_version", "packet_sha256", "fixture_ids"})
    if packet["schema_version"] != SCHEMA or packet["procedure_version"] != PROCEDURE:
        raise ValueError("unknown topology version")
    if manifest["schema_version"] != "exactcis.topology_manifest.v1":
        raise ValueError("unknown topology manifest")
    if manifest["packet_sha256"] != base.digest("exactcis.topology.packet.v1", packet):
        raise ValueError("topology packet hash mismatch")
    if base.canonical_bytes(packet["profile"]) != base.canonical_bytes(
        asdict(Limits())
    ):
        raise ValueError("topology profile differs from the recorded implementation")
    expected_sources = {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in SOURCES
    }
    if packet["sources"] != expected_sources:
        raise ValueError("topology source hash mismatch")
    if (
        packet["specification_sha256"]
        != hashlib.sha256((root / base.SPEC_PATH).read_bytes()).hexdigest()
    ):
        raise ValueError("topology specification hash mismatch")
    gh = packet["generator_sha256"]
    if (
        not isinstance(gh, str)
        or len(gh) != 64
        or any(c not in "0123456789abcdef" for c in gh)
    ):
        raise ValueError("invalid topology generator hash")
    generator_present = (root / GENERATOR).is_file()
    if (
        generator_present
        and hashlib.sha256((root / GENERATOR).read_bytes()).hexdigest() != gh
    ):
        raise ValueError("topology generator hash mismatch")
    records = packet["records"]
    if not isinstance(records, list) or not 1 <= len(records) <= 64:
        raise ValueError("topology record count outside profile")
    ids = []
    for item in records:
        base._keys(
            item,
            {
                "fixture_id",
                "schema_version",
                "procedure_version",
                "orientation",
                "claim_ceiling",
                "inputs",
                "input_sha256",
                "derived",
                "output_sha256",
            },
        )
        identity = item["fixture_id"]
        if (
            not isinstance(identity, str)
            or base.re.fullmatch(r"[a-z][a-z0-9_]{0,79}", identity) is None
        ):
            raise ValueError("invalid topology fixture identity")
        ids.append(identity)
        if (item["schema_version"], item["procedure_version"], item["orientation"]) != (
            RECORD,
            PROCEDURE,
            base.ORIENTATION,
        ):
            raise ValueError("topology record identity mismatch")
        inputs = item["inputs"]
        if (
            not isinstance(inputs, dict)
            or not isinstance(inputs.get("kind"), str)
            or inputs["kind"] not in CLAIMS
        ):
            raise ValueError("unknown topology record input")
        if item["claim_ceiling"] != CLAIMS[inputs["kind"]]:
            raise ValueError("topology claim ceiling mismatch")
        if item["input_sha256"] != base.digest("exactcis.topology.input.v1", inputs):
            raise ValueError("topology input hash mismatch")
        if item["output_sha256"] != base.digest(
            "exactcis.topology.output.v1", item["derived"]
        ):
            raise ValueError("topology output hash mismatch")
        if base.canonical_bytes(derive(inputs)) != base.canonical_bytes(
            item["derived"]
        ):
            raise ValueError("topology scientific replay mismatch")
    if ids != sorted(set(ids)) or ids != manifest["fixture_ids"]:
        raise ValueError("topology fixture identity/order mismatch")
    return {
        "records_replayed": len(records),
        "generator_source_checked": generator_present,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, default=base.FIXTURE_DIRECTORY)
    args = parser.parse_args()
    print(
        json.dumps(
            verify(
                (args.directory / PACKET).read_bytes(),
                (args.directory / MANIFEST).read_bytes(),
            ),
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
