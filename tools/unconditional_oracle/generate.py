"""Generate the bounded U1 fixed-null packet from public U0 primitive inputs.

Run from the repository root with ``python -m tools.unconditional_oracle.generate``.
This generator is repository-only; exact replay lives in the sdist's tests.
"""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction as F
from pathlib import Path

from tests.unconditional import _replay as replay


def primitive_cases() -> list[tuple[str, dict]]:
    def finite(n1, n0, observed, psi, direction, level):
        return {
            "kind": "fixed_null",
            "n1": n1,
            "n0": n0,
            "observed": observed,
            "effect": {"kind": "finite", "beta": psi, "s": psi / (1 + psi)},
            "direction": direction,
            "level": {"kind": "exact_side_level", "value": level},
        }

    cases = []
    tangent = F(108, 3125)
    for suffix, delta in (
        ("equal", F(0)),
        ("below", -F(1, 10**12)),
        ("above", F(1, 10**12)),
    ):
        cases.append(
            (
                f"tangency_{suffix}",
                finite(2, 3, (2, 0), F(1), "greater", tangent + delta),
            )
        )
    for i, effect in enumerate((F(23, 9), F(47, 17), F(3), F(25, 7))):
        cases.append(
            (f"disconnected_{i}", finite(4, 4, (0, 2), effect, "less", F(1, 40)))
        )
    cases.append(
        ("multiple_maxima", finite(2, 4, (1, 0), F(1, 4), "greater", F(1, 20)))
    )
    cases.append(("full_mask", finite(2, 3, (0, 0), F(2), "greater", F(1, 20))))
    cases.append(("zero_threshold", finite(2, 3, (0, 0), F(2), "greater", F(1))))
    cases.append(("alpha_zero", finite(2, 3, (1, 0), F(2), "greater", F(0))))
    decoded = finite(2, 3, (1, 0), F(2), "greater", F(1, 40))
    decoded["level"] = {"kind": "public_alpha", "hex": (0.05).hex()}
    cases.append(("decoded_alpha_unequal_groups", decoded))
    for endpoint in ("zero", "infinity"):
        for name, observed in (("supported", (0, 0)), ("unsupported", (1, 1))):
            for label, level in (("zero", F(0)), ("positive", F(1, 40))):
                cases.append(
                    (
                        f"structural_{endpoint}_{name}_{label}",
                        {
                            "kind": "structural",
                            "n1": 2,
                            "n0": 3,
                            "observed": observed,
                            "effect": {
                                "kind": endpoint,
                                "s": F(int(endpoint == "infinity")),
                            },
                            "level": {"kind": "exact_side_level", "value": level},
                        },
                    )
                )
    cases.append(
        (
            "ordering_breakpoint",
            {
                "kind": "ordering_event",
                "n1": 4,
                "n0": 4,
                "observed": (0, 2),
                "candidate": (1, 3),
                "direction": "less",
                "isolator": (F(29, 10), F(59, 20)),
            },
        )
    )
    return sorted(cases)


def generate(directory: Path) -> tuple[bytes, bytes]:
    records = [replay.make_record(name, inputs) for name, inputs in primitive_cases()]
    packet = {
        "schema_version": replay.SCHEMA_VERSION,
        "procedure_version": replay.PROCEDURE_VERSION,
        "scope": "U1_fixed_rational_null_and_ordering_bracket_diagnostics",
        "sources": replay.source_hashes(),
        "specification_sha256": hashlib.sha256(
            (replay.ROOT / replay.SPEC_PATH).read_bytes()
        ).hexdigest(),
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "records": records,
    }
    manifest = {
        "schema_version": "exactcis.unconditional.oracle_manifest.v1",
        "packet_sha256": replay.digest("exactcis.oracle.packet.v1", packet),
        "fixture_ids": [record["fixture_id"] for record in records],
    }
    data, manifest_data = (
        replay.canonical_bytes(packet),
        replay.canonical_bytes(manifest),
    )
    replay.verify_packet(data, manifest_data)
    directory.mkdir(parents=True, exist_ok=True)
    (directory / replay.PACKET_NAME).write_bytes(data)
    (directory / replay.MANIFEST_NAME).write_bytes(manifest_data)
    return data, manifest_data


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=replay.FIXTURE_DIRECTORY)
    args = parser.parse_args()
    data, _ = generate(args.output)
    print(
        f"Generated {len(primitive_cases())} exact diagnostic records "
        f"({len(data)} bytes)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
