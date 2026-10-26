"""Compare independent tensor, cutoff/witness and projected-event references.

The corpus is explicit and finite. Each lane's inconclusion or resource refusal
is retained. The packet establishes no general completeness or production cap.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict
from fractions import Fraction as F
from pathlib import Path

from tests.unconditional import _cutoff_cover_reference as cutoff
from tests.unconditional import _oracle as oracle
from tests.unconditional import _replay as replay
from tests.unconditional import _tensor_reference as tensor
from tests.unconditional import _topology as projected
from tests.unconditional._algebraic import Work
from tests.unconditional._polynomial import (
    DEFAULT_LIMITS,
    OracleLimitError,
    OracleLimits,
    threshold_decision,
)

ROOT = Path(__file__).resolve().parents[2]
SOURCES = (
    "tests/__init__.py",
    "tests/unconditional/__init__.py",
    "docs_md/unconditional_exact_specification.md",
    "tests/unconditional/_algebraic.py",
    "tests/unconditional/_parametric.py",
    "tests/unconditional/_tensor_reference.py",
    "tests/unconditional/_cutoff_cover_reference.py",
    "tests/unconditional/_oracle.py",
    "tests/unconditional/_polynomial.py",
    "tests/unconditional/_replay.py",
    "tests/unconditional/_topology.py",
    "tests/unconditional/_lane_comparison.py",
)
SCHEMA = "exactcis.three_lane_qualification.v1"
PROCEDURE = "boschloo_three_lane_reference_v1"


def _status(answer: bool | None) -> str:
    return (
        "accepted"
        if answer is True
        else "rejected"
        if answer is False
        else "inconclusive"
    )


def compare(
    n1: int,
    n0: int,
    observed: tuple[int, int],
    psi: F,
    direction: str,
    level: F,
    *,
    polynomial_limits: OracleLimits = DEFAULT_LIMITS,
) -> dict:
    selected = cutoff.mask(n1, n0, observed, psi, direction)
    if selected != oracle.rejection_mask(n1, n0, observed, psi, direction):
        raise AssertionError("independent cutoff/mask disagreement")
    power = tensor.objective(n1, n0, selected, level)
    h = projected.threshold(n1, n0, selected, level, Work())
    projected_power = {
        (i, j): coefficient
        for j, row in enumerate(h)
        for i, coefficient in enumerate(row)
        if coefficient
    }
    if power != projected_power:
        raise AssertionError("independent tensor/projected coefficient disagreement")
    grid = tensor.controls(power, (n1, n1 + n0), (F(0), F(1), F(0), F(1)))
    s = psi / (1 + psi)
    values = tensor.slice_effect(grid, s)

    # Exact coefficient equality plus independent evaluation tests both coordinate
    # clearing and the Bernstein basis. This is a fixed-mask identity.
    def denominator(q: F) -> F:
        return ((1 - s) * (1 - q) + s * q) ** n1

    for q in (F(0), F(2, 7), F(1)):
        direct = (cutoff.probability(n1, n0, selected, psi, q) - level) * denominator(q)
        if tensor.evaluate(grid, s, q) != direct:
            raise AssertionError("independent probability/tensor disagreement")
    ta, visits = tensor.decide_nuisance(values)
    ca = cutoff.decide(n1, n0, observed, psi, direction, level)
    row = {
        "n1": n1,
        "n0": n0,
        "observed": list(observed),
        "schema_version": "exactcis.three_lane_record.v1",
        "procedure_version": PROCEDURE,
        "effect": replay.encode(psi),
        "compact_effect": replay.encode(s),
        "direction": direction,
        "alpha": replay.encode(2 * level),
        "side_level": replay.encode(level),
        "mask": replay.encode(selected),
        "power_coefficients": replay.encode(
            [[i, j, coefficient] for (i, j), coefficient in sorted(power.items())]
        ),
        "tensor": _status(ta),
        "tensor_nodes": visits,
        "cutoff_cover": _status(ca),
        "mask_size": len(selected),
        "nonzero_power_coefficients": len(power),
        "projected_profile": asdict(polynomial_limits),
    }
    try:
        pa = threshold_decision(
            oracle.threshold_coefficients(n1, n0, selected, psi, level),
            limits=polynomial_limits,
        )
    except OracleLimitError as error:
        row["projected_event"] = "resource_refused"
        row["refusal"] = str(error)
    else:
        row["projected_event"] = _status(pa)
        if (ta is not None and ta != pa) or (ca is not None and ca != pa):
            raise AssertionError("scientific decision disagreement")
    row["input_sha256"] = replay.digest(
        "exactcis.three_lane.input.v1",
        {
            name: row[name]
            for name in (
                "n1",
                "n0",
                "observed",
                "effect",
                "compact_effect",
                "direction",
                "alpha",
                "side_level",
                "projected_profile",
            )
        },
    )
    row["output_sha256"] = replay.digest("exactcis.three_lane.output.v1", row)
    return row


def qualification(max_total: int = 4) -> dict:
    if type(max_total) is not int or max_total not in (2, 3, 4, 5, 6):
        raise ValueError("declared qualification total must be 2 through 6")
    cases = [
        (n1, total - n1, (x, y))
        for total in range(2, max_total + 1)
        for n1 in range(1, total)
        for x in range(n1 + 1)
        for y in range(total - n1 + 1)
    ]
    cases.append((4, 4, (0, 2)))
    rows = [
        compare(n1, n0, observed, psi, direction, level)
        for n1, n0, observed in cases
        for psi in (F(1, 3), F(1), F(7, 3))
        for direction in ("greater", "less")
        for level in (
            (F(0), F(1, 40), F(1, 2))
            if n1 + n0 <= 4 or (n1, n0) == (4, 4)
            else (F(1, 40),)
        )
    ]
    return {
        "schema_version": SCHEMA,
        "procedure_version": PROCEDURE,
        "scope": (
            "finite fixed-null identities and sound supported decisions; "
            "no global completeness"
        ),
        "domain": {"positive_groups_total_at_most": max_total, "extra": [4, 4, 0, 2]},
        "tensor_refinement_depth": 4,
        "inconclusion": (
            "bounded witness/Bernstein criterion did not certify a decision"
        ),
        "units": {
            "tensor_nodes": "visited nuisance Bernstein nodes, not Fraction operations"
        },
        "sources": {
            name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in SOURCES
        },
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "specification_sha256": hashlib.sha256(
            (ROOT / "docs_md/unconditional_exact_specification.md").read_bytes()
        ).hexdigest(),
        "results": rows,
        "inputs_sha256": replay.digest(
            "exactcis.three_lane.inputs.v1", [row["input_sha256"] for row in rows]
        ),
        "outputs_sha256": replay.digest("exactcis.three_lane.outputs.v1", rows),
    }


def verify_packet(packet: dict) -> None:
    try:
        total = packet["domain"]["positive_groups_total_at_most"]
    except (KeyError, TypeError) as error:
        raise ValueError("malformed qualification domain") from error
    if type(total) is not int or total not in (2, 3, 4, 5, 6):
        raise ValueError("unsupported qualification domain")
    if canonical_bytes(packet) != canonical_bytes(qualification(total)):
        raise ValueError("qualification identity or scientific replay mismatch")


def canonical_bytes(payload: object) -> bytes:
    return replay.canonical_bytes(payload)


def read_packet(path: Path) -> dict:
    with path.open("rb") as stream:
        raw = stream.read(8_000_001)
    if len(raw) > 8_000_000:
        raise ValueError("qualification packet byte limit exceeded")
    packet = json.loads(raw)
    if raw != canonical_bytes(packet):
        raise ValueError("noncanonical qualification JSON")
    return packet


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-total", type=int, choices=(2, 3, 4, 5, 6), default=6)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--verify", type=Path)
    args = parser.parse_args()
    if args.verify is not None:
        verify_packet(read_packet(args.verify))
        print("Finite three-lane packet replay passed")
    else:
        args.output.write_bytes(canonical_bytes(qualification(args.max_total)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
