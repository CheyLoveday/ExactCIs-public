"""Canonical, independently reconstructed small-table Boschloo oracle records.

This is reference tooling, not a production kernel or a global topology oracle.
Scientific rationals use reduced decimal numerator/denominator strings. Digests
bind canonical UTF-8 JSON (sorted keys, compact separators, terminal newline)
to explicit domains. Source hashes are ordinary SHA-256 of exact source bytes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import asdict
from fractions import Fraction
from pathlib import Path
from typing import Any

from . import _oracle as oracle
from . import _polynomial as polynomial

SCHEMA_VERSION = "exactcis.unconditional.oracle_packet.v1"
RECORD_VERSION = "exactcis.unconditional.oracle_record.v1"
PROCEDURE_VERSION = "boschloo_or_u0_v2"
CLAIM_CEILING = "finite_diagnostic"
ORIENTATION = "a b / c d; n1=a+b; n0=c+d; observed=(a,c)"
ROOT = Path(__file__).resolve().parents[2]
SPEC_PATH = "docs_md/unconditional_exact_specification.md"
SOURCE_PATHS = (
    "tests/__init__.py",
    "tests/unconditional/__init__.py",
    "tests/unconditional/_oracle.py",
    "tests/unconditional/_polynomial.py",
    "tests/unconditional/_replay.py",
)
GENERATOR_PATH = "tools/unconditional_oracle/generate.py"
FIXTURE_DIRECTORY = ROOT / "tests/references/unconditional"
PACKET_NAME = "boschloo_fixed_null_v1.json"
MANIFEST_NAME = "manifest_v1.json"


def encode(value: Any) -> Any:
    if isinstance(value, Fraction):
        return {"num": str(value.numerator), "den": str(value.denominator)}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    if isinstance(value, dict):
        if any(type(key) is not str for key in value):
            raise ValueError("JSON object keys must be strings")
        return {key: encode(item) for key, item in value.items()}
    if value is None or type(value) in (str, bool, int):
        return value
    raise ValueError("scientific floats and non-JSON values are forbidden")


def canonical_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            encode(value), sort_keys=True, separators=(",", ":"), allow_nan=False
        )
        + "\n"
    ).encode("utf-8")


def digest(domain: str, value: Any) -> str:
    return hashlib.sha256(
        domain.encode("ascii") + b"\0" + canonical_bytes(value)
    ).hexdigest()


def rational(value: Any) -> Fraction:
    if not isinstance(value, dict) or set(value) != {"num", "den"}:
        raise ValueError("rational requires exactly num and den")
    num, den = value["num"], value["den"]
    if not isinstance(num, str) or not isinstance(den, str):
        raise ValueError("rational integers must be decimal strings")
    if len(num) > 512 or len(den) > 512:
        raise polynomial.OracleLimitError("oracle rational-input digit budget exceeded")
    if (
        re.fullmatch(r"0|-?[1-9][0-9]*", num) is None
        or re.fullmatch(r"[1-9][0-9]*", den) is None
    ):
        raise ValueError("noncanonical rational integer")
    result = Fraction(int(num), int(den))
    if encode(result) != value:
        raise ValueError("rational must be reduced with positive denominator")
    return result


def _keys(value: Any, expected: set[str]) -> None:
    if not isinstance(value, dict) or set(value) != expected:
        raise ValueError("unexpected or missing schema fields")


def _table(inputs: dict[str, Any]) -> tuple[int, int, tuple[int, int]]:
    n1, n0 = inputs["n1"], inputs["n0"]
    if any(type(n) is not int or not 1 <= n <= 12 for n in (n1, n0)):
        raise polynomial.OracleLimitError(
            "packet replay supports positive groups through 12 only"
        )
    observed = inputs["observed"]
    if not isinstance(observed, list) or len(observed) != 2:
        raise ValueError("observed must contain two success counts")
    point = (observed[0], observed[1])
    oracle._point(n1, n0, point)
    return n1, n0, point


def _level(value: Any) -> Fraction:
    if isinstance(value, dict) and value.get("kind") == "public_alpha":
        _keys(value, {"kind", "hex"})
        if not isinstance(value["hex"], str):
            raise ValueError("public alpha must be a hexadecimal float string")
        alpha = float.fromhex(value["hex"])
        if not 1e-12 < alpha < 1 - 1e-12 or alpha.hex() != value["hex"]:
            raise ValueError("invalid public alpha encoding")
        numerator, denominator = alpha.as_integer_ratio()
        return Fraction(numerator, 2 * denominator)
    _keys(value, {"kind", "value"})
    if value["kind"] != "exact_side_level":
        raise ValueError("unknown level kind")
    result = rational(value["value"])
    if not 0 <= result <= 1:
        raise ValueError("side level must lie in [0,1]")
    return result


def _certificate(
    coefficients: Any, left: Fraction = Fraction(0), right: Fraction = Fraction(1)
) -> dict[str, Any]:
    result = asdict(polynomial.root_certificate(coefficients, left, right))
    for key in ("original", "squarefree", "interior_polynomial", "endpoint_values"):
        result[key] = tuple(Fraction(*pair) for pair in result[key])
    result["chain"] = tuple(
        tuple(Fraction(*pair) for pair in row) for row in result["chain"]
    )
    result["interval"] = (left, right)
    result["root_count_semantics"] = (
        "distinct_interior_roots_endpoints_owned_separately"
    )
    result["schema_version"] = "exactcis.unconditional.oracle_root_certificate.v1"
    result["procedure_version"] = PROCEDURE_VERSION
    return result


def derive(inputs: dict[str, Any]) -> dict[str, Any]:
    """Reconstruct every scientific output from primitive exact inputs."""
    if not isinstance(inputs, dict):
        raise ValueError("primitive inputs must be an object")
    kind = inputs.get("kind")
    common = {"kind", "n1", "n0", "observed"}
    if kind == "ordering_event":
        _keys(inputs, common | {"candidate", "direction", "isolator"})
    elif kind in ("fixed_null", "structural"):
        _keys(
            inputs,
            common
            | {"effect", "level"}
            | ({"direction"} if kind == "fixed_null" else set()),
        )
    else:
        raise ValueError("unknown primitive kind")
    n1, n0, observed = _table(inputs)
    table = (observed[0], n1 - observed[0], observed[1], n0 - observed[1])
    if kind == "ordering_event":
        candidate = inputs["candidate"]
        if not isinstance(candidate, list) or len(candidate) != 2:
            raise ValueError("candidate must contain two success counts")
        candidate = tuple(candidate)
        if not isinstance(inputs["isolator"], list) or len(inputs["isolator"]) != 2:
            raise ValueError("isolator requires two rational endpoints")
        left, right = map(rational, inputs["isolator"])
        if not 0 < left < right:
            raise ValueError("ordering-event isolator must be finite and positive")
        direction = inputs["direction"]
        comparison = oracle.comparison_polynomial(
            n1, n0, observed, candidate, direction
        )
        certificate = _certificate(comparison, left, right)
        if certificate["interior_roots"] != 1 or any(certificate["endpoint_roots"]):
            raise ValueError(
                "ordering-event bracket must isolate exactly one interior root"
            )
        masks = tuple(
            oracle.rejection_mask(n1, n0, observed, effect, direction)
            for effect in (left, right)
        )
        return {
            "table": table,
            "comparison_power_coefficients": comparison,
            "root_certificate": certificate,
            "bracket_endpoint_masks": masks,
            "candidate_endpoint_membership": tuple(candidate in mask for mask in masks),
            "candidate_at_event": "included_by_exact_equality",
            "full_event_point_mask": "not_computed",
        }
    level = _level(inputs["level"])
    effect = inputs["effect"]
    if kind == "structural":
        _keys(effect, {"kind", "s"})
        if effect["kind"] not in ("zero", "infinity"):
            raise ValueError("structural effect requires an endpoint tag")
        expected_s = Fraction(int(effect["kind"] == "infinity"))
        if rational(effect["s"]) != expected_s:
            raise ValueError("structural compact-coordinate mismatch")
        pair = oracle.structural_pair(n1, n0, observed, effect["kind"])
        return {
            "table": table,
            "alpha_side": level,
            "directional_pair": pair,
            "accepted": all(p >= level for p in pair),
        }
    _keys(effect, {"kind", "beta", "s"})
    if effect["kind"] != "finite":
        raise ValueError("fixed null requires a finite effect")
    psi = rational(effect["beta"])
    if psi <= 0 or rational(effect["s"]) != psi / (1 + psi):
        raise ValueError("finite effect/compact-coordinate mismatch")
    direction = inputs["direction"]
    mask = oracle.rejection_mask(n1, n0, observed, psi, direction)
    controls_a, controls_b = oracle.bernstein_coefficients(n1, n0, mask, psi)
    threshold = oracle.threshold_coefficients(n1, n0, mask, psi, level)
    numerator = oracle.threshold_coefficients(n1, n0, mask, psi, Fraction(0))
    full_numerator = oracle.threshold_coefficients(
        n1, n0, oracle.sample_space(n1, n0), psi, Fraction(0)
    )
    stationary = polynomial.add(
        polynomial.multiply(polynomial.derivative(numerator), full_numerator),
        tuple(
            -x
            for x in polynomial.multiply(
                numerator, polynomial.derivative(full_numerator)
            )
        ),
    )
    zero_threshold = all(x == 0 for x in threshold)
    zero_stationary = all(x == 0 for x in stationary)
    cutoffs = oracle.cutoff_vector(n1, n0, observed, psi, direction)
    if oracle.expand_cutoffs(n1, n0, cutoffs, direction) != mask:
        raise ArithmeticError("cutoff reconstruction disagrees with generic mask")
    return {
        "table": table,
        "alpha_side": level,
        "mask": mask,
        "mask_sha256": digest("exactcis.oracle.mask.v1", mask),
        "cutoffs": cutoffs,
        "cutoff_convention": (
            "greater_suffix_min_or_hi_plus_one;less_prefix_max_or_lo_minus_one"
        ),
        "coefficient_basis": "power_ascending_and_bernstein_common_degree",
        "common_degree": n1 + n0,
        "numerator_bernstein": controls_a,
        "denominator_bernstein": controls_b,
        "threshold_power": threshold,
        "threshold_root_certificate": None
        if zero_threshold
        else _certificate(threshold),
        "zero_threshold": zero_threshold,
        "accepted": polynomial.threshold_decision(threshold),
        "stationary_power": stationary,
        "stationary_root_certificate": None
        if zero_stationary
        else _certificate(stationary),
        "stationary_identically_zero": zero_stationary,
    }


def make_record(fixture_id: str, inputs: dict[str, Any]) -> dict[str, Any]:
    inputs = encode(inputs)
    derived = encode(derive(inputs))
    return {
        "schema_version": RECORD_VERSION,
        "procedure_version": PROCEDURE_VERSION,
        "fixture_id": fixture_id,
        "orientation": ORIENTATION,
        "claim_ceiling": CLAIM_CEILING,
        "seed": None,
        "inputs": inputs,
        "primitive_sha256": digest("exactcis.oracle.inputs.v1", inputs),
        "derived": derived,
        "output_sha256": digest("exactcis.oracle.output.v1", derived),
    }


def source_hashes(root: Path = ROOT) -> dict[str, str]:
    return {
        path: hashlib.sha256((root / path).read_bytes()).hexdigest()
        for path in SOURCE_PATHS
    }


def verify_record(record: dict[str, Any]) -> None:
    _keys(
        record,
        {
            "schema_version",
            "procedure_version",
            "fixture_id",
            "orientation",
            "claim_ceiling",
            "seed",
            "inputs",
            "primitive_sha256",
            "derived",
            "output_sha256",
        },
    )
    if (
        record["schema_version"] != RECORD_VERSION
        or record["procedure_version"] != PROCEDURE_VERSION
    ):
        raise ValueError("unknown record/procedure version")
    if (
        record["orientation"] != ORIENTATION
        or record["claim_ceiling"] != CLAIM_CEILING
        or record["seed"] is not None
    ):
        raise ValueError("record identity or claim ceiling mismatch")
    if (
        not isinstance(record["fixture_id"], str)
        or re.fullmatch(r"[a-z0-9_]+", record["fixture_id"]) is None
    ):
        raise ValueError("invalid fixture identity")
    if record["primitive_sha256"] != digest(
        "exactcis.oracle.inputs.v1", record["inputs"]
    ):
        raise ValueError("primitive-input hash mismatch")
    if record["output_sha256"] != digest(
        "exactcis.oracle.output.v1", record["derived"]
    ):
        raise ValueError("derived-output hash mismatch")
    if canonical_bytes(derive(record["inputs"])) != canonical_bytes(record["derived"]):
        raise ValueError("scientific replay mismatch")


def _load_canonical(data: bytes) -> Any:
    if len(data) > 4_000_000:
        raise polynomial.OracleLimitError("oracle packet byte budget exceeded")
    value = json.loads(data)
    if canonical_bytes(value) != data:
        raise ValueError("noncanonical JSON bytes")
    return value


def verify_packet(
    data: bytes, manifest_data: bytes, root: Path = ROOT
) -> dict[str, Any]:
    packet, manifest = _load_canonical(data), _load_canonical(manifest_data)
    _keys(manifest, {"schema_version", "packet_sha256", "fixture_ids"})
    if manifest["schema_version"] != "exactcis.unconditional.oracle_manifest.v1":
        raise ValueError("unknown manifest version")
    if manifest["packet_sha256"] != digest("exactcis.oracle.packet.v1", packet):
        raise ValueError("canonical packet hash mismatch")
    _keys(
        packet,
        {
            "schema_version",
            "procedure_version",
            "scope",
            "sources",
            "specification_sha256",
            "generator_sha256",
            "records",
        },
    )
    if (
        packet["schema_version"] != SCHEMA_VERSION
        or packet["procedure_version"] != PROCEDURE_VERSION
    ):
        raise ValueError("unknown packet/procedure version")
    if packet["scope"] != "U1_fixed_rational_null_and_ordering_bracket_diagnostics":
        raise ValueError("unknown packet scope")
    if packet["sources"] != source_hashes(root):
        raise ValueError("oracle source hash mismatch")
    if (
        packet["specification_sha256"]
        != hashlib.sha256((root / SPEC_PATH).read_bytes()).hexdigest()
    ):
        raise ValueError("specification source hash mismatch")
    generator = root / GENERATOR_PATH
    if (
        not isinstance(packet["generator_sha256"], str)
        or re.fullmatch(r"[0-9a-f]{64}", packet["generator_sha256"]) is None
    ):
        raise ValueError("invalid generator source hash")
    if (
        generator.exists()
        and packet["generator_sha256"]
        != hashlib.sha256(generator.read_bytes()).hexdigest()
    ):
        raise ValueError("generator source hash mismatch")
    records = packet["records"]
    if not isinstance(records, list) or not 1 <= len(records) <= 256:
        raise ValueError("invalid fixture count")
    if any(
        not isinstance(record, dict) or not isinstance(record.get("fixture_id"), str)
        for record in records
    ):
        raise ValueError("malformed fixture record")
    ids = [record["fixture_id"] for record in records]
    if ids != sorted(set(ids)) or ids != manifest["fixture_ids"]:
        raise ValueError("fixture identity/order mismatch")
    for record in records:
        verify_record(record)
    return {
        "records_replayed": len(records),
        "generator_source_checked": generator.exists(),
        "claim_ceiling": CLAIM_CEILING,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, default=FIXTURE_DIRECTORY)
    args = parser.parse_args()
    result = verify_packet(
        (args.directory / PACKET_NAME).read_bytes(),
        (args.directory / MANIFEST_NAME).read_bytes(),
    )
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
