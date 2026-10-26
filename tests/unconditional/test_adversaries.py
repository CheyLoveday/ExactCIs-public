"""Frozen actual Boschloo anchors and explicitly generic certificate attacks."""

import hashlib
import json
import math
from pathlib import Path

import pytest

from exactcis import UnsupportedMethodError

from ._production_protocol import boschloo_hull
from ._replay import canonical_bytes, digest

DIRECTORY = Path(__file__).parents[1] / "references/unconditional"


def test_adversarial_bank_binds_historical_records_and_exact_sources():
    raw = (DIRECTORY / "adversarial_manifest_v1.json").read_bytes()
    manifest = json.loads(raw)
    assert canonical_bytes(manifest) == raw
    assert manifest["schema_version"] == "exactcis.boschloo_adversarial_manifest.v1"
    packet = json.loads((DIRECTORY / "boschloo_fixed_null_v1.json").read_bytes())
    anchors = {row["fixture_id"]: row["output_sha256"] for row in packet["records"]}
    assert manifest["fixed_null_anchors"] == anchors
    assert len(anchors) == 21
    root = Path(__file__).parents[2]
    assert manifest["sources"] == {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in manifest["sources"]
    }
    payload = {
        key: value for key, value in manifest.items() if key != "manifest_sha256"
    }
    assert manifest["manifest_sha256"] == digest(
        "exactcis.adversarial_manifest.v1", payload
    )
    assert {row["repair_owner"] for row in manifest["strict_failures"]} == {
        "U3-B4/U4A-3"
    }
    assert all(
        row["current_failure_class"] == "UnsupportedMethodError"
        for row in manifest["strict_failures"]
    )


def test_fresh_adversarial_bank_generation_is_byte_identical():
    root = Path(__file__).parents[2]
    generator = root / "tools/unconditional_oracle/generate_adversaries.py"
    if not generator.is_file():
        return
    from tools.unconditional_oracle.generate_adversaries import manifest

    packet = manifest()
    assert (
        packet["generator_sha256"] == hashlib.sha256(generator.read_bytes()).hexdigest()
    )
    assert (
        canonical_bytes(packet)
        == (DIRECTORY / "adversarial_manifest_v1.json").read_bytes()
    )


@pytest.mark.xfail(
    raises=UnsupportedMethodError,
    strict=True,
    reason=(
        "one_trial_inclusive_lower; U3-B4/U4A-3; method=boschloo absent; "
        "expected inclusive lower endpoint 1"
    ),
)
def test_production_one_trial_inclusive_lower():
    result = boschloo_hull((1, 0, 0, 1), 0.5)
    # Exact side level 1/4: t^2/(1+t)^2 >= 1/4 iff psi=t^2 >= 1.
    assert 0 < result.lower <= 1 <= result.upper
    assert math.isinf(result.upper)


@pytest.mark.xfail(
    raises=UnsupportedMethodError,
    strict=True,
    reason=(
        "one_trial_inclusive_upper; U3-B4/U4A-3; method=boschloo absent; "
        "expected inclusive upper endpoint 1"
    ),
)
def test_production_one_trial_inclusive_upper():
    result = boschloo_hull((0, 1, 1, 0), 0.5)
    assert result.lower == 0
    assert result.lower <= 1 <= result.upper < math.inf


def test_boschloo_does_not_leak_into_risk_ratio_registry():
    from exactcis import Design, Estimand
    from exactcis.estimands import methods_for

    assert all(
        method != "boschloo"
        for method in methods_for(Design.COHORT_BINOMIAL, Estimand.RR)
    )
