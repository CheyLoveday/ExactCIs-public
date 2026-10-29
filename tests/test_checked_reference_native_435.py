"""Custody/protocol checks for retained actual native Lean 4.35 executions.

These tests do not rerun Lean or turn the finite examples into a general proof.
"""

from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
pytestmark = pytest.mark.skipif(
    not (ROOT / "formal").is_dir(), reason="repository-only checked reference"
)
if (ROOT / "formal").is_dir():
    sys.path.insert(0, str(ROOT / "formal/tools"))
    import boschloo

DIRECTORY = ROOT / "tests/references/checked_boschloo_435_v1"
RECEIPT = json.loads((DIRECTORY / "replay.json").read_bytes())
CASES = {case["name"]: case for case in RECEIPT["cases"]}


def _blob(record: dict) -> bytes:
    data = (DIRECTORY / record["path"]).read_bytes()
    if "mutation" in record:
        # Reconstruct the actually rejected witness without duplicating the
        # unchanged 250 kB historical hull certificate.
        mutation = record["mutation"]
        value = json.loads(data)
        slot = value
        for key in mutation["path"][:-1]:
            slot = slot[key]
        slot[mutation["path"][-1]] = mutation["value"]
        data = json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode(
            "ascii"
        )
    assert len(data) == record["bytes"]
    assert hashlib.sha256(data).hexdigest() == record["sha256"].replace("-", "")
    return data


def test_current_native_435_source_custody() -> None:
    assert RECEIPT["toolchain"] == "leanprover/lean4:v4.35.0"
    assert (ROOT / "formal/lean-toolchain").read_text(encoding="utf-8").strip() == (
        RECEIPT["toolchain"]
    )
    for relative, key in (
        ("formal/checked-reference-manifest.json", "source_manifest_sha256"),
        ("formal/lake-manifest.json", "dependency_lock_sha256"),
        (RECEIPT["frontend_path"], "frontend_sha256"),
    ):
        assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == (
            RECEIPT[key].replace("-", "")
        )
    assert set(CASES) == {"hull", "full", "wrong-witness", "budget-exhausted"}


@pytest.mark.parametrize(
    ("name", "status", "returncode"),
    (
        ("hull", "accepted", 0),
        ("full", "accepted", 0),
        ("wrong-witness", "rejected", 3),
        ("budget-exhausted", "refused", 2),
    ),
)
def test_retained_native_435_case(name: str, status: str, returncode: int) -> None:
    case = CASES[name]
    _blob(case["input"])
    terminal = json.loads(_blob(case["payload"]))["terminal"]
    prior = tuple(map(int, case["prior_counters"]))
    reply, result = boschloo._reply(_blob(case["stdout"]), returncode, prior, terminal)
    assert case["returncode"] == returncode
    assert reply == case["reply"]
    assert reply["status"] == status
    assert len(reply["counters"]) == 15
    assert all(int(after) >= before for after, before in zip(reply["counters"], prior))
    if name == "hull":
        assert result is not None and result.kind == "HULL"
        assert result.lower == Fraction(39, 473)
        assert result.upper is None
    elif name == "full":
        assert result is not None and result.kind == "FULL"
        assert result.lower == Fraction(0)
        assert result.upper is None
    else:
        assert result is None
        assert "result" not in reply
        assert "reason" in reply


@pytest.mark.parametrize("name", CASES)
def test_native_435_status_and_counter_mismatches_refuse(name: str) -> None:
    case = CASES[name]
    stdout = _blob(case["stdout"])
    terminal = json.loads(_blob(case["payload"]))["terminal"]
    prior = tuple(map(int, case["prior_counters"]))
    wrong_code = 1 if case["returncode"] == 0 else 0
    with pytest.raises(ValueError, match="status and exit code disagree"):
        boschloo._reply(stdout, wrong_code, prior, terminal)
    changed = json.loads(stdout)
    changed["counters"][2] = str(prior[2] - 1)
    with pytest.raises(ValueError):
        boschloo._reply(
            json.dumps(changed).encode(), case["returncode"], prior, terminal
        )


def test_native_435_hull_bound_mismatch_refuses() -> None:
    case = CASES["hull"]
    terminal = json.loads(_blob(case["payload"]))["terminal"]
    terminal["outerLower"] = {"numerator": "0", "denominator": "1"}
    with pytest.raises(ValueError, match="endpoints disagree"):
        boschloo._reply(
            _blob(case["stdout"]),
            case["returncode"],
            tuple(map(int, case["prior_counters"])),
            terminal,
        )
