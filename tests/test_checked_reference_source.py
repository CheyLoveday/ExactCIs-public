"""Source custody and package separation for the optional checked reference."""

from __future__ import annotations

import hashlib
import json
import shutil
import sys
from fractions import Fraction
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
pytestmark = pytest.mark.skipif(
    not (ROOT / "formal").is_dir(), reason="repository-only checked reference"
)
if (ROOT / "tools").is_dir():
    from tools import check_boschloo_reference as gate
    from tools import check_distribution_contents as distribution
    from tools import check_public_tree as tree
if (ROOT / "formal").is_dir():
    sys.path.insert(0, str(ROOT / "formal/tools"))
    import boschloo


@pytest.fixture
def checkout(tmp_path: Path) -> Path:
    shutil.copytree(
        ROOT / "formal",
        tmp_path / "formal",
        ignore=shutil.ignore_patterns(".lake", "__pycache__"),
    )
    return tmp_path


def manifest(root: Path) -> dict:
    return json.loads((root / "formal" / gate.MANIFEST).read_bytes())


def save(root: Path, data: dict) -> None:
    (root / "formal" / gate.MANIFEST).write_text(
        json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n"
    )


def change(root: Path, relative: str, value: str) -> None:
    path = root / "formal" / relative
    path.write_text(value)
    data = manifest(root)
    raw = path.read_bytes()
    data["files"][relative] = {
        "bytes": len(raw),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }
    save(root, data)


def test_exact_focused_slice() -> None:
    assert gate.check(ROOT) == []
    assert "formal" in distribution.DENIED_PARTS
    assert "formal" in tree.ALLOWED_TOP_LEVEL
    assert ".lake" in tree.DENIED_PARTS


def test_retained_native_example_custody_and_exact_endpoint_conversion() -> None:
    """Custody/protocol replay only; this test does not execute the Lean checker."""
    directory = ROOT / "tests/references/checked_boschloo_v1"
    receipt = json.loads((directory / "replay.json").read_bytes())
    for name in ("input", "payload"):
        assert hashlib.sha256(
            (directory / f"{name}.json").read_bytes()
        ).hexdigest() == (receipt[f"{name}_sha256"].replace("-", ""))
    assert hashlib.sha256(
        (ROOT / "formal" / gate.MANIFEST).read_bytes()
    ).hexdigest() == (receipt["source_manifest_sha256"].replace("-", ""))
    payload = json.loads((directory / "payload.json").read_bytes())
    _, result = boschloo._reply(
        json.dumps(receipt["checker_reply"]).encode(),
        0,
        tuple(int(n) for n in receipt["prior_counters"]),
        payload["terminal"],
    )
    assert result is not None
    assert result.kind == "HULL"
    assert result.lower == Fraction(39, 473)
    assert result.upper is None
    assert result.as_dict() == receipt["checked_result"]


@pytest.mark.parametrize(
    ("path", "allowed"),
    [
        ("README.md", True),
        ("tools/boschloo_check", True),
        ("tools/lean/boschloo_check.lean", True),
        ("tools/boschloo.py", True),
        ("ExactCIs/Unconditional/MeteredGlobalChecker.lean", True),
        ("CarfSpine/Basic.lean", True),
        ("", False),
        ("/outside.lean", False),
        ("../outside.lean", False),
        ("tools/unreviewed.py", False),
        ("ExactCIs/Unconditional/ProducerBuilder.lean", False),
        ("ExactCIs/.hidden/X.lean", False),
        ("other/X.lean", False),
        ("contracts.json", False),
    ],
)
def test_path_boundary(path: str, allowed: bool) -> None:
    assert gate.path_allowed(path) is allowed


def test_comments_and_strings_do_not_invent_imports() -> None:
    text = """/- import Bad /- nested -/ -/
-- import AlsoBad
def message := "escaped \\\" sorry import Hidden"
public import ExactCIs.A Mathlib.B -- tail
import CarfSpine.C
"""
    assert gate.lean_imports(text) == ["ExactCIs.A", "Mathlib.B", "CarfSpine.C"]
    assert gate.lean_code("-- no final newline") == ""
    with pytest.raises(ValueError, match="unterminated"):
        gate.lean_code("/- unfinished")


@pytest.mark.parametrize(
    "field", ["schema", "entry_module", "verification_scope", "generator"]
)
def test_manifest_cannot_promote_scope(checkout: Path, field: str) -> None:
    data = manifest(checkout)
    data[field] = "unreviewed"
    save(checkout, data)
    assert gate.check(checkout)


def test_noncanonical_manifest_and_source_tamper(checkout: Path) -> None:
    path = checkout / "formal" / gate.MANIFEST
    path.write_bytes(path.read_bytes() + b" ")
    assert "noncanonical or unsupported reference manifest" in gate.check(checkout)
    path.write_bytes(path.read_bytes()[:-1])
    source = checkout / "formal/tools/boschloo.py"
    source.write_bytes(source.read_bytes() + b"\n")
    assert any("source bytes differ" in error for error in gate.check(checkout))


def test_inventory_and_forbidden_source(checkout: Path) -> None:
    source = checkout / "formal/unreviewed.txt"
    source.write_text("unreviewed")
    assert "reference source inventory differs" in gate.check(checkout)
    change(checkout, "unreviewed.txt", "unreviewed")
    assert any("outside reference" in error for error in gate.check(checkout))


def test_missing_source_is_not_accepted(checkout: Path) -> None:
    (checkout / "formal/tools/boschloo_check").unlink()
    assert any("missing or linked" in error for error in gate.check(checkout))


def test_source_symlink_is_not_accepted(checkout: Path, tmp_path: Path) -> None:
    path = checkout / "formal/tools/boschloo_check"
    value = path.read_bytes()
    path.unlink()
    outside = tmp_path / "outside"
    outside.write_bytes(value)
    try:
        path.symlink_to(outside)
    except OSError:
        pytest.skip("symbolic-link privilege unavailable")
    assert any("missing or linked" in error for error in gate.check(checkout))


@pytest.mark.parametrize(
    ("relative", "value", "message"),
    [
        ("lean-toolchain", "leanprover/lean4:v4.35.0\n", "Lean 4.33"),
        ("global-checker-v1.schema.json", "{}\n", "frozen dependency/schema"),
        (
            "lakefile.toml",
            'defaultTargets=["Other"]\n[[lean_lib]]\nname="Other"\n',
            "Lake targets",
        ),
    ],
)
def test_pins_and_build_boundary(
    checkout: Path, relative: str, value: str, message: str
) -> None:
    change(checkout, relative, value)
    assert any(message in error for error in gate.check(checkout))


@pytest.mark.parametrize(
    ("addition", "message"),
    [
        ("\naxiom unreviewed : True\n", "placeholder/axiom"),
        ("\nimport Unreviewed.Library\n", "unreviewed external"),
        ("\nimport ExactCIs.Missing\n", "unselected checker import"),
    ],
)
def test_import_and_proof_boundary(checkout: Path, addition: str, message: str) -> None:
    relative = gate.ENTRY.replace(".", "/") + ".lean"
    path = checkout / "formal" / relative
    change(checkout, relative, path.read_text() + addition)
    assert any(message in error for error in gate.check(checkout))


def test_manifest_selection_and_runtime_import_boundary(checkout: Path) -> None:
    data = manifest(checkout)
    data["lean_modules"].pop()
    data["python_modules"].pop()
    save(checkout, data)
    errors = gate.check(checkout)
    assert "checker module selection differs" in errors
    assert "reference Python module selection differs" in errors
    path = checkout / "formal/tools/boschloo.py"
    change(checkout, "tools/boschloo.py", path.read_text() + "\nimport numpy\n")
    assert any("Python dependency" in error for error in gate.check(checkout))


def test_guard_cli_reports_custody_ceiling(monkeypatch, capsys) -> None:
    monkeypatch.setattr(gate, "check", lambda root: [])
    assert gate.main() == 0
    assert "assurance INCOMPLETE" in capsys.readouterr().out
    monkeypatch.setattr(gate, "check", lambda root: ["changed source"])
    assert gate.main() == 1
    assert "ERROR: changed source" in capsys.readouterr().out
