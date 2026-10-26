"""Narrow tests for reviewed high-entropy provenance exceptions."""

from __future__ import annotations

from pathlib import Path

import pytest

ROOT = Path(__file__).parents[1]

if not (ROOT / "tools").is_dir():
    pytest.skip("tools/ not shipped in the public sdist", allow_module_level=True)

from tools import check_history_secrets as history_gate  # noqa: E402


def test_timing_evidence_wheel_checksum_allowlist_is_exact() -> None:
    path = "tools/timing_evidence.json"
    known = f'  "wheel_sha256": "{history_gate.TIMING_EVIDENCE_WHEEL_SHA256}",'
    unknown = f'  "wheel_sha256": "{"0" * 64}",'

    assert history_gate._allowed_reference_revision(path, known)
    assert not history_gate._allowed_reference_revision(path, unknown)


@pytest.mark.parametrize(
    ("path", "line"),
    (
        (
            "replication/jss_package_paper.py",
            f'RELEASE_COMMIT = "{history_gate.PUBLIC_RELEASE_1_1_2_SHA}"',
        ),
        (
            "tests/test_jss_replication.py",
            f'"commit": "{history_gate.PUBLIC_RELEASE_1_1_2_SHA}",',
        ),
    ),
)
def test_jss_release_provenance_allowlist_is_exact(path: str, line: str) -> None:
    unknown = line.replace(history_gate.PUBLIC_RELEASE_1_1_2_SHA, "0" * 40)

    assert history_gate._allowed_reference_revision(path, line)
    assert not history_gate._allowed_reference_revision(path, unknown)
    assert not history_gate._allowed_reference_revision("replication/other.py", line)


def test_shallow_repository_is_rejected_before_scanning(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    def shallow_state(*arguments: str, text: bool = True) -> str:
        assert arguments == ("rev-parse", "--is-shallow-repository")
        assert text
        return "true\n"

    monkeypatch.setattr(history_gate, "_git", shallow_state)
    monkeypatch.setattr(
        history_gate,
        "_current_tree_errors",
        lambda: pytest.fail("secret scan started before the clone premise check"),
    )

    assert history_gate.main() == 1
    output = capsys.readouterr().out
    assert "full Git clone" in output
    assert "fetch-depth: 0" in output


def test_generated_oracle_allowlist_rejects_changed_content_and_paths() -> None:
    for path in history_gate.ORACLE_PACKET_LINE_DIGESTS:
        line = (history_gate.ROOT / path).read_text().rstrip("\n")
        assert history_gate._allowed_reference_revision(path, line)
        assert not history_gate._allowed_reference_revision("other.json", line)
        assert not history_gate._allowed_reference_revision(path, line + "altered")
        data = (history_gate.ROOT / path).read_bytes()
        assert history_gate._reviewed_packet_data(path, data)
        assert not history_gate._reviewed_packet_data("other.json", data)
        assert not history_gate._reviewed_packet_data(path, data + b"\n")
        assert not history_gate._reviewed_packet_data(path, data[:-1] + b" \n")


def test_reviewed_packet_prefilter_scans_changed_bytes_and_unreviewed_paths(
    tmp_path, monkeypatch
):
    import hashlib
    import json
    import subprocess

    pytest.importorskip("detect_secrets")
    # Deliberately synthetic detector input, built at runtime; no credential.
    value = hashlib.sha256(b"public detector control").hexdigest()
    data = (json.dumps({"sample": value}) + "\n").encode()
    reviewed = tmp_path / "reviewed.json"
    ordinary = tmp_path / "ordinary.json"
    reviewed.write_bytes(data)
    ordinary.write_bytes(data)
    subprocess.run(["git", "init", "-q", str(tmp_path)], check=True)
    subprocess.run(
        ["git", "add", "reviewed.json", "ordinary.json"], cwd=tmp_path, check=True
    )
    monkeypatch.setattr(history_gate, "ROOT", tmp_path)
    monkeypatch.setattr(
        history_gate,
        "ORACLE_PACKET_LINE_DIGESTS",
        {"reviewed.json": hashlib.sha256(data[:-1]).hexdigest()},
    )
    errors = history_gate._current_tree_errors()
    assert any("ordinary.json" in error for error in errors)
    assert not any("reviewed.json" in error for error in errors)
    reviewed.write_bytes(data[:-1] + b" \n")
    errors = history_gate._current_tree_errors()
    assert any("reviewed.json" in error for error in errors)
