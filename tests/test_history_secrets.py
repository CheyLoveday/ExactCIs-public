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
