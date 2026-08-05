"""Narrow tests for reviewed high-entropy provenance exceptions."""

from __future__ import annotations

from tools.check_history_secrets import (
    TIMING_EVIDENCE_WHEEL_SHA256,
    _allowed_reference_revision,
)


def test_timing_evidence_wheel_checksum_allowlist_is_exact() -> None:
    path = "tools/timing_evidence.json"
    known = f'  "wheel_sha256": "{TIMING_EVIDENCE_WHEEL_SHA256}",'
    unknown = f'  "wheel_sha256": "{"0" * 64}",'

    assert _allowed_reference_revision(path, known)
    assert not _allowed_reference_revision(path, unknown)
