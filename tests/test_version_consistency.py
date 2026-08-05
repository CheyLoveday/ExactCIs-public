"""Unit tests for the public-release provenance contract."""

from __future__ import annotations

import pytest

from tools import check_version_consistency as version_gate


def _cff(
    version: str,
    commit: str,
    *,
    date_released: str | None = None,
    repository_code: str | None = None,
    doi: str | None = None,
) -> str:
    lines = [
        "cff-version: 1.2.0",
        "title: ExactCIs",
        "type: software",
        f'version: "{version}"',
        f'commit: "{commit}"',
        "license: MIT",
    ]
    if date_released is not None:
        lines.append(f"date-released: {date_released}")
    if repository_code is not None:
        lines.append(f"repository-code: {repository_code}")
    if doi is not None:
        lines.append(f"doi: {doi}")
    return "\n".join(lines) + "\n"


def test_grandfathered_release_and_rc_keep_the_historical_source_sha() -> None:
    for version in ("1.0.0", "1.0.0rc2", "1.1.0", "1.1.0rc1"):
        errors = version_gate.citation_cff_errors(
            _cff(version, version_gate.HISTORICAL_SCIENTIFIC_SOURCE_SHA),
            version,
            is_unreleased=False,
            release_tag=None,
            tag_commit=None,
        )
        assert errors == []


def test_model_b_passes_with_the_commit_resolved_from_the_release_tag(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    release_commit = "a" * 40

    def resolved(*arguments: str) -> str:
        assert arguments == ("rev-list", "-n", "1", "v1.1.1")
        return release_commit

    monkeypatch.setattr(version_gate, "_git_output", resolved)
    tag_commit = version_gate.release_tag_commit("v1.1.1")
    errors = version_gate.citation_cff_errors(
        _cff(
            "1.1.1",
            tag_commit,
            date_released="2026-08-06",
            repository_code="https://github.com/CheyLoveday/ExactCIs-public",
        ),
        "1.1.1",
        is_unreleased=False,
        release_tag="v1.1.1",
        tag_commit=tag_commit,
    )

    assert errors == []


def test_model_b_rejects_a_citation_commit_that_differs_from_its_tag() -> None:
    errors = version_gate.citation_cff_errors(
        _cff(
            "1.1.1",
            "b" * 40,
            date_released="2026-08-06",
            repository_code="https://github.com/CheyLoveday/ExactCIs-public",
        ),
        "1.1.1",
        is_unreleased=False,
        release_tag="v1.1.1",
        tag_commit="a" * 40,
    )

    assert any("does not equal the commit resolved" in error for error in errors)


def test_model_b_requires_a_release_date_for_a_published_version() -> None:
    errors = version_gate.citation_cff_errors(
        _cff(
            "1.1.1",
            "a" * 40,
            repository_code="https://github.com/CheyLoveday/ExactCIs-public",
        ),
        "1.1.1",
        is_unreleased=False,
        release_tag="v1.1.1",
        tag_commit="a" * 40,
    )

    assert "CITATION.cff date-released is required for published Model B" in errors


def test_cff_doi_remains_forbidden_after_release_metadata_is_allowed() -> None:
    errors = version_gate.citation_cff_errors(
        _cff(
            "1.1.0",
            version_gate.HISTORICAL_SCIENTIFIC_SOURCE_SHA,
            date_released="2026-08-05",
            repository_code="https://github.com/CheyLoveday/ExactCIs-public",
            doi="10.9999/not-assigned",
        ),
        "1.1.0",
        is_unreleased=False,
        release_tag=None,
        tag_commit=None,
    )

    assert "CITATION.cff invents a DOI" in errors


def test_unreleased_model_b_requires_the_documented_placeholder() -> None:
    errors = version_gate.citation_cff_errors(
        _cff("1.1.1", "a" * 40),
        "1.1.1",
        is_unreleased=True,
        release_tag=None,
        tag_commit=None,
    )

    assert any("documented unreleased placeholder" in error for error in errors)
