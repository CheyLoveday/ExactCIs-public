"""Unit tests for the public-release provenance contract."""

from __future__ import annotations

import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

ROOT = Path(__file__).parents[1]

if not (ROOT / "tools").is_dir():
    pytest.skip("tools/ not shipped in the public sdist", allow_module_level=True)

from tools import check_version_consistency as version_gate  # noqa: E402


def _cff(
    version: str,
    commit: str | None,
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
        "license: MIT",
    ]
    if commit is not None:
        lines.insert(4, f'commit: "{commit}"')
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


def test_model_b_passes_with_a_tag_resolved_to_a_commit(
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
            None,
            date_released="2026-08-06",
            repository_code="https://github.com/CheyLoveday/ExactCIs-public",
        ),
        "1.1.1",
        is_unreleased=False,
        release_tag="v1.1.1",
        tag_commit=tag_commit,
    )

    assert errors == []


def test_model_b_rejects_a_citation_commit_for_a_published_release() -> None:
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

    assert any("commit must be absent" in error for error in errors)


def test_model_b_requires_a_release_tag_to_resolve_to_one_commit() -> None:
    errors = version_gate.citation_cff_errors(
        _cff(
            "1.1.1",
            None,
            date_released="2026-08-06",
            repository_code=version_gate.PUBLIC_REPOSITORY,
        ),
        "1.1.1",
        is_unreleased=False,
        release_tag="v1.1.1",
        tag_commit="not-a-commit",
    )

    assert "release tag did not resolve to one 40-character commit" in errors


def test_model_b_requires_a_release_date_for_a_published_version() -> None:
    errors = version_gate.citation_cff_errors(
        _cff(
            "1.1.1",
            None,
            repository_code="https://github.com/CheyLoveday/ExactCIs-public",
        ),
        "1.1.1",
        is_unreleased=False,
        release_tag="v1.1.1",
        tag_commit="a" * 40,
    )

    assert "CITATION.cff date-released is required for published Model B" in errors


def test_model_b_requires_a_repository_code_for_a_published_version() -> None:
    errors = version_gate.citation_cff_errors(
        _cff("1.1.1", None, date_released="2026-08-06"),
        "1.1.1",
        is_unreleased=False,
        release_tag=None,
        tag_commit=None,
    )

    assert "CITATION.cff repository-code is required for published Model B" in errors


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


def _write_published_model_b_tree(root: Path) -> None:
    about = root / "src" / "exactcis" / "__about__.py"
    about.parent.mkdir(parents=True)
    about.write_text('__version__ = "1.1.1"\n', encoding="utf-8")
    (root / "pyproject.toml").write_text(
        """[project]
dynamic = ["version"]

[tool.hatch.version]
path = "src/exactcis/__about__.py"
""",
        encoding="utf-8",
    )
    (root / "CHANGELOG.md").write_text(
        """# Changelog

## [Unreleased]

## [1.1.1] - 2026-08-06

Release `exactcis==1.1.1` with tag `v1.1.1`.
""",
        encoding="utf-8",
    )
    (root / "CITATION.cff").write_text(
        _cff(
            "1.1.1",
            None,
            date_released="2026-08-06",
            repository_code=version_gate.PUBLIC_REPOSITORY,
        ),
        encoding="utf-8",
    )
    (root / "CITATION.txt").write_text(
        """ExactCIs
Version: 1.1.1
Public repository: https://github.com/CheyLoveday/ExactCIs-public
Public tag: v1.1.1
PyPI: exactcis==1.1.1

Cite the exact version and tag above. No DOI has been assigned.
""",
        encoding="utf-8",
    )
    workflow = root / ".github" / "workflows" / "release.yml"
    workflow.parent.mkdir(parents=True)
    workflow.write_text(
        """on:
  workflow_dispatch:
    inputs:
      candidate_tag:
        default: v1.1.1
release-v1.1.1-through-testpypi
""",
        encoding="utf-8",
    )


def test_published_model_b_passes_the_full_local_gate_without_a_tag(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _write_published_model_b_tree(tmp_path)
    monkeypatch.setattr(version_gate, "ROOT", tmp_path)
    monkeypatch.setattr(version_gate, "ABOUT", tmp_path / "src/exactcis/__about__.py")
    monkeypatch.setitem(sys.modules, "exactcis", SimpleNamespace(__version__="1.1.1"))

    assert version_gate.check() == []


def test_published_model_b_citation_text_requires_release_provenance() -> None:
    citation = """ExactCIs
Version: 1.1.1
Public repository: https://github.com/CheyLoveday/ExactCIs-public
Public tag: v1.1.1
PyPI: exactcis==1.1.1
"""

    assert (
        version_gate.citation_text_errors(
            citation,
            "1.1.1",
            is_unreleased=False,
            cff_commit=None,
        )
        == []
    )
    errors = version_gate.citation_text_errors(
        citation + f"Public repository revision: {'a' * 40}\n",
        "1.1.1",
        is_unreleased=False,
        cff_commit=None,
    )
    assert "CITATION.txt published Model B must not name a revision SHA" in errors
    errors = version_gate.citation_text_errors(
        citation.replace(f"Public repository: {version_gate.PUBLIC_REPOSITORY}\n", ""),
        "1.1.1",
        is_unreleased=False,
        cff_commit=None,
    )
    assert any("Public repository" in error for error in errors)


def test_release_workflow_records_the_tag_revision_with_checksums() -> None:
    workflow = (
        Path(__file__).parents[1] / ".github" / "workflows" / "release.yml"
    ).read_text(encoding="utf-8")

    assert 'git rev-list -n 1 "$CANDIDATE_TAG"' in workflow
    assert "Release revision: %s" in workflow
    assert "cat release-bundle/SHA256SUMS" in workflow
