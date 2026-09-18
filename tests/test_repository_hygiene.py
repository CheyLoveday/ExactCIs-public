"""Regression tests for the public-prose hygiene vocabulary boundary."""

from __future__ import annotations

from pathlib import Path

import pytest

ROOT = Path(__file__).parents[1]

if (ROOT / "tools").is_dir():
    from tools import check_repository_hygiene as hygiene  # noqa: E402
else:
    # The public sdist intentionally excludes repository-only hygiene tooling.
    # Keep collection compatible with its fixed release-gate skip contract;
    # source-tree runs exercise the checker below.
    hygiene = None


def test_public_formalisation_vocabulary_is_not_private() -> None:
    if hygiene is None:
        return
    assert hygiene.PRIVATE_DOC_TERM.search("Lean theorem correspondence") is None


@pytest.mark.parametrize(
    "private_term",
    (
        "PS4",
        "Paper M",
        "JSS",
        "ClinVar",
        "VEP",
        "CARF",
        "ERDOS",
        "hotstart",
        "manuscript",
    ),
)
def test_actual_private_or_manuscript_terms_remain_blocked(
    private_term: str,
) -> None:
    if hygiene is None:
        return
    assert hygiene.PRIVATE_DOC_TERM.search(private_term) is not None
