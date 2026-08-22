"""Regression tests for the public-prose hygiene vocabulary boundary."""

from __future__ import annotations

from pathlib import Path

import pytest

ROOT = Path(__file__).parents[1]

if not (ROOT / "tools").is_dir():
    pytest.skip("tools/ not shipped in the public sdist", allow_module_level=True)

from tools import check_repository_hygiene as hygiene


def test_public_formalisation_vocabulary_is_not_private() -> None:
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
    assert hygiene.PRIVATE_DOC_TERM.search(private_term) is not None
