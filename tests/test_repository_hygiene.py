"""Regression tests for the public-prose hygiene vocabulary boundary."""

from __future__ import annotations

import pytest

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
